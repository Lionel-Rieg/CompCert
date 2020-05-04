(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*                                                             *)
(*  Copyright VERIMAG. All rights reserved.                    *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

open RTL;;
open Camlcoq;;
open Maps;;
open Kildall;;
open HashedSet;;
open Inject;;

type reg = P.t;;

module Dominator =
  struct
    type t = Unreachable | Dominated of int | Multiple
    let bot = Unreachable and top = Multiple
    let beq a b =
      match a, b with
      | Unreachable, Unreachable
      | Multiple, Multiple -> true
      | (Dominated x), (Dominated y) -> x = y
      | _ -> false
    let lub a b =
      match a, b with
      | Multiple, _
      | _, Multiple -> Multiple
      | Unreachable, x
      | x, Unreachable -> x
      | (Dominated x), (Dominated y) when x=y -> a
      | (Dominated _), (Dominated _) -> Multiple

    let pp oc = function
      | Unreachable -> output_string oc "unreachable"
      | Multiple -> output_string oc "multiple"
      | Dominated x -> Printf.fprintf oc "%d" x;;
  end

module Dominator_Solver = Dataflow_Solver(Dominator)(NodeSetForward)

let apply_dominator (is_marked : node -> bool) (pc : node)
      (before : Dominator.t) : Dominator.t =
  match before with
  | Dominator.Unreachable -> before
  | _ ->
     if is_marked pc
     then Dominator.Dominated (P.to_int pc)
     else before;;

let dominated_parts1 (f : coq_function) :
      (bool PTree.t) * (Dominator.t PMap.t option) =
  let headers = Duplicateaux.get_loop_headers f.fn_code f.fn_entrypoint in
  let dominated = Dominator_Solver.fixpoint f.fn_code RTL.successors_instr
    (apply_dominator (fun pc -> match PTree.get pc headers with
                                | Some x -> x
                                | None -> false)) f.fn_entrypoint
    Dominator.top in
  (headers, dominated);;

let dominated_parts (f : coq_function) : Dominator.t PMap.t * PSet.t PTree.t =
  let (headers, dominated) = dominated_parts1 f in
  match dominated with
  | None -> failwith "dominated_parts 1"
  | Some dominated ->
     let singletons =
       PTree.fold (fun before pc flag ->
         if flag
         then PTree.set pc (PSet.add pc PSet.empty) before
         else before) headers PTree.empty in
     (dominated,
     PTree.fold (fun before pc ii ->
         match PMap.get pc dominated with
         | Dominator.Dominated x ->
            let px = P.of_int x in
            (match PTree.get px before with
             | None -> failwith "dominated_parts 2"
             | Some old ->
                PTree.set px (PSet.add pc old) before)
         | _ -> before) f.fn_code singletons);;

let graph_traversal (initial_node : P.t)
  (successor_iterator : P.t -> (P.t -> unit) -> unit) : PSet.t =
  let seen = ref PSet.empty
  and stack = Stack.create () in
  Stack.push initial_node stack;
  while not (Stack.is_empty stack)
  do
    let vertex = Stack.pop stack in
    if not (PSet.contains !seen vertex)
    then
      begin
        seen := PSet.add vertex !seen;
        successor_iterator vertex (fun x -> Stack.push x stack) 
      end
  done;
  !seen;;

let filter_dominated_part (predecessors : P.t list PTree.t)
      (header : P.t) (dominated_part : PSet.t) =
  graph_traversal header
    (fun (vertex : P.t) (f : P.t -> unit) ->
      match PTree.get vertex predecessors with
      | None -> ()
      | Some l ->
         List.iter
           (fun x ->
             if PSet.contains dominated_part x
             then f x) l
    );;

let inner_loops (f : coq_function) =
  let (dominated, parts) = dominated_parts f
  and predecessors = Kildall.make_predecessors f.fn_code RTL.successors_instr in
  (dominated, predecessors, PTree.map (filter_dominated_part predecessors) parts);;

let map_reg mapper r =
  match PTree.get r mapper with
  | None -> r
  | Some x -> x;;

let rewrite_loop_body (last_alloc : reg ref)
      (insns : RTL.code) (header : P.t) (loop_body : PSet.t) =
  let seen = ref PSet.empty
  and stack = Stack.create ()
  and rewritten = ref [] in
  let add_inj ii = rewritten := ii::!rewritten in
  Stack.push (header, PTree.empty) stack;
  while not (Stack.is_empty stack)
  do
    let (pc, mapper) = Stack.pop stack in
    if not (PSet.contains !seen pc)
    then
      begin
        seen := PSet.add pc !seen;
        match PTree.get pc insns with
        | None -> ()
        | Some ii ->
           let mapper' =
             match ii with
             | Iop(op, args, res, pc') when not (Op.is_trapping_op op) ->
                let new_res = P.succ !last_alloc in
                last_alloc := new_res;
                add_inj (INJop(op,
                               (List.map (map_reg mapper) args),
                               new_res));
                PTree.set res new_res mapper
             | Iload(trap, chunk, addr, args, res, pc')
                  when Archi.has_notrap_loads &&
                       !Clflags.option_fnontrap_loads ->
                let new_res = P.succ !last_alloc in
                last_alloc := new_res;
                add_inj (INJload(chunk, addr,
                                 (List.map (map_reg mapper) args),
                                 new_res));
                PTree.set res new_res mapper
             | _ -> mapper in
           List.iter (fun x ->
               if PSet.contains loop_body x
               then Stack.push (x, mapper') stack)
             (successors_instr ii)
      end
  done;
  List.rev !rewritten;;

let pp_inj_instr (oc : out_channel) (ii : inj_instr) =
  match ii with
  | INJnop -> output_string oc "nop"
  | INJop(op, args, res) ->
     Printf.fprintf oc "%a = %a"
       PrintRTL.reg res (PrintOp.print_operation PrintRTL.reg) (op, args)
  | INJload(chunk, addr, args, dst) ->
     Printf.fprintf oc "%a = %s[%a]"
       PrintRTL.reg dst (PrintAST.name_of_chunk chunk)
         (PrintOp.print_addressing PrintRTL.reg) (addr, args);;

let pp_inj_list (oc : out_channel) (l : inj_instr list) =
  List.iter (Printf.fprintf oc "%a; " pp_inj_instr) l;;

let pp_injections (oc : out_channel) (injections : inj_instr list PTree.t) =
  List.iter
    (fun (pc, injl) ->
      Printf.fprintf oc "%d : %a\n" (P.to_int pc) pp_inj_list injl)
    (PTree.elements injections);;

let compute_injections1 (f : coq_function) =
  let (dominated, predecessors, loop_bodies) = inner_loops f
  and last_alloc = ref (max_reg_function f) in
  (dominated, predecessors,
   PTree.map (fun header body ->
    (body, rewrite_loop_body last_alloc f.fn_code header body)) loop_bodies);;

let compute_injections (f : coq_function) : inj_instr list PTree.t =
  let (dominated, predecessors, injections) = compute_injections1 f in
  let output_map = ref PTree.empty in
  List.iter
    (fun (header, (body, inj)) ->
      match PTree.get header predecessors with
      | None -> failwith "compute_injections"
      | Some l ->
         List.iter (fun predecessor ->
             if (PMap.get predecessor dominated)<>Dominator.Unreachable &&
                  not (PSet.contains body predecessor)
             then output_map := PTree.set predecessor inj !output_map) l)
    (PTree.elements injections);
  !output_map;;
  
let pp_list pp_item oc l =
  output_string oc "{ ";
  let first = ref true in
  List.iter (fun x ->
      (if !first
       then first := false
       else output_string oc ", ");
      pp_item oc x) l;
  output_string oc " }";;

let pp_pset oc s =
  pp_list (fun oc -> Printf.fprintf oc "%d") oc
    (List.sort (fun x y -> y - x) (List.map P.to_int (PSet.elements s)));;

let print_dominated_parts oc f =
  List.iter (fun (header, nodes) ->
      Printf.fprintf oc "%d : %a\n" (P.to_int header) pp_pset nodes)
    (PTree.elements (snd (dominated_parts f)));;

let print_inner_loops oc f =
  List.iter (fun (header, nodes) ->
      Printf.fprintf oc "%d : %a\n" (P.to_int header) pp_pset nodes)
    (PTree.elements (let (_,_,l) = (inner_loops f) in l));;

let print_dominated_parts1 oc f =
  match snd (dominated_parts1 f) with
  | None -> output_string oc "error\n"
  | Some parts ->
     List.iter
       (fun (pc, instr) ->
         Printf.fprintf oc "%d : %a\n" (P.to_int pc) Dominator.pp
           (PMap.get pc parts)
       )
       (PTree.elements f.fn_code);;
  
let loop_headers (f : coq_function) : RTL.node list =
  List.map fst (List.filter snd (PTree.elements (Duplicateaux.get_loop_headers f.fn_code f.fn_entrypoint)));;

let print_loop_headers f =
  print_endline "Loop headers";
  List.iter
    (fun i -> Printf.printf "%d " (P.to_int i))
    (loop_headers f);
  print_newline ();;

let gen_injections (f : coq_function) (coq_max_pc : node) (coq_max_reg : reg):
      (Inject.inj_instr list) PTree.t =
  let injections = compute_injections f in
  (* let () = pp_injections stdout injections in *)
  injections;;
