open RTL;;
open Camlcoq;;
open Maps;;
open Kildall;;
open HashedSet;;

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

(* unfinished *)
let dominated_parts (f : coq_function) : PSet.t PTree.t =
  let (headers, dominated) = dominated_parts1 f in
  match dominated with
  | None -> failwith "dominated_parts 1"
  | Some dominated ->
     let singletons =
       PTree.fold (fun before pc flag ->
         if flag
         then PTree.set pc (PSet.add pc PSet.empty) before
         else before) headers PTree.empty in
     PTree.fold (fun before pc ii ->
         match PMap.get pc dominated with
         | Dominator.Dominated x ->
            let px = P.of_int x in
            (match PTree.get px before with
             | None -> failwith "dominated_parts 2"
             | Some old ->
                PTree.set px (PSet.add pc old) before)
         | _ -> before) f.fn_code singletons;;

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

let pp_pset oc s =
  output_string oc "{ ";
  let first = ref true in
  List.iter (fun x ->
      (if !first
       then first := false
       else output_string oc ", ");
      Printf.printf "%d" x)
    (List.sort (fun x y -> y - x) (List.map P.to_int (PSet.elements s)));
  output_string oc " }";;

let print_dominated_parts oc f =
  List.iter (fun (header, nodes) ->
      Printf.fprintf oc "%d : %a\n" (P.to_int header) pp_pset nodes)
    (PTree.elements (dominated_parts f));;

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
  let _ = print_dominated_parts stdout f in
  PTree.empty;;
(*
  let max_reg = P.to_int coq_max_reg in
  PTree.set coq_max_pc [Inject.INJload(AST.Mint32, (Op.Aindexed (Ptrofs.of_int (Z.of_sint 0))), [P.of_int 1], P.of_int (max_reg+1))] PTree.empty;;
 *)
