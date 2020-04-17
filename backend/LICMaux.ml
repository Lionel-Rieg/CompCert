open RTL;;
open Camlcoq;;
open Maps;;
open Kildall;;

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

let dominated_parts (f : coq_function) : Dominator.t PMap.t option =
  let headers = Duplicateaux.get_loop_headers f.fn_code f.fn_entrypoint in
  Dominator_Solver.fixpoint f.fn_code RTL.successors_instr
    (apply_dominator (fun pc -> match PTree.get pc headers with
                                | Some x -> x
                                | None -> false)) f.fn_entrypoint
    Dominator.top;;

let print_dominated_parts oc f =
  match dominated_parts f with
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
