open RTL;;
open Camlcoq;;
open Maps;;
open Integers;;

type reg = P.t;;

module IntSet = Set.Make(struct type t=int let compare = (-) end);;

let loop_headers (f : coq_function) =
  PTree.fold (fun (already : IntSet.t)
                  (coq_pc : node) (instr : instruction) ->
      let pc = P.to_int coq_pc in
      List.fold_left (fun (already : IntSet.t) (coq_pc' : node) ->
          let pc' = P.to_int coq_pc' in
          if pc' >= pc
          then IntSet.add pc' already
          else already) already (successors_instr instr))
    f.fn_code IntSet.empty;;

let print_loop_headers f =
  print_endline "Loop headers";
  IntSet.iter
    (fun i -> Printf.printf "%d " i)
    (loop_headers f);
  print_newline ();;

let gen_injections (f : coq_function) (coq_max_pc : node) (coq_max_reg : reg):
  (Inject.inj_instr list) PTree.t =
  let max_reg = P.to_int coq_max_reg in
  PTree.set coq_max_pc [Inject.INJload(AST.Mint32, (Op.Aindexed (Ptrofs.of_int (Z.of_sint 0))), [P.of_int 1], P.of_int (max_reg+1))] PTree.empty;;
