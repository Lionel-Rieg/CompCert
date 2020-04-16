open RTL;;
open Camlcoq;;
open Maps;;

type reg = P.t;;

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
  let _ = print_loop_headers f in
  PTree.empty;;
(*
  let max_reg = P.to_int coq_max_reg in
  PTree.set coq_max_pc [Inject.INJload(AST.Mint32, (Op.Aindexed (Ptrofs.of_int (Z.of_sint 0))), [P.of_int 1], P.of_int (max_reg+1))] PTree.empty;;
 *)
