open RTL
open Maps

(* For now, identity function *)
let duplicate_aux f =
  let pTreeEntry = PTree.set (fn_entrypoint f) (fn_entrypoint f) PTree.empty
  in (((fn_code f), (fn_entrypoint f)), pTreeEntry)
