open RTL
open Maps

let rec make_identity_ptree_rec = function
| [] -> PTree.empty
| m::lm -> let (n, _) = m in PTree.set n n (make_identity_ptree_rec lm)

let make_identity_ptree f = make_identity_ptree_rec (PTree.elements (fn_code f))

(* For now, identity function *)
let duplicate_aux f =
  let pTreeId = make_identity_ptree f
  in (((fn_code f), (fn_entrypoint f)), pTreeId)
