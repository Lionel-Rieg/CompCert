open RTL
open Maps

let rec make_identity_ptree_rec = function
| [] -> PTree.empty
| m::lm -> let (n, _) = m in PTree.set n n (make_identity_ptree_rec lm)

let make_identity_ptree f = make_identity_ptree_rec (PTree.elements f.fn_code)

(* For now, identity function *)
let duplicate_aux f =
  let pTreeId = make_identity_ptree f
  in ((f.fn_code, f.fn_entrypoint), pTreeId)
