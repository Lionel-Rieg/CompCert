open RTL
open Maps

let duplicate_aux f = (((fn_code f), (fn_entrypoint f)), PTree.empty)
