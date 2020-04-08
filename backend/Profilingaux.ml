open Camlcoq
open RTL
   
let function_id (f : coq_function) : Digest.t =
  Digest.string (Marshal.to_string f []);;

let branch_id (f_id : Digest.t) (node : P.t) : Digest.t =
  Digest.string (f_id ^ (Int64.to_string (P.to_int64 node)));;

let pp_id channel (x : Digest.t) =
  for i=0 to 15 do
    Printf.fprintf channel "%02x" (Char.code (String.get x i))
  done

let spp_id () (x : Digest.t) : string =
  let s = ref "" in
  for i=0 to 15 do
    s := Printf.sprintf "%02x%s" (Char.code (String.get x i)) !s
  done;
  !s;;
