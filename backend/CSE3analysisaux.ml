open CSE3analysis
open Maps
open HashedSet
open Camlcoq

let flatten_eq eq =
  ((P.to_int eq.eq_lhs), eq.eq_op, List.map P.to_int eq.eq_args);;

let preanalysis (f : RTL.coq_function) =
  let cur_eq_id = ref 0
  and cur_catalog = ref PTree.empty
  and eq_table = Hashtbl.create 100
  and rhs_table = Hashtbl.create 100
  and cur_kill_reg = ref (PMap.init PSet.empty)
  and cur_kill_mem = ref PSet.empty
  and cur_moves = ref (PMap.init PSet.empty) in
  let eq_find_oracle node eq =
    Hashtbl.find_opt eq_table (flatten_eq eq)
  and rhs_find_oracle node sop args =
    match Hashtbl.find_opt rhs_table (sop, List.map P.to_int args) with
    | None -> PSet.empty
    | Some s -> s in
  let mutating_eq_find_oracle node eq =
    incr cur_eq_id; None in (* FIXME *)
  ignore 
    (internal_analysis
      { eq_catalog     = (fun eq_id -> PTree.get eq_id !cur_catalog);
        eq_find_oracle = mutating_eq_find_oracle;
        eq_rhs_oracle  = rhs_find_oracle ;
        eq_kill_reg    = (fun reg -> PMap.get reg !cur_kill_reg);
        eq_kill_mem    = (fun () -> !cur_kill_mem);
        eq_moves       = (fun reg -> PMap.get reg !cur_moves)
      } f);
  { hint_eq_catalog    = !cur_catalog;
    hint_eq_find_oracle= eq_find_oracle;
    hint_eq_rhs_oracle = rhs_find_oracle };;
