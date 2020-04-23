open CSE3analysis
open Maps
open HashedSet
open Camlcoq

let flatten_eq eq =
  ((P.to_int eq.eq_lhs), eq.eq_op, List.map P.to_int eq.eq_args);;

let imp_add_i_j s i j =
  s := PMap.set i (PSet.add j (PMap.get i !s)) !s;;

let string_of_chunk = function
    | AST.Mint8signed -> "int8signed"
    | AST.Mint8unsigned -> "int8unsigned"
    | AST.Mint16signed -> "int16signed"
    | AST.Mint16unsigned -> "int16unsigned"
    | AST.Mint32 -> "int32"
    | AST.Mint64 -> "int64"
    | AST.Mfloat32 -> "float32"
    | AST.Mfloat64 -> "float64"
    | AST.Many32 -> "any32"
    | AST.Many64 -> "any64";;

let print_reg channel i =
  Printf.fprintf channel "r%d" i;;

let print_eq channel (lhs, sop, args) =
  match sop with
  | SOp op ->
     Printf.printf "%a = %a\n" print_reg lhs (PrintOp.print_operation print_reg) (op, args)
  | SLoad(chunk, addr) ->
     Printf.printf "%a = %s @ %a\n" print_reg lhs (string_of_chunk chunk)
       (PrintOp.print_addressing print_reg) (addr, args);;

let print_set s =
  Printf.printf "{ ";
  List.iter (fun i -> Printf.printf "%d; " (P.to_int i)) (PSet.elements s);
  Printf.printf "}\n";;

let pp_rhs oc (sop, args) =
  match sop with
  | SOp op -> PrintOp.print_operation PrintRTL.reg oc (op, args)
  | SLoad(chunk, addr) ->
     Printf.fprintf oc "%s[%a]"
       (PrintAST.name_of_chunk chunk)
         (PrintOp.print_addressing PrintRTL.reg) (addr, args);;

let preanalysis (tenv : typing_env) (f : RTL.coq_function) =
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
    (* Printf.printf "query for %a\n" pp_rhs (sop, args); *)
    match Hashtbl.find_opt rhs_table (sop, List.map P.to_int args) with
    | None -> PSet.empty
    | Some s -> s in
  let mutating_eq_find_oracle node eq : P.t option =
    let (flat_eq_lhs, flat_eq_op, flat_eq_args) as flat_eq = flatten_eq eq in
    match Hashtbl.find_opt eq_table flat_eq with
    | Some x ->
       Some x
    | None ->
       (* TODO print_eq stderr flat_eq; *)
       incr cur_eq_id;
       let id = !cur_eq_id in
       let coq_id = P.of_int id in
       begin
         Hashtbl.add eq_table flat_eq coq_id;
         (cur_catalog := PTree.set coq_id eq !cur_catalog);
         Hashtbl.add rhs_table (flat_eq_op, flat_eq_args)
           (PSet.add coq_id
              (match Hashtbl.find_opt rhs_table (flat_eq_op, flat_eq_args) with
               | None -> PSet.empty
               | Some s -> s));
         List.iter
           (fun reg -> imp_add_i_j cur_kill_reg reg coq_id)
           (eq.eq_lhs :: eq.eq_args);
         (if eq_depends_on_mem eq
          then cur_kill_mem := PSet.add coq_id !cur_kill_mem);
         (match eq.eq_op, eq.eq_args with
          | (SOp Op.Omove), [rhs] -> imp_add_i_j cur_moves eq.eq_lhs coq_id
          | _, _ -> ());
         Some coq_id
       end
  in
  match
    internal_analysis
      { eq_catalog     = (fun eq_id -> PTree.get eq_id !cur_catalog);
        eq_find_oracle = mutating_eq_find_oracle;
        eq_rhs_oracle  = rhs_find_oracle ;
        eq_kill_reg    = (fun reg -> PMap.get reg !cur_kill_reg);
        eq_kill_mem    = (fun () -> !cur_kill_mem);
        eq_moves       = (fun reg -> PMap.get reg !cur_moves)
      } tenv f
  with None -> failwith "CSE3analysisaux analysis failed, try re-running with -fno-cse3"
     | Some invariants ->
        invariants,
        { hint_eq_catalog    = !cur_catalog;
          hint_eq_find_oracle= eq_find_oracle;
          hint_eq_rhs_oracle = rhs_find_oracle };;
