(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open LTL
open Maps

let debug_flag = ref false

let debug fmt =
  if !debug_flag then Printf.eprintf fmt
  else Printf.ifprintf stderr fmt

(* Trivial enumeration, in decreasing order of PC *)

(***
let enumerate_aux f reach =
  positive_rec
    Coq_nil
    (fun pc nodes ->
      if PMap.get pc reach
      then Coq_cons (pc, nodes)
      else nodes)
    f.fn_nextpc
***)

(* More clever enumeration that flattens basic blocks *)

open Camlcoq

module IntSet = Set.Make(struct type t = int let compare = compare end)

(* Determine join points: reachable nodes that have > 1 predecessor *)

let join_points f =
  let reached = ref IntSet.empty in
  let reached_twice = ref IntSet.empty in
  let rec traverse pc =
    let npc = P.to_int pc in
    if IntSet.mem npc !reached then begin
      if not (IntSet.mem npc !reached_twice) then
        reached_twice := IntSet.add npc !reached_twice
    end else begin
      reached := IntSet.add npc !reached;
      match PTree.get pc f.fn_code with
      | None -> ()
      | Some b -> traverse_succs (successors_block b)
    end
  and traverse_succs = function
    | [] -> ()
    | [pc] -> traverse pc
    | pc :: l -> traverse pc; traverse_succs l
  in traverse f.fn_entrypoint; !reached_twice

(* Cut into reachable basic blocks, annotated with the min value of the PC *)

let basic_blocks f joins =
  let blocks = ref [] in
  let visited = ref IntSet.empty in
  (* start_block:
       pc is the function entry point
          or a join point
          or the successor of a conditional test *)
  let rec start_block pc =
    let npc = P.to_int pc in
    if not (IntSet.mem npc !visited) then begin
      visited := IntSet.add npc !visited;
      in_block [] max_int pc
    end
  (* in_block: add pc to block and check successors *)
  and in_block blk minpc pc =
    let npc = P.to_int pc in
    let blk = pc :: blk in
    let minpc = min npc minpc in
    match PTree.get pc f.fn_code with
    | None -> assert false
    | Some b ->
       let rec do_instr_list = function
       | [] -> assert false
       | Lbranch s :: _ -> next_in_block blk minpc s
       | Ltailcall (sig0, ros) :: _ -> end_block blk minpc
       | Lcond (cond, args, ifso, ifnot, _) :: _ ->
             end_block blk minpc; start_block ifso; start_block ifnot
       | Ljumptable(arg, tbl) :: _ ->
             end_block blk minpc; List.iter start_block tbl
       | Lreturn :: _ -> end_block blk minpc
       | instr :: b' -> do_instr_list b' in
       do_instr_list b
  (* next_in_block: check if join point and either extend block
     or start block *)
  and next_in_block blk minpc pc =
    let npc = P.to_int pc in
    if IntSet.mem npc joins
    then (end_block blk minpc; start_block pc)
    else in_block blk minpc pc
  (* end_block: record block that we just discovered *)
  and end_block blk minpc =
    blocks := (minpc, List.rev blk) :: !blocks
  in
    start_block f.fn_entrypoint; !blocks

(* Flatten basic blocks in decreasing order of minpc *)

let flatten_blocks blks =
  let cmp_minpc (mpc1, _) (mpc2, _) =
    if mpc1 = mpc2 then 0 else if mpc1 > mpc2 then -1 else 1
  in
    List.flatten (List.map snd (List.sort cmp_minpc blks))

(* Build the enumeration *)

let enumerate_aux_flat f reach =
  flatten_blocks (basic_blocks f (join_points f))

(**
 * Alternate enumeration based on traces as identified by Duplicate.v 
 *
 * This is a slight alteration to the above heuristic, ensuring that any
 * superblock will be contiguous in memory, while still following the original
 * heuristic
 *)

let get_some = function
| None -> failwith "Did not get some"
| Some thing -> thing

exception EmptyList

let rec last_element = function
  | [] -> raise EmptyList
  | e :: [] -> e
  | e' :: e :: l -> last_element (e::l)

let print_plist l =
  let rec f = function
  | [] -> ()
  | n :: l -> Printf.printf "%d, " (P.to_int n); f l
  in begin
    if !debug_flag then begin
      Printf.printf "[";
      f l;
      Printf.printf "]"
    end
  end

(* adapted from the above join_points function, but with PTree *)
let get_join_points code entry =
  let reached = ref (PTree.map (fun n i -> false) code) in
  let reached_twice = ref (PTree.map (fun n i -> false) code) in
  let rec traverse pc =
    if get_some @@ PTree.get pc !reached then begin
      if not (get_some @@ PTree.get pc !reached_twice) then
        reached_twice := PTree.set pc true !reached_twice
    end else begin
      reached := PTree.set pc true !reached;
      traverse_succs (successors_block @@ get_some @@ PTree.get pc code)
    end
  and traverse_succs = function
    | [] -> ()
    | [pc] -> traverse pc
    | pc :: l -> traverse pc; traverse_succs l
  in traverse entry; !reached_twice

let forward_sequences code entry =
  let visited = ref (PTree.map (fun n i -> false) code) in
  let join_points = get_join_points code entry in
  (* returns the list of traversed nodes, and a list of nodes to start traversing next *)
  let rec traverse_fallthrough code node =
    (* debug "Traversing %d..\n" (P.to_int node); *)
    if not (get_some @@ PTree.get node !visited) then begin
      visited := PTree.set node true !visited;
      match PTree.get node code with
      | None -> failwith "No such node"
      | Some bb ->
          let ln, rem = match (last_element bb) with
          | Lop _ | Lload _ | Lgetstack _ | Lsetstack _ | Lstore _ | Lcall _
          | Lbuiltin _ -> assert false
          | Ltailcall _ | Lreturn -> begin (* debug "STOP tailcall/return\n"; *) ([], []) end
          | Lbranch n ->
              if get_some @@ PTree.get n join_points then ([], [n])
              else let ln, rem = traverse_fallthrough code n in (ln, rem)
          | Lcond (_, _, ifso, ifnot, info) -> (match info with
            | None -> begin (* debug "STOP Lcond None\n"; *) ([], [ifso; ifnot]) end
            | Some false ->
                if get_some @@ PTree.get ifnot join_points then ([], [ifso; ifnot])
                else let ln, rem = traverse_fallthrough code ifnot in (ln, [ifso] @ rem)
            | Some true ->
                if get_some @@ PTree.get ifso join_points then ([], [ifso; ifnot])
                else let ln, rem = traverse_fallthrough code ifso in (ln, [ifnot] @ rem)
            )
          | Ljumptable(_, ln) -> begin (* debug "STOP Ljumptable\n"; *) ([], ln) end
          in ([node] @ ln, rem)
      end
    else ([], [])
  in let rec f code = function
  | [] -> []
  | node :: ln ->
      let fs, rem_from_node = traverse_fallthrough code node
      in [fs] @ ((f code rem_from_node) @ (f code ln))
  in (f code [entry])

(** Unused code
module PInt = struct
  type t = P.t
  let compare x y = compare (P.to_int x) (P.to_int y)
end

module PSet = Set.Make(PInt)

module LPInt = struct
  type t = P.t list
  let rec compare x y =
    match x with
    | [] -> ( match y with
      | [] -> 0
      | _ -> 1 )
    | e :: l -> match y with
      | [] -> -1
      | e' :: l' ->
          let e_cmp = PInt.compare e e' in
          if e_cmp == 0 then compare l l' else e_cmp
end

module LPSet = Set.Make(LPInt)

let iter_lpset f s = Seq.iter f (LPSet.to_seq s)

let first_of = function
  | [] -> None
  | e :: l -> Some e

let rec last_of = function
  | [] -> None
  | e :: l -> (match l with [] -> Some e | e :: l -> last_of l)

let can_be_merged code s s' =
  let last_s = get_some @@ last_of s in
  let first_s' = get_some @@ first_of s' in
  match get_some @@ PTree.get last_s code with
  | Lop _ | Lload _ | Lgetstack _ | Lsetstack _ | Lstore _ | Lcall _
  | Lbuiltin _ | Ltailcall _ | Lreturn -> false
  | Lbranch n -> n == first_s'
  | Lcond (_, _, ifso, ifnot, info) -> (match info with
    | None -> false
    | Some false -> ifnot == first_s'
    | Some true -> failwith "Inconsistency detected - ifnot is not the preferred branch")
  | Ljumptable (_, ln) ->
      match ln with
      | [] -> false
      | n :: ln -> n == first_s'

let merge s s' = Some s

let try_merge code (fs: (BinNums.positive list) list) =
  let seqs = ref (LPSet.of_list fs) in
  let oldLength = ref (LPSet.cardinal !seqs) in
  let continue = ref true in
  let found = ref false in
  while !continue do
    begin
      found := false;
      iter_lpset (fun s ->
        if !found then ()
        else iter_lpset (fun s' ->
          if (!found || s == s') then ()
          else if (can_be_merged code s s') then
            begin
              seqs := LPSet.remove s !seqs;
              seqs := LPSet.remove s' !seqs;
              seqs := LPSet.add (get_some (merge s s')) !seqs;
              found := true;
            end
          else ()
        ) !seqs
      ) !seqs;
      if !oldLength == LPSet.cardinal !seqs then
        continue := false
      else
        oldLength := LPSet.cardinal !seqs
    end
  done;
  !seqs
*)

(** Code adapted from Duplicateaux.get_loop_headers
  *
  * Getting loop branches with a DFS visit :
  * Each node is either Unvisited, Visited, or Processed
  * pre-order: node becomes Processed
  * post-order: node becomes Visited
  *
  * If we come accross an edge to a Processed node, it's a loop!
  *)
type pos = BinNums.positive

module PP = struct
  type t = pos * pos
  let compare a b =
    let ax, ay = a in
    let bx, by = b in
    let dx = compare ax bx in
    if (dx == 0) then compare ay by
    else dx
end

module PPMap = Map.Make(PP)

type vstate = Unvisited | Processed | Visited

let get_loop_edges code entry =
  let visited = ref (PTree.map (fun n i -> Unvisited) code) in
  let is_loop_edge = ref PPMap.empty
  in let rec dfs_visit code from = function
  | [] -> ()
  | node :: ln ->
      match (get_some @@ PTree.get node !visited) with
      | Visited -> ()
      | Processed -> begin
          let from_node = get_some from in
          is_loop_edge := PPMap.add (from_node, node) true !is_loop_edge;
          visited := PTree.set node Visited !visited
        end
      | Unvisited -> begin
          visited := PTree.set node Processed !visited;
          let bb = get_some @@ PTree.get node code in
          let next_visits = (match (last_element bb) with
          | Lop _ | Lload _ | Lgetstack _ | Lsetstack _ | Lstore _ | Lcall _
          | Lbuiltin _ -> assert false
          | Ltailcall _ | Lreturn -> []
          | Lbranch n -> [n]
          | Lcond (_, _, ifso, ifnot, _) -> [ifso; ifnot]
          | Ljumptable(_, ln) -> ln
          ) in dfs_visit code (Some node) next_visits;
          visited := PTree.set node Visited !visited;
          dfs_visit code from ln
        end
  in begin
    dfs_visit code None [entry];
    !is_loop_edge
  end

let ppmap_is_true pp ppmap = PPMap.mem pp ppmap && PPMap.find pp ppmap

module Int = struct
  type t = int
  let compare x y = compare x y
end

module ISet = Set.Make(Int)

let print_iset s = begin
  if !debug_flag then begin
    Printf.printf "{";
    ISet.iter (fun e -> Printf.printf "%d, " e) s;
    Printf.printf "}"
  end
end

let print_depmap dm = begin
  if !debug_flag then begin
    Printf.printf "[|";
    Array.iter (fun s -> print_iset s; Printf.printf ", ") dm;
    Printf.printf "|]\n"
  end
end

let construct_depmap code entry fs =
  let is_loop_edge = get_loop_edges code entry in
  let visited = ref (PTree.map (fun n i -> false) code) in
  let depmap = Array.map (fun e -> ISet.empty) fs in
  let find_index_of_node n =
    let index = ref 0 in
    begin
      Array.iteri (fun i s ->
        match List.find_opt (fun e -> e == n) s with
        | Some _ -> index := i
        | None -> ()
      ) fs;
      !index
    end
  in let check_and_update_depmap from target =
    (* debug "From %d to %d\n" (P.to_int from) (P.to_int target); *)
    if not (ppmap_is_true (from, target) is_loop_edge) then
      let in_index_fs = find_index_of_node from in
      let out_index_fs = find_index_of_node target in
      if out_index_fs != in_index_fs then
        depmap.(out_index_fs) <- ISet.add in_index_fs depmap.(out_index_fs)
      else ()
    else ()
  in let rec dfs_visit code = function
  | [] -> ()
  | node :: ln ->
      begin
        match (get_some @@ PTree.get node !visited) with
        | true -> ()
        | false -> begin
            visited := PTree.set node true !visited;
            let bb = get_some @@ PTree.get node code in
            let next_visits =
              match (last_element bb) with
              | Ltailcall _ | Lreturn -> []
              | Lbranch n -> (check_and_update_depmap node n; [n])
              | Lcond (_, _, ifso, ifnot, _) -> begin
                  check_and_update_depmap node ifso;
                  check_and_update_depmap node ifnot;
                  [ifso; ifnot]
                end
              | Ljumptable(_, ln) -> begin
                  List.iter (fun n -> check_and_update_depmap node n) ln;
                  ln
                end
              (* end of bblocks should not be another value than one of the above *)
              | _ -> failwith "last_element gave an invalid output"
            in dfs_visit code next_visits
          end;
        dfs_visit code ln
      end
  in begin
    dfs_visit code [entry];
    depmap
  end

let print_sequence s =
  if !debug_flag then begin
    Printf.printf "[";
    List.iter (fun n -> Printf.printf "%d, " (P.to_int n)) s;
    Printf.printf "]\n"
  end

let print_ssequence ofs =
  if !debug_flag then begin
    Printf.printf "[";
    List.iter (fun s -> print_sequence s) ofs;
    Printf.printf "]\n"
  end

let order_sequences code entry fs =
  let fs_a = Array.of_list fs in
  let depmap = construct_depmap code entry fs_a in
  let fs_evaluated = Array.map (fun e -> false) fs_a in
  let ordered_fs = ref [] in
  let evaluate s_id =
    begin
      assert (not fs_evaluated.(s_id));
      ordered_fs := fs_a.(s_id) :: !ordered_fs;
      fs_evaluated.(s_id) <- true;
      (* debug "++++++\n";
      debug "Scheduling %d\n" s_id;
      debug "Initial depmap: "; print_depmap depmap; *)
      Array.iteri (fun i deps ->
        depmap.(i) <- ISet.remove s_id deps
      ) depmap;
      (* debug "Final depmap: "; print_depmap depmap; *)
    end
  in let choose_best_of candidates =
    let current_best_id = ref None in
    let current_best_score = ref None in
    begin
      List.iter (fun id ->
        match !current_best_id with
        | None -> begin
            current_best_id := Some id;
            match fs_a.(id) with
            | [] -> current_best_score := None
            | n::l -> current_best_score := Some (P.to_int n)
          end
        | Some b -> begin
            match fs_a.(id) with
            | [] -> ()
            | n::l -> let nscore = P.to_int n in
              match !current_best_score with
              | None -> (current_best_id := Some id; current_best_score := Some nscore)
              | Some bs -> if nscore > bs then (current_best_id := Some id; current_best_score := Some nscore)
          end
      ) candidates;
      !current_best_id
    end
  in let select_next () =
    let candidates = ref [] in
    begin
      Array.iteri (fun i deps ->
        begin
          (* debug "Deps of %d: " i; print_iset deps; debug "\n"; *)
          (* FIXME - if we keep it that way (no dependency check), remove all the unneeded stuff *)
          if ((* deps == ISet.empty && *) not fs_evaluated.(i)) then
            candidates := i :: !candidates
        end
      ) depmap;
      if not (List.length !candidates > 0) then begin
        Array.iteri (fun i deps ->
          if (not fs_evaluated.(i)) then candidates := i :: !candidates
        ) depmap;
      end;
      get_some (choose_best_of !candidates)
    end
  in begin
    debug "-------------------------------\n";
    debug "depmap: "; print_depmap depmap;
    debug "forward sequences identified: "; print_ssequence fs;
    while List.length !ordered_fs != List.length fs do
      let next_id = select_next () in
      evaluate next_id
    done;
    debug "forward sequences ordered: "; print_ssequence (List.rev (!ordered_fs));
    List.rev (!ordered_fs)
  end

let enumerate_aux_trace f reach =
  let code = f.fn_code in
  let entry = f.fn_entrypoint in
  let fs = forward_sequences code entry in
  let ofs = order_sequences code entry fs in
  List.flatten ofs

let enumerate_aux f reach =
  if !Clflags.option_ftracelinearize then enumerate_aux_trace f reach
  else enumerate_aux_flat f reach
