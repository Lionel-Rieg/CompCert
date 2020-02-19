
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
       | Lcond (cond, args, ifso, ifnot) :: _ ->
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
 * Enumeration based on traces as identified by Duplicate.v 
 *
 * The Duplicate phase heuristically identifies the most frequented paths. Each
 * Icond is modified so that the preferred condition is a fallthrough (ifnot)
 * rather than a branch (ifso).
 *
 * The enumeration below takes advantage of this - preferring to layout nodes
 * following the fallthroughs of the Lcond branches.
 *
 * It is slightly adapted from the work of Petris and Hansen 90 on intraprocedural
 * code positioning - only we do it on a broader grain, since we don't have the exact
 * frequencies (we only know which branch is the preferred one)
 *)

let get_some = function
| None -> failwith "Did not get some"
| Some thing -> thing

exception EmptyList

let rec last_element = function
  | [] -> raise EmptyList
  | e :: [] -> e
  | e' :: e :: l -> last_element (e::l)

(** old version
let dfs code entrypoint =
  let visited = ref (PTree.map (fun n i -> false) code) in
  let rec dfs_list code = function
  | [] -> []
  | node :: ln ->
      let node_dfs =
        if not (get_some @@ PTree.get node !visited) then begin
          visited := PTree.set node true !visited;
          match PTree.get node code with
          | None -> failwith "No such node"
          | Some bb -> [node] @ match (last_element bb) with
            | Lop _ | Lload _ | Lgetstack _ | Lsetstack _ | Lstore _ | Lcall _
            | Lbuiltin _ -> assert false
            | Ltailcall _ | Lreturn -> []
            | Lbranch n -> dfs_list code [n]
            | Lcond (_, _, ifso, ifnot) -> dfs_list code [ifnot; ifso]
            | Ljumptable(_, ln) -> dfs_list code ln
          end
        else []
      in node_dfs @ (dfs_list code ln)
  in dfs_list code [entrypoint]

let enumerate_aux_trace f reach = dfs f.fn_code f.fn_entrypoint
*)


let forward_sequences code entry =
  let visited = ref (PTree.map (fun n i -> false) code) in
  (* returns the list of traversed nodes, and a list of nodes to start traversing next *)
  let rec traverse_fallthrough code node =
    if not (get_some @@ PTree.get node !visited) then begin
      visited := PTree.set node true !visited;
      match PTree.get node code with
      | None -> failwith "No such node"
      | Some bb ->
          let ln, rem = match (last_element bb) with
          | Lop _ | Lload _ | Lgetstack _ | Lsetstack _ | Lstore _ | Lcall _
          | Lbuiltin _ -> assert false
          | Ltailcall _ | Lreturn -> ([], [])
          | Lbranch n -> let ln, rem = traverse_fallthrough code n in (ln, rem)
          | Lcond (_, _, ifso, ifnot) -> let ln, rem = traverse_fallthrough code ifnot in (ln, [ifso] @ rem)
          | Ljumptable(_, ln) -> match ln with
              | [] -> ([], [])
              | n :: ln -> let lln, rem = traverse_fallthrough code n in (lln, ln @ rem)
          in ([node] @ ln, rem)
      end
    else ([], [])
  in let rec f code = function
  | [] -> []
  | node :: ln ->
      let fs, rem = traverse_fallthrough code node
      in [fs] @ (f code rem)
  in (f code [entry])

let order_sequences fs = fs

let enumerate_aux_trace f reach =
  let fs = forward_sequences f.fn_code f.fn_entrypoint
  in let ofs = order_sequences fs
  in List.flatten ofs

let enumerate_aux f reach =
  if !Clflags.option_ftracelinearize then enumerate_aux_trace f reach
  else enumerate_aux_flat f reach
