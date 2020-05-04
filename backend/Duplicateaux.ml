(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(* Oracle for Duplicate pass.
 * - Add static prediction information to Icond nodes
 * - Performs tail duplication on interesting traces to form superblocks
 * - (TODO: perform partial loop unrolling inside innermost loops)
 *)

open RTL
open Maps
open Camlcoq

let debug_flag = ref false

let debug fmt =
  if !debug_flag then Printf.eprintf fmt
  else Printf.ifprintf stderr fmt

let get_some = function
| None -> failwith "Did not get some"
| Some thing -> thing

let rtl_successors = function
| Itailcall _ | Ireturn _ -> []
| Icall(_,_,_,_,n) | Ibuiltin(_,_,_,n) | Inop n | Iop (_,_,_,n)
| Iload (_,_,_,_,_,n) | Istore (_,_,_,_,n) -> [n]
| Icond (_,_,n1,n2,_) -> [n1; n2]
| Ijumptable (_,ln) -> ln

let bfs code entrypoint = begin
  debug "bfs\n";
  let visited = ref (PTree.map (fun n i -> false) code)
  and bfs_list = ref []
  and to_visit = Queue.create ()
  and node = ref entrypoint
  in begin
    Queue.add entrypoint to_visit;
    while not (Queue.is_empty to_visit) do
      node := Queue.pop to_visit;
      if not (get_some @@ PTree.get !node !visited) then begin
        visited := PTree.set !node true !visited;
        match PTree.get !node code with
        | None -> failwith "No such node"
        | Some i ->
            bfs_list := !node :: !bfs_list;
            let succ = rtl_successors i in
            List.iter (fun n -> Queue.add n to_visit) succ
      end
    done;
    List.rev !bfs_list
  end
end

let optbool o = match o with Some _ -> true | None -> false

let ptree_get_some n ptree = get_some @@ PTree.get n ptree

let get_predecessors_rtl code = begin
  debug "get_predecessors_rtl\n";
  let preds = ref (PTree.map (fun n i -> []) code) in
  let process_inst (node, i) =
    let succ = rtl_successors i
    in List.iter (fun s ->
      let previous_preds = ptree_get_some s !preds in
      if optbool @@ List.find_opt (fun e -> e == node) previous_preds then ()
      else preds := PTree.set s (node::previous_preds) !preds) succ
  in begin
    List.iter process_inst (PTree.elements code);
    !preds
  end
end

module PInt = struct
  type t = P.t
  let compare x y = compare (P.to_int x) (P.to_int y)
end

module PSet = Set.Make(PInt)

let print_intlist l =
  let rec f = function
  | [] -> ()
  | n::ln -> (Printf.printf "%d " (P.to_int n); f ln)
  in begin
    if !debug_flag then begin
      Printf.printf "[";
      f l;
      Printf.printf "]"
    end
  end

let print_intset s =
  let seq = PSet.to_seq s
  in begin
    if !debug_flag then begin
      Printf.printf "{";
      Seq.iter (fun n ->
        Printf.printf "%d " (P.to_int n)
      ) seq;
      Printf.printf "}"
    end
  end

type vstate = Unvisited | Processed | Visited

(** Getting loop branches with a DFS visit :
  * Each node is either Unvisited, Visited, or Processed
  * pre-order: node becomes Processed
  * post-order: node becomes Visited
  *
  * If we come accross an edge to a Processed node, it's a loop!
  *)
let get_loop_headers code entrypoint = begin
  debug "get_loop_headers\n";
  let visited = ref (PTree.map (fun n i -> Unvisited) code)
  and is_loop_header = ref (PTree.map (fun n i -> false) code)
  in let rec dfs_visit code = function
  | [] -> ()
  | node :: ln ->
      match (get_some @@ PTree.get node !visited) with
      | Visited -> ()
      | Processed -> begin
          debug "Node %d is a loop header\n" (P.to_int node);
          is_loop_header := PTree.set node true !is_loop_header;
          visited := PTree.set node Visited !visited
        end
      | Unvisited -> begin
          visited := PTree.set node Processed !visited;
          match PTree.get node code with
          | None -> failwith "No such node"
          | Some i -> let next_visits = rtl_successors i in dfs_visit code next_visits;
          visited := PTree.set node Visited !visited;
          dfs_visit code ln
        end
  in begin
    dfs_visit code [entrypoint];
    !is_loop_header
  end
end

let ptree_printbool pt =
  let elements = PTree.elements pt
  in begin
    if !debug_flag then begin
      Printf.printf "[";
      List.iter (fun (n, b) ->
        if b then Printf.printf "%d, " (P.to_int n) else ()
      ) elements;
      Printf.printf "]"
    end
  end

(* Looks ahead (until a branch) to see if a node further down verifies
 * the given predicate *)
let rec look_ahead code node is_loop_header predicate =
  if (predicate node) then true
  else match (rtl_successors @@ get_some @@ PTree.get node code) with
    | [n] -> if (predicate n) then true
        else (
          if (get_some @@ PTree.get n is_loop_header) then false
          else look_ahead code n is_loop_header predicate
        )
    | _ -> false

let do_call_heuristic code cond ifso ifnot is_loop_header =
  begin
    debug "\tCall heuristic..\n";
    let predicate n = (function
    | Icall _ -> true
    | _ -> false) @@ get_some @@ PTree.get n code
    in let ifso_call = look_ahead code ifso is_loop_header predicate
    in let ifnot_call = look_ahead code ifnot is_loop_header predicate
    in if ifso_call && ifnot_call then None
    else if ifso_call then Some false
    else if ifnot_call then Some true
    else None
  end

let do_opcode_heuristic code cond ifso ifnot is_loop_header =
  begin
    debug "\tOpcode heuristic..\n";
    DuplicateOpcodeHeuristic.opcode_heuristic code cond ifso ifnot is_loop_header
  end

let do_return_heuristic code cond ifso ifnot is_loop_header =
  begin
    debug "\tReturn heuristic..\n";
    let predicate n = (function
    | Ireturn _ -> true
    | _ -> false) @@ get_some @@ PTree.get n code
    in let ifso_return = look_ahead code ifso is_loop_header predicate
    in let ifnot_return = look_ahead code ifnot is_loop_header predicate
    in if ifso_return && ifnot_return then None
    else if ifso_return then Some false
    else if ifnot_return then Some true
    else None
  end

let do_store_heuristic code cond ifso ifnot is_loop_header =
  begin
    debug "\tStore heuristic..\n";
    let predicate n = (function
    | Istore _ -> true
    | _ -> false) @@ get_some @@ PTree.get n code
    in let ifso_store = look_ahead code ifso is_loop_header predicate
    in let ifnot_store = look_ahead code ifnot is_loop_header predicate
    in if ifso_store && ifnot_store then None
    else if ifso_store then Some false
    else if ifnot_store then Some true
    else None
  end

let do_loop_heuristic code cond ifso ifnot is_loop_header =
  begin
    debug "\tLoop heuristic..\n";
    let predicate n = get_some @@ PTree.get n is_loop_header in
    let ifso_loop = look_ahead code ifso is_loop_header predicate in
    let ifnot_loop = look_ahead code ifnot is_loop_header predicate in
    if ifso_loop && ifnot_loop then None (* TODO - take the innermost loop ? *)
    else if ifso_loop then Some true
    else if ifnot_loop then Some false
    else None
  end

let do_loop2_heuristic loop_info n code cond ifso ifnot is_loop_header =
  begin
    debug "\tLoop2 heuristic..\n";
    match get_some @@ PTree.get n loop_info with
    | None -> None
    | Some b -> Some b
  end

(* Returns a PTree of either None or Some b where b determines the node following the loop, for a cb instruction *)
(* It uses the fact that loops in CompCert are done by a branch (backedge) instruction followed by a cb *)
let get_loop_info is_loop_header bfs_order code =
  let loop_info = ref (PTree.map (fun n i -> None) code) in
  let mark_path s n =
    let visited = ref (PTree.map (fun n i -> false) code) in
    let rec explore src dest =
      if (get_some @@ PTree.get src !visited) then false
      else if src == dest then true
      else begin
        visited := PTree.set src true !visited;
        match rtl_successors @@ get_some @@ PTree.get src code with
        | [] -> false
        | [s] -> explore s dest
        | [s1; s2] -> (explore s1 dest) || (explore s2 dest)
        | _ -> false
      end
    in let rec advance_to_cb src =
      if (get_some @@ PTree.get src !visited) then None
      else begin
        visited := PTree.set src true !visited;
        match get_some @@ PTree.get src code with
        | Inop s | Iop (_, _, _, s) | Iload (_,_,_,_,_,s) | Istore (_,_,_,_,s) | Icall (_,_,_,_,s)
        | Ibuiltin (_,_,_,s) -> advance_to_cb s
        | Icond _ -> Some src
        | Ijumptable _ | Itailcall _ | Ireturn _ -> None
      end
    in begin
      debug "Marking path from %d to %d\n" (P.to_int n) (P.to_int s);
      match advance_to_cb s with
      | None -> (debug "Nothing found\n")
      | Some s -> ( debug "Advancing to %d\n" (P.to_int s);
          match get_some @@ PTree.get s !loop_info with
          | None | Some _ -> begin
              match get_some @@ PTree.get s code with
              | Icond (_, _, n1, n2, _) ->
                  let b1 = explore n1 n in
                  let b2 = explore n2 n in
                  if (b1 && b2) then (debug "both true\n")
                  else if b1 then (debug "true privileged\n"; loop_info := PTree.set s (Some true) !loop_info)
                  else if b2 then (debug "false privileged\n"; loop_info := PTree.set s (Some false) !loop_info)
                  else (debug "none true\n")
              | _ -> ( debug "not an icond\n" )
            end
          (* | Some _ -> ( debug "already loop info there\n" ) FIXME - we don't know yet whether a branch to a loop head is a backedge or not *)
        )
    end
  in begin
    List.iter (fun n ->
      match get_some @@ PTree.get n code with
      | Inop s | Iop (_,_,_,s) | Iload (_,_,_,_,_,s) | Istore (_,_,_,_,s) | Icall (_,_,_,_,s)
      | Ibuiltin (_, _, _, s) ->
          if get_some @@ PTree.get s is_loop_header then mark_path s n
      | Icond _ -> () (* loop backedges are never Icond in CompCert RTL.3 *)
      | Ijumptable _ -> ()
      | Itailcall _ | Ireturn _ -> ()
    ) bfs_order;
    !loop_info
  end

(* Remark - compared to the original paper, we don't use the store heuristic *)
let get_directions code entrypoint = begin
  debug "get_directions\n";
  let bfs_order = bfs code entrypoint in
  let is_loop_header = get_loop_headers code entrypoint in
  let loop_info = get_loop_info is_loop_header bfs_order code in
  let directions = ref (PTree.map (fun n i -> None) code) in (* None <=> no predicted direction *)
  begin
    (* ptree_printbool is_loop_header; *)
    (* debug "\n"; *)
    List.iter (fun n ->
      match (get_some @@ PTree.get n code) with
      | Icond (cond, lr, ifso, ifnot, _) ->
          (* debug "Analyzing %d.." (P.to_int n); *)
          let heuristics = [ do_opcode_heuristic;
            do_return_heuristic; do_loop2_heuristic loop_info n; do_loop_heuristic; do_call_heuristic;
             (* do_store_heuristic *) ] in
          let preferred = ref None in
          begin
            debug "Deciding condition for RTL node %d\n" (P.to_int n);
            List.iter (fun do_heur ->
              match !preferred with
              | None -> preferred := do_heur code cond ifso ifnot is_loop_header
              | Some _ -> ()
            ) heuristics;
            directions := PTree.set n !preferred !directions;
            (match !preferred with | Some false -> debug "\tFALLTHROUGH\n"
                                   | Some true -> debug "\tBRANCH\n"
                                   | None -> debug "\tUNSURE\n");
            debug "---------------------------------------\n"
          end
      | _ -> ()
    ) bfs_order;
    !directions
  end
end

let update_direction direction = function
| Icond (cond, lr, n, n', _) -> Icond (cond, lr, n, n', direction)
| i -> i

let rec update_direction_rec directions = function
| [] -> PTree.empty
| m::lm -> let (n, i) = m
    in let direction = get_some @@ PTree.get n directions
    in PTree.set n (update_direction direction i) (update_direction_rec directions lm)

(* Uses branch prediction to write prediction annotations in Icond *)
let update_directions code entrypoint = begin
  debug "Update_directions\n";
  let directions = get_directions code entrypoint
  in begin
    (* debug "Ifso directions: ";
    ptree_printbool directions;
    debug "\n"; *)
    update_direction_rec directions (PTree.elements code)
  end
end

(** Trace selection *)

let rec exists_false_rec = function
  | [] -> false
  | m::lm -> let (_, b) = m in if b then exists_false_rec lm else true

let exists_false boolmap = exists_false_rec (PTree.elements boolmap)

(* DFS using prediction info to guide the exploration *)
let dfs code entrypoint = begin
  debug "dfs\n";
  let visited = ref (PTree.map (fun n i -> false) code) in
  let rec dfs_list code = function
  | [] -> []
  | node :: ln ->
      if get_some @@ PTree.get node !visited then dfs_list code ln
      else begin
        visited := PTree.set node true !visited;
        let next_nodes = (match get_some @@ PTree.get node code with
        | Icall(_, _, _, _, n) | Ibuiltin (_, _, _, n) | Iop (_, _, _, n)
        | Iload (_, _, _, _, _, n) | Istore (_, _, _, _, n) | Inop n -> [n]
        | Ijumptable (_, ln) -> ln
        | Itailcall _ | Ireturn _ -> []
        | Icond (_, _, n1, n2, info) -> (match info with
          | Some false -> [n2; n1]
          | _ -> [n1; n2]
          )
        ) in node :: dfs_list code (next_nodes @ ln)
      end
  in dfs_list code [entrypoint]
end

let rec select_unvisited_node is_visited = function
| [] -> failwith "Empty list"
| n :: ln -> if not (ptree_get_some n is_visited) then n else select_unvisited_node is_visited ln

let best_successor_of node code is_visited =
  match (PTree.get node code) with
  | None -> failwith "No such node in the code"
  | Some i ->
      let next_node = match i with
      | Inop n | Iop (_,_,_,n) | Iload (_,_,_,_,_,n) | Istore(_,_,_,_,n)
      | Icall (_,_,_,_,n) | Ibuiltin (_,_,_,n) -> Some n
      | Icond (_, _, n1, n2, ob) -> (match ob with None -> None | Some false -> Some n2 | Some true -> Some n1)
      | _ -> None
      in match next_node with
      | None -> None
      | Some n -> if not (ptree_get_some n is_visited) then Some n else None

(* FIXME - could be improved by selecting in priority the predicted paths *)
let best_predecessor_of node predecessors code order is_visited =
  match (PTree.get node predecessors) with
  | None -> failwith "No predecessor list found"
  | Some lp ->
      try Some (List.find (fun n ->
          if (List.mem n lp) && (not (ptree_get_some n is_visited)) then
            match ptree_get_some n code with
            | Icond (_, _, n1, n2, ob) -> (match ob with
              | None -> false
              | Some false -> n == n2
              | Some true -> n == n1
              )
            | _ -> true
          else false
        ) order)
      with Not_found -> None

let print_trace t = print_intlist t

let print_traces traces =
  let rec f = function
  | [] -> ()
  | t::lt -> Printf.printf "\n\t"; print_trace t; Printf.printf ",\n"; f lt
  in begin
    if !debug_flag then begin
      Printf.printf "Traces: {";
      f traces;
      Printf.printf "}\n";
    end
  end

(* Dumb (but linear) trace selection *)
let select_traces_linear code entrypoint =
  let is_visited = ref (PTree.map (fun n i -> false) code) in
  let bfs_order = bfs code entrypoint in
  let rec go_through node = begin
    is_visited := PTree.set node true !is_visited;
    let next_node = match (get_some @@ PTree.get node code) with
      | Icall(_, _, _, _, n) | Ibuiltin (_, _, _, n) | Iop (_, _, _, n)
      | Iload (_, _, _, _, _, n) | Istore (_, _, _, _, n) | Inop n -> Some n
      | Ijumptable _ | Itailcall _ | Ireturn _ -> None
      | Icond (_, _, n1, n2, info) -> (match info with
        | Some false -> Some n2
        | Some true -> Some n1
        | None -> None
        )
    in match next_node with
    | None -> [node]
    | Some n ->
        if not (get_some @@ PTree.get n !is_visited) then node :: go_through n
        else [node]
    end
  in let traces = ref [] in begin
    List.iter (fun n ->
      if not (get_some @@ PTree.get n !is_visited) then
        traces := (go_through n) :: !traces
    ) bfs_order;
    !traces
  end


(* Algorithm mostly inspired from Chang and Hwu 1988
 * "Trace Selection for Compiling Large C Application Programs to Microcode" *)
let select_traces_chang code entrypoint = begin
  debug "select_traces\n";
  let order = dfs code entrypoint in
  let predecessors = get_predecessors_rtl code in
  let traces = ref [] in
  let is_visited = ref (PTree.map (fun n i -> false) code) in begin (* mark all nodes visited *)
    debug "Length: %d\n" (List.length order);
    while exists_false !is_visited do (* while (there are unvisited nodes) *)
      let seed = select_unvisited_node !is_visited order in
      let trace = ref [seed] in
      let current = ref seed in begin
        is_visited := PTree.set seed true !is_visited; (* mark seed visited *)
        let quit_loop = ref false in begin
          while not !quit_loop do
            let s = best_successor_of !current code !is_visited in
            match s with
            | None -> quit_loop := true (* if (s==0) exit loop *)
            | Some succ -> begin
                trace := !trace @ [succ];
                is_visited := PTree.set succ true !is_visited; (* mark s visited *)
                current := succ
                end
          done;
          current := seed;
          quit_loop := false;
          while not !quit_loop do
            let s = best_predecessor_of !current predecessors code order !is_visited in
            match s with
            | None -> quit_loop := true (* if (s==0) exit loop *)
            | Some pred -> begin
                trace := pred :: !trace;
                is_visited := PTree.set pred true !is_visited; (* mark s visited *)
                current := pred
                end
          done;
          traces := !trace :: !traces;
        end
      end
    done;
    (* debug "DFS: \t"; print_intlist order; debug "\n"; *)
    debug "Traces: "; print_traces !traces;
    !traces
  end
end

let select_traces code entrypoint =
  let length = List.length @@ PTree.elements code in
  if (length < 5000) then select_traces_chang code entrypoint
  else select_traces_linear code entrypoint

let rec make_identity_ptree_rec = function
| [] -> PTree.empty
| m::lm -> let (n, _) = m in PTree.set n n (make_identity_ptree_rec lm)

let make_identity_ptree code = make_identity_ptree_rec (PTree.elements code)

(* Change the pointers of preds nodes to point to n' instead of n *)
let rec change_pointers code n n' = function
  | [] -> code
  | pred :: preds ->
      let new_pred_inst = match ptree_get_some pred code with
        | Icall(a, b, c, d, n0) -> assert (n0 == n); Icall(a, b, c, d, n')
        | Ibuiltin(a, b, c, n0) -> assert (n0 == n); Ibuiltin(a, b, c, n')
        | Ijumptable(a, ln) -> assert (optbool @@ List.find_opt (fun e -> e == n) ln);
                               Ijumptable(a, List.map (fun e -> if (e == n) then n' else e) ln)
        | Icond(a, b, n1, n2, i) -> assert (n1 == n || n2 == n);
                                 let n1' = if (n1 == n) then n' else n1
                                 in let n2' = if (n2 == n) then n' else n2
                                 in Icond(a, b, n1', n2', i)
        | Inop n0 -> assert (n0 == n); Inop n'
        | Iop (a, b, c, n0) -> assert (n0 == n); Iop (a, b, c, n')
        | Iload (a, b, c, d, e, n0) -> assert (n0 == n); Iload (a, b, c, d, e, n')
        | Istore (a, b, c, d, n0) -> assert (n0 == n); Istore (a, b, c, d, n')
        | Itailcall _ | Ireturn _ -> failwith "That instruction cannot be a predecessor"
      in let new_code = PTree.set pred new_pred_inst code
      in change_pointers new_code n n' preds

(* parent: parent of n to keep as parent
 * preds: all the other parents of n
 * n': the integer which should contain the duplicate of n
 * returns: new code, new ptree *)
let duplicate code ptree parent n preds n' =
  debug "Duplicating node %d into %d..\n" (P.to_int n) (P.to_int n');
  match PTree.get n' code with
  | Some _ -> failwith "The PTree already has a node n'"
  | None ->
      let c' = change_pointers code n n' preds
      in let new_code = PTree.set n' (ptree_get_some n code) c'
      and new_ptree = PTree.set n' n ptree
      in (new_code, new_ptree)

let rec maxint = function
  | [] -> 0
  | i :: l -> assert (i >= 0); let m = maxint l in if i > m then i else m

let is_empty = function
  | [] -> true
  | _ -> false

(* code: RTL code
 * preds: mapping node -> predecessors
 * ptree: the revmap
 * trace: the trace to follow tail duplication on *)
let tail_duplicate code preds ptree trace =
  (* next_int: unused integer that can be used for the next duplication *)
  let next_int = ref (maxint (List.map (fun e -> let (n, _) = e in P.to_int n) (PTree.elements code)) + 1)
  (* last_node and last_duplicate store resp. the last processed node of the trace, and its duplication *)
  in let last_node = ref None
  in let last_duplicate = ref None
  in let nb_duplicated = ref 0
  (* recursive function on a trace *)
  in let rec f code ptree is_first = function
    | [] -> (code, ptree)
    | n :: t ->
        let (new_code, new_ptree) =
          if is_first then (code, ptree) (* first node is never duplicated regardless of its inputs *)
          else
            let node_preds = ptree_get_some n preds
            in let node_preds_nolast = List.filter (fun e -> e <> get_some !last_node) node_preds
            in let final_node_preds = match !last_duplicate with
              | None -> node_preds_nolast
              | Some n' -> n' :: node_preds_nolast
            in if not (is_empty final_node_preds) then
              let n' = !next_int
              in let (newc, newp) = duplicate code ptree !last_node n final_node_preds (P.of_int n')
              in begin
                next_int := !next_int + 1;
                nb_duplicated := !nb_duplicated + 1;
                last_duplicate := Some (P.of_int n');
                (newc, newp)
              end
            else (code, ptree)
        in begin
          last_node := Some n;
          f new_code new_ptree false t
        end
  in let new_code, new_ptree = f code ptree true trace
  in (new_code, new_ptree, !nb_duplicated)

let superblockify_traces code preds traces =
  let max_nb_duplicated = !Clflags.option_fduplicate (* FIXME - should be architecture dependent *)
  in let ptree = make_identity_ptree code
  in let rec f code ptree = function
    | [] -> (code, ptree, 0)
    | trace :: traces ->
        let new_code, new_ptree, nb_duplicated = tail_duplicate code preds ptree trace
        in if (nb_duplicated < max_nb_duplicated)
          then (debug "End duplication\n"; f new_code new_ptree traces)
          else (debug "Too many duplicated nodes, aborting tail duplication\n"; (code, ptree, 0))
  in let new_code, new_ptree, _ = f code ptree traces
  in (new_code, new_ptree)

let rec invert_iconds_trace code = function
  | [] -> code
  | n :: ln ->
      let code' = match ptree_get_some n code with
        | Icond (c, lr, ifso, ifnot, info) -> (match info with
            | Some true -> begin
                (* debug "Reversing ifso/ifnot for node %d\n" (P.to_int n); *)
                PTree.set n (Icond (Op.negate_condition c, lr, ifnot, ifso, Some false)) code
              end
            | _ -> code)
        | _ -> code
      in invert_iconds_trace code' ln

let rec invert_iconds code = function
  | [] -> code
  | t :: ts ->
      let code' = if !Clflags.option_finvertcond then invert_iconds_trace code t
                  else code
      in invert_iconds code' ts

let duplicate_aux f =
  let entrypoint = f.fn_entrypoint in
  if !Clflags.option_fduplicate < 0 then
    ((f.fn_code, entrypoint), make_identity_ptree f.fn_code)
  else
    let code = update_directions (f.fn_code) entrypoint in
    let traces = select_traces code entrypoint in
    let icond_code = invert_iconds code traces in
    let preds = get_predecessors_rtl icond_code in
    if !Clflags.option_fduplicate >= 1 then
      let (new_code, pTreeId) = ((* print_traces traces; *) superblockify_traces icond_code preds traces) in
      ((new_code, f.fn_entrypoint), pTreeId)
    else
      ((icond_code, entrypoint), make_identity_ptree code)
