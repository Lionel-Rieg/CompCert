open RTL
open Maps
open Camlcoq

(* TTL : IR emphasizing the preferred next node *)
module TTL = struct
  type instruction =
  | Tleaf of RTL.instruction
  | Tnext of node * RTL.instruction

  type code = instruction PTree.t
end;;

open TTL

(** RTL to TTL *)

let get_some = function
| None -> failwith "Did not get some"
| Some thing -> thing

let bfs code entrypoint =
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
            bfs_list := !bfs_list @ [!node];
            match i with
            | Icall(_, _, _, _, n) -> Queue.add n to_visit
            | Ibuiltin(_, _, _, n) -> Queue.add n to_visit
            | Ijumptable(_, ln) -> List.iter (fun n -> Queue.add n to_visit) ln
            | Itailcall _ | Ireturn _ -> ()
            | Icond (_, _, n1, n2) -> Queue.add n1 to_visit; Queue.add n2 to_visit
            | Inop n | Iop (_, _, _, n) | Iload (_, _, _, _, _, n) | Istore (_, _, _, _, n) -> Queue.add n to_visit
      end
    done;
    !bfs_list
  end

let get_predecessors_rtl code =
  let preds = ref (PTree.map (fun n i -> []) code) in
  let process_inst (node, i) =
    let succ = match i with
      | Inop n | Iop (_,_,_,n) | Iload (_, _,_,_,_,n) | Istore (_,_,_,_,n)
      | Icall (_,_,_,_,n) | Ibuiltin (_, _, _, n) -> [n]
      | Icond (_,_,n1,n2) -> [n1;n2]
      | Ijumptable (_,ln) -> ln
      | Itailcall _ | Ireturn _ -> []
    in List.iter (fun s -> preds := PTree.set s (node::(get_some @@ PTree.get s !preds)) !preds) succ
  in begin
    List.iter process_inst (PTree.elements code);
    !preds
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
    Printf.printf "[";
    f l;
    Printf.printf "]"
  end

let print_intset s =
  let seq = PSet.to_seq s
  in begin
    Printf.printf "{";
    Seq.iter (fun n ->
      Printf.printf "%d " (P.to_int n)
    ) seq;
    Printf.printf "}"
  end

(* FIXME - dominators not working well because the order of dataflow update isn't right *)
  (*
let get_dominators code entrypoint =
  let bfs_order = bfs code entrypoint
  and predecessors = get_predecessors_rtl code
  in let doms = ref (PTree.map (fun n i -> PSet.of_list bfs_order) code)
  in begin
    Printf.printf "BFS: ";
    print_intlist bfs_order;
    Printf.printf "\n";
    List.iter (fun n ->
      let preds = get_some @@ PTree.get n predecessors
      and single = PSet.singleton n
      in match preds with
      | [] -> doms := PTree.set n single !doms
      | p::lp ->
          let set_p = get_some @@ PTree.get p !doms
          and set_lp = List.map (fun p -> get_some @@ PTree.get p !doms) lp
          in let inter = List.fold_left PSet.inter set_p set_lp
          in let union = PSet.union inter single
          in begin
            Printf.printf "----------------------------------------\n";
            Printf.printf "n = %d\n" (P.to_int n);
            Printf.printf "set_p = "; print_intset set_p; Printf.printf "\n";
            Printf.printf "set_lp = ["; List.iter (fun s -> print_intset s; Printf.printf ", ") set_lp; Printf.printf "]\n";
            Printf.printf "=> inter = "; print_intset inter; Printf.printf "\n";
            Printf.printf "=> union = "; print_intset union; Printf.printf "\n";
            doms := PTree.set n union !doms
          end
    ) bfs_order;
    !doms
  end
*)

let print_dominators dominators =
  let domlist = PTree.elements dominators
  in begin
    Printf.printf "{\n";
    List.iter (fun (n, doms) ->
      Printf.printf "\t";
      Printf.printf "%d:" (P.to_int n);
      print_intset doms;
      Printf.printf "\n"
    ) domlist
  end

type vstate = Unvisited | Processed | Visited

(** Getting loop branches with a DFS visit :
  * Each node is either Unvisited, Visited, or Processed
  * pre-order: node becomes Processed
  * post-order: node becomes Visited
  *
  * If we come accross an edge to a Processed node, it's a loop!
  *)
let get_loop_headers code entrypoint =
  let visited = ref (PTree.map (fun n i -> Unvisited) code)
  and is_loop_header = ref (PTree.map (fun n i -> false) code)
  in let rec dfs_visit code = function
  | [] -> ()
  | node :: ln ->
      match (get_some @@ PTree.get node !visited) with
      | Visited -> ()
      | Processed -> begin
          is_loop_header := PTree.set node true !is_loop_header;
          visited := PTree.set node Visited !visited
        end
      | Unvisited -> begin
          visited := PTree.set node Processed !visited;
          match PTree.get node code with
          | None -> failwith "No such node"
          | Some i -> let next_visits = (match i with
            | Icall (_, _, _, _, n) | Ibuiltin (_, _, _, n) | Inop n | Iop (_, _, _, n)
            | Iload (_, _, _, _, _, n) | Istore (_, _, _, _, n) -> [n]
            | Icond (_, _, n1, n2) -> [n1; n2]
            | Itailcall _ | Ireturn _ -> []
            | Ijumptable (_, ln) -> ln
            ) in dfs_visit code next_visits;
          visited := PTree.set node Visited !visited;
          dfs_visit code ln
        end
  in begin
    dfs_visit code [entrypoint];
    !is_loop_header
  end

let ptree_printbool pt =
  let elements = PTree.elements pt
  in begin
    Printf.printf "[";
    List.iter (fun (n, b) ->
      if b then Printf.printf "%d, " (P.to_int n) else ()
    ) elements;
    Printf.printf "]"
  end

(* Looks ahead (until a branch) to see if a node further down verifies
 * the given predicate *)
let rec look_ahead code node is_loop_header predicate =
  if (predicate node) then true
  else match (get_some @@ PTree.get node code) with
    | Ireturn _ | Itailcall _ | Icond _ | Ijumptable _ -> false
    | Inop n | Iop (_, _, _, n) | Iload (_, _, _, _, _, n)
    | Istore (_, _, _, _, n) | Icall (_, _, _, _, n)
    | Ibuiltin (_, _, _, n) ->
      if (get_some @@ PTree.get n is_loop_header) then false
      else look_ahead code n is_loop_header predicate

let get_directions code entrypoint =
  let bfs_order = bfs code entrypoint
  and is_loop_header = get_loop_headers code entrypoint
  and directions = ref (PTree.map (fun n i -> false) code) (* false <=> fallthru *)
  in begin
    Printf.printf "Loop headers: ";
    ptree_printbool is_loop_header;
    Printf.printf "\n";
    List.iter (fun n ->
      match (get_some @@ PTree.get n code) with
      | Icond (cond, lr, n, n') -> directions := PTree.set n (Random.bool ()) !directions
      | _ -> ()
    ) bfs_order;
    !directions
  end

let to_ttl_inst direction = function
| Ireturn o -> Tleaf (Ireturn o)
| Inop n -> Tnext (n, Inop n)
| Iop (op, lr, r, n) -> Tnext (n, Iop(op, lr, r, n))
| Iload (tm, m, a, lr, r, n) -> Tnext (n, Iload(tm, m, a, lr, r, n))
| Istore (m, a, lr, r, n) -> Tnext (n, Istore(m, a, lr, r, n))
| Icall (s, ri, lr, r, n) -> Tleaf (Icall(s, ri, lr, r, n))
| Itailcall (s, ri, lr) -> Tleaf (Itailcall(s, ri, lr))
| Ibuiltin (ef, lbr, br, n) -> Tleaf (Ibuiltin(ef, lbr, br, n))
| Icond (cond, lr, n, n') -> (match direction with
    | false -> Tnext (n', Icond(cond, lr, n, n'))
    | true -> Tnext (n, Icond(cond, lr, n, n')))
| Ijumptable (r, ln) -> Tleaf (Ijumptable(r, ln))

let rec to_ttl_code_rec directions = function
| [] -> PTree.empty
| m::lm -> let (n, i) = m
    in let direction = get_some @@ PTree.get n directions
    in PTree.set n (to_ttl_inst direction i) (to_ttl_code_rec directions lm)

let to_ttl_code code entrypoint =
  let directions = get_directions code entrypoint
  in begin
    Random.init(0); (* using same seed to make it deterministic *)
    to_ttl_code_rec directions (PTree.elements code)
  end

(** Trace selection on TTL *)

let rec exists_false_rec = function
  | [] -> false
  | m::lm -> let (_, b) = m in if b then exists_false_rec lm else true

let exists_false boolmap = exists_false_rec (PTree.elements boolmap)

(* DFS on TTL to guide the exploration *)
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
          | Some ti -> [node] @ match ti with
              | Tleaf i -> (match i with
                  | Icall(_, _, _, _, n) -> dfs_list code [n]
                  | Ibuiltin(_, _, _, n) -> dfs_list code [n]
                  | Ijumptable(_, ln) -> dfs_list code ln
                  | Itailcall _ | Ireturn _ -> [] 
                  | _ -> failwith "Tleaf case not handled in dfs" )
              | Tnext (n,i) -> (dfs_list code [n]) @ match i with
                  | Icond (_, _, n1, n2) -> dfs_list code [n1; n2]
                  | Inop _ | Iop _ | Iload _ | Istore _ -> []
                  | _ -> failwith "Tnext case not handled in dfs"
          end
        else []
      in node_dfs @ (dfs_list code ln)
  in dfs_list code [entrypoint]

let ptree_get_some n ptree = get_some @@ PTree.get n ptree

let get_predecessors_ttl code =
  let preds = ref (PTree.map (fun n i -> []) code) in
  let process_inst (node, ti) = match ti with
  | Tleaf _ -> ()
  | Tnext (_, i) -> let succ = match i with
      | Inop n | Iop (_,_,_,n) | Iload (_, _,_,_,_,n) | Istore (_,_,_,_,n)
      | Icall (_,_,_,_,n) | Ibuiltin (_, _, _, n) -> [n]
      | Icond (_,_,n1,n2) -> [n1;n2]
      | Ijumptable (_,ln) -> ln
      | _ -> []
      in List.iter (fun s -> preds := PTree.set s (node::(get_some @@ PTree.get s !preds)) !preds) succ
  in begin
    List.iter process_inst (PTree.elements code);
    !preds
  end

let rtl_proj code = PTree.map (fun n ti -> match ti with Tleaf i | Tnext(_, i) -> i) code

let rec select_unvisited_node is_visited = function
| [] -> failwith "Empty list"
| n :: ln -> if not (ptree_get_some n is_visited) then n else select_unvisited_node is_visited ln

let best_successor_of node code is_visited =
  match (PTree.get node code) with
  | None -> failwith "No such node in the code"
  | Some ti -> match ti with
      | Tleaf _ -> None
      | Tnext (n,_) -> if not (ptree_get_some n is_visited) then Some n
                       else None

let best_predecessor_of node predecessors order is_visited =
  match (PTree.get node predecessors) with
  | None -> failwith "No predecessor list found"
  | Some lp -> try Some (List.find (fun n -> (List.mem n lp) && (not (ptree_get_some n is_visited))) order)
               with Not_found -> None

(* Algorithm mostly inspired from Chang and Hwu 1988
 * "Trace Selection for Compiling Large C Application Programs to Microcode" *)
let select_traces code entrypoint =
  let order = dfs code entrypoint in
  let predecessors = get_predecessors_ttl code in
  let traces = ref [] in
  let is_visited = ref (PTree.map (fun n i -> false) code) in begin (* mark all nodes visited *)
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
            let s = best_predecessor_of !current predecessors order !is_visited in
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
    Printf.printf "DFS: \t"; print_intlist order; Printf.printf "\n";
    !traces
  end

let print_trace t = print_intlist t

let print_traces traces =
  let rec f = function
  | [] -> ()
  | t::lt -> Printf.printf "\n\t"; print_trace t; Printf.printf ",\n"; f lt
  in begin
    Printf.printf "Traces: {";
    f traces;
    Printf.printf "}\n";
  end

let rec make_identity_ptree_rec = function
| [] -> PTree.empty
| m::lm -> let (n, _) = m in PTree.set n n (make_identity_ptree_rec lm)

let make_identity_ptree f = make_identity_ptree_rec (PTree.elements f.fn_code)

(* For now, identity function *)
let duplicate_aux f =
  let pTreeId = make_identity_ptree f in
  let entrypoint = fn_entrypoint f in
  let traces = select_traces (to_ttl_code (fn_code f) entrypoint) entrypoint
  in begin
    print_traces traces;
    (((fn_code f), (fn_entrypoint f)), pTreeId)
  end
