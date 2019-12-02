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

(* FIXME - for now, random choice *)

let select_one n n' = if Random.bool () then n else n'

let to_ttl_inst = function
| Ireturn o -> Tleaf (Ireturn o)
| Inop n -> Tnext (n, Inop n)
| Iop (op, lr, r, n) -> Tnext (n, Iop(op, lr, r, n))
| Iload (m, a, lr, r, n) -> Tnext (n, Iload(m, a, lr, r, n))
| Istore (m, a, lr, r, n) -> Tnext (n, Istore(m, a, lr, r, n))
| Icall (s, ri, lr, r, n) -> Tnext (n, Icall(s, ri, lr, r, n))
| Itailcall (s, ri, lr) -> Tleaf (Itailcall(s, ri, lr))
| Ibuiltin (ef, lbr, br, n) -> Tnext (n, Ibuiltin(ef, lbr, br, n))
| Icond (cond, lr, n, n') -> Tnext (select_one n n', Icond(cond, lr, n, n'))
| Ijumptable (r, ln) -> Tnext (List.hd ln, Ijumptable(r, ln))

let rec to_ttl_code_rec = function
| [] -> PTree.empty
| m::lm -> let (n, i) = m in PTree.set n (to_ttl_inst i) (to_ttl_code_rec lm)

let to_ttl_code code = begin
  Random.init(0); (* using same seed to make it deterministic *)
  to_ttl_code_rec (PTree.elements code)
end

(** Trace selection on TTL *)

let rec exists_false_rec = function
  | [] -> false
  | m::lm -> let (_, b) = m in if b then exists_false_rec lm else true

let exists_false boolmap = exists_false_rec (PTree.elements boolmap)

let get_some = function
| None -> failwith "Did not get some"
| Some thing -> thing

(* FIXME - heuristic : starting from entrypoint, then going downward *)
let bfs code entrypoint =
  let visited = ref (PTree.map (fun n i -> false) code) in
  let rec bfs_list code = function
  | [] -> []
  | node :: ln ->
      let node_bfs =
        if not (get_some @@ PTree.get node !visited) then begin
          visited := PTree.set node true !visited;
          match PTree.get node code with
          | None -> failwith "No such node"
          | Some ti -> [node] @ match ti with
              | Tleaf i -> []
              | Tnext (n,i) -> (bfs_list code [n]) @ match i with
                  | Icond (_, _, n1, n2) -> bfs_list code [n1; n2]
                  | Ijumptable (_, ln) -> bfs_list code ln
                  | _ -> []
          end
        else []
      in node_bfs @ (bfs_list code ln)
  in bfs_list code [entrypoint]

let ptree_get_some n ptree = get_some @@ PTree.get n ptree

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

let get_predecessors code =
  let preds = ref (PTree.map (fun n i -> []) code) in
  let process_inst (node, ti) = match ti with
  | Tleaf _ -> ()
  | Tnext (_, i) -> let succ = match i with
      | Inop n | Iop (_,_,_,n) | Iload (_,_,_,_,n) | Istore (_,_,_,_,n)
      | Icall (_,_,_,_,n) | Ibuiltin (_, _, _, n) -> [n]
      | Icond (_,_,n1,n2) -> [n1;n2]
      | Ijumptable (_,ln) -> ln
      | _ -> []
      in List.iter (fun s -> preds := PTree.set s (node::(get_some @@ PTree.get s !preds)) !preds) succ
  in begin
    List.iter process_inst (PTree.elements code);
    !preds
  end

(* Algorithm mostly inspired from Chang and Hwu 1988
 * "Trace Selection for Compiling Large C Application Programs to Microcode" *)
let select_traces code entrypoint =
  let order = bfs code entrypoint in
  let predecessors = get_predecessors code in
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
    !traces
  end

(* for debugging *)
let print_trace trace =
  let rec f = function
  | [] -> ()
  | n::ln -> (Printf.printf "%d " (P.to_int n); f ln)
  in begin
    Printf.printf "[";
    f trace;
    Printf.printf "]"
  end

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

let make_identity_ptree f = make_identity_ptree_rec (PTree.elements (fn_code f))

(* For now, identity function *)
let duplicate_aux f =
  let pTreeId = make_identity_ptree f in
  let traces = select_traces (to_ttl_code @@ fn_code f) (fn_entrypoint f)
  in begin
    print_traces traces;
    (((fn_code f), (fn_entrypoint f)), pTreeId)
  end
