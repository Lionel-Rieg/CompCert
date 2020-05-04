(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*                                                             *)
(*  Copyright VERIMAG. All rights reserved.                    *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

type uid = int

let uid_base = min_int
let next_uid = ref (uid_base+1)

let incr_uid () =
  let r = !next_uid in
  if r = max_int
  then failwith "HashedSet: no more uid"
  else next_uid := succ r;;

let cur_uid () = !next_uid;;

type pset =
  | Empty
  | Node of uid * pset * bool * pset;;

let get_uid = function
  | Empty -> uid_base
  | Node(uid, _, _, _) -> uid;;

module HashedPSet =
  struct
    type t = pset
           
    let hash = function
      | Empty -> 0
      | Node(_, b0, f, b1) -> Hashtbl.hash (get_uid b0, f, get_uid b1);;

    let equal x x' = match x, x' with
      | Empty, Empty -> true
      | Node(_, b0, f, b1), Node(_, b0', f', b1') ->
         b0 == b0' && f == f' && b1 == b1'
      | _, _ -> false
  end;;

module PSetHash = Weak.Make(HashedPSet);;

let htable = PSetHash.create 1000;;

let qnode b0 f b1 =
  let x = Node(cur_uid(), b0, f, b1) in
  match PSetHash.find_opt htable x with
  | None -> PSetHash.add htable x; incr_uid(); x
  | Some y -> y;;

let node (b0, f, b1) = qnode b0 f b1;;

let empty = Empty;;

let pset_match empty_case node_case = function
  | Empty -> empty_case ()
  | Node(_, b0, f, b1) -> node_case b0 f b1;;

let eq (x : pset) (y : pset) = (x==y);;
