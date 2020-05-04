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

type pset
val qnode : pset -> bool -> pset -> pset
val node : pset * bool * pset -> pset
val empty : pset
val pset_match : (unit -> 'a) -> (pset -> bool -> pset -> 'a) -> pset -> 'a
val eq : pset -> pset -> bool
