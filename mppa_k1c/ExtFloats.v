(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           Xavier Leroy       INRIA Paris-Rocquencourt       *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

Require Import Floats Integers ZArith.

Module ExtFloat.
(** TODO check with the actual K1c;
    this is what happens on x86 and may be inappropriate. *)

Definition min (x : float) (y : float) : float :=
  match Float.compare x y with
  | Some Eq | Some Lt => x
  | Some Gt | None => y
  end.

Definition max (x : float) (y : float) : float :=
  match Float.compare x y with
  | Some Eq | Some Gt => x
  | Some Lt | None => y
  end.
End ExtFloat.

Module ExtFloat32.
(** TODO check with the actual K1c *)

Definition min (x : float32) (y : float32) : float32 :=
  match Float32.compare x y with
  | Some Eq | Some Lt => x
  | Some Gt | None => y
  end.

Definition max (x : float32) (y : float32) : float32 :=
  match Float32.compare x y with
  | Some Eq | Some Gt => x
  | Some Lt | None => y
  end.

Definition one := Float32.of_int (Int.repr (1%Z)).
Definition inv (x : float32) : float32 :=
  Float32.div one x.

End ExtFloat32.
