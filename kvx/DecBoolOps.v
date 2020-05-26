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

Set Implicit Arguments.

Theorem and_dec : forall A B C D : Prop,
    { A } + { B } -> { C } + { D } ->
    { A /\ C } + { (B /\ C) \/ (B /\ D) \/ (A /\ D) }.
Proof.
  intros A B C D AB CD.
  destruct AB; destruct CD.
  - left. tauto.
  - right. tauto.
  - right. tauto.
  - right. tauto.
Qed.

  
