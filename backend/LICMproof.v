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

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.
Require Import LICM.
Require Injectproof.

Definition match_prog : program -> program -> Prop :=
  Injectproof.match_prog gen_injections.

Section PRESERVATION.

  Variables prog tprog: program.
  Hypothesis TRANSF: match_prog prog tprog.

  Lemma transf_program_match:
    forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
  Proof.
    intros. eapply match_transform_partial_program_contextual; eauto.
  Qed.
  
  Theorem transf_program_correct :
    Smallstep.forward_simulation (semantics prog) (semantics tprog).
  Proof.
    apply Injectproof.transf_program_correct with (gen_injections := gen_injections).
    exact TRANSF.
  Qed.
End PRESERVATION.
