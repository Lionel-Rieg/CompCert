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

(** Correctness proof for Asmgen *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm Asmgen Machblockgen Asmblockgen.
Require Import Machblockgenproof Asmblockgenproof PostpassSchedulingproof.

Local Open Scope linking_scope.

Definition block_passes :=
      mkpass Machblockgenproof.match_prog
  ::: mkpass Asmblockgenproof.match_prog
  ::: mkpass PostpassSchedulingproof.match_prog
  ::: mkpass Asm.match_prog
  ::: pass_nil _.

Definition match_prog := pass_match (compose_passes block_passes).

Lemma transf_program_match:
  forall p tp, Asmgen.transf_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp H.
  unfold Asmgen.transf_program in H. apply bind_inversion in H. destruct H.
  inversion_clear H. apply bind_inversion in H1. destruct H1.
  inversion_clear H. inversion H2. unfold time, Compopts.time in *. remember (Machblockgen.transf_program p) as mbp.
  unfold match_prog; simpl.
  exists mbp; split. apply Machblockgenproof.transf_program_match; auto.
  exists x; split. apply Asmblockgenproof.transf_program_match; auto.
  exists x0; split. apply PostpassSchedulingproof.transf_program_match; auto.
  exists tp; split. apply Asm.transf_program_match; auto. auto.
Qed.

(** Return Address Offset *)

Definition return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop :=
  Mach_return_address_offset Asmblockgenproof.return_address_offset.

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros; unfold return_address_offset; eapply Mach_return_address_exists; eauto.
  intros; eapply Asmblockgenproof.return_address_exists; eauto.
Qed.


Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  unfold match_prog in TRANSF. simpl in TRANSF.
  inv TRANSF. inv H. inv H1. inv H. inv H2. inv H. inv H3. inv H.
  eapply compose_forward_simulations. 
  exploit Machblockgenproof.transf_program_correct; eauto.
  unfold Machblockgenproof.inv_trans_rao. 
  eapply compose_forward_simulations. apply Asmblockgenproof.transf_program_correct; eauto.
  eapply compose_forward_simulations. apply PostpassSchedulingproof.transf_program_correct; eauto.
  apply Asm.transf_program_correct. eauto.
Qed.

End PRESERVATION.

Instance TransfAsm: TransfLink match_prog := pass_match_link (compose_passes block_passes).

(*******************************************)
(* Stub actually needed by driver/Compiler *)

Module Asmgenproof0.

Definition return_address_offset := return_address_offset.

End Asmgenproof0.
