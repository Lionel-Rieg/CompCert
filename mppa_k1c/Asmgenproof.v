(* *********************************************************************)
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

(** Correctness proof for RISC-V generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm Asmgen Machblockgen Asmblockgen.
Require Import Machblockgenproof Asmblockgenproof.

(* Local Open Scope linking_scope.

Definition block_passes :=
      mkpass Machblockgenproof.match_prog
  ::: mkpass Asmblockgenproof.match_prog
  ::: mkpass Asm.match_prog
  ::: pass_nil _.
 *)

Inductive match_prog : Mach.program -> Asm.program -> Prop :=
  | mk_match_prog: forall p mbp abp tp,
      Machblockgen.transf_program p = mbp -> Machblockgenproof.match_prog p mbp ->
      Asmblockgen.transf_program mbp = OK abp -> Asmblockgenproof.match_prog mbp abp ->
      Asm.match_prog abp tp ->
      match_prog p tp.

Lemma transf_program_match:
  forall p tp, Asmgen.transf_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp H.
  unfold Asmgen.transf_program in H. apply bind_inversion in H. destruct H.
  inversion_clear H. inversion_clear H1. remember (Machblockgen.transf_program p) as mbp.
  constructor 1 with (mbp:=mbp) (abp:=x); auto.
  subst. apply Machblockgenproof.transf_program_match.
  apply Asmblockgenproof.transf_program_match. auto.
  apply Asm.transf_program_match. auto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics (inv_trans_rao return_address_offset) prog) (Asm.semantics tprog).
Proof.
  inv TRANSF.
  eapply compose_forward_simulations. apply Machblockgenproof.transf_program_correct; eauto.
  eapply compose_forward_simulations. apply Asmblockgenproof.transf_program_correct; eauto.
  apply Asm.transf_program_correct. eauto.
Qed.

End PRESERVATION.
