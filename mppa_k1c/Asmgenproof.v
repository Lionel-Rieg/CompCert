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

Local Open Scope linking_scope.

Definition block_passes :=
      mkpass Machblockgenproof.match_prog
  ::: mkpass Asmblockgenproof.match_prog
  ::: mkpass Asm.match_prog
  ::: pass_nil _.

Definition match_prog := pass_match (compose_passes block_passes).

Lemma transf_program_match:
  forall p tp, Asmgen.transf_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp H.
  unfold Asmgen.transf_program in H. apply bind_inversion in H. destruct H.
  inversion_clear H. inversion H1. remember (Machblockgen.transf_program p) as mbp.
  unfold match_prog; simpl.
  exists mbp; split. apply Machblockgenproof.transf_program_match; auto.
  exists x; split. apply Asmblockgenproof.transf_program_match; auto.
  exists tp; split. apply Asm.transf_program_match; auto. auto.
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
  unfold match_prog in TRANSF. simpl in TRANSF.
  inv TRANSF. inv H. inv H1. inv H. inv H2. inv H.
  eapply compose_forward_simulations. apply Machblockgenproof.transf_program_correct; eauto.
  eapply compose_forward_simulations. apply Asmblockgenproof.transf_program_correct; eauto.
  apply Asm.transf_program_correct. eauto.
Qed.

End PRESERVATION.
