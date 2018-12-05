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

(** Correctness proof for the [Debugvar] pass. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Machblock Conventions Asmblock.
Require Import PostpassScheduling.

(** * Relational characterization of the transformation *)

Definition match_prog (p tp: Asmblock.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Inductive transf_block_spec (ge: Genv.t fundef unit) (f: function) (bb tbb: bblock) :=
  | transf_block_spec_intro:
      (forall rs m,
      exec_bblock ge f bb rs m = exec_bblock ge f tbb rs m) ->
      transf_block_spec ge f bb tbb.

Axiom transf_block_inv:
  forall ge f bb tbb,
  transf_block bb = OK tbb -> transf_block_spec ge f bb tbb.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit function_ptr_translated; eauto.
  intros (tf' & A & B). monadInv B. rewrite H0 in EQ. inv EQ. auto.
Qed.

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s1 s2, s1 = s2 -> match_states s1 s2.

Lemma prog_main_preserved:
  prog_main tprog = prog_main prog.
Proof (match_program_main TRANSL).

Lemma prog_main_address_preserved:
  (Genv.symbol_address (Genv.globalenv prog) (prog_main prog) Ptrofs.zero) =
  (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero).
Proof.
  unfold Genv.symbol_address. rewrite symbols_preserved.
  rewrite prog_main_preserved. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  econstructor; split.
  - eapply initial_state_intro.
    eapply (Genv.init_mem_transf_partial TRANSL); eauto.
  - econstructor; eauto. subst ge0. subst rs0. rewrite prog_main_address_preserved. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. econstructor; eauto.
Qed.

Lemma transf_find_bblock:
  forall ofs f bb tf,
  find_bblock (Ptrofs.unsigned ofs) (fn_blocks f) = Some bb ->
  transf_function f = OK tf ->
  exists tbb,
    find_bblock (Ptrofs.unsigned ofs) (fn_blocks tf) = Some tbb
    /\ transf_block bb = OK tbb.
Proof.
Admitted.

Lemma transf_exec_bblock:
  forall f tf bb rs m rs' m',
  exec_bblock ge f bb rs m = Next rs' m' ->
  transf_function f = OK tf ->
  exec_bblock tge tf bb rs m = Next rs' m'.
Proof.
Admitted.

Axiom TODO: False.

Theorem transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step tge s1' t s2' /\ match_states s2 s2').
Proof.
  induction 1; intros; inv MS.
  - exploit function_ptr_translated; eauto. intros (tf & A & B). monadInv B.
    exploit transf_find_bblock; eauto. intros (tbb & C & D).
    exists (State rs' m'); split; try (constructor; auto).
    econstructor; eauto.
    exploit transf_block_inv; eauto. intros E. inv E.
    erewrite <- H3.
    eapply transf_exec_bblock; eauto.
  - destruct TODO.
  - destruct TODO.
Admitted.

Theorem transf_program_correct:
  forward_simulation (Asmblock.semantics prog) (Asmblock.semantics tprog).
Proof.
  eapply forward_simulation_step.
  - apply senv_preserved.
  - apply transf_initial_states.
  - apply transf_final_states.
  - apply transf_step_correct.
Qed.

End PRESERVATION.
