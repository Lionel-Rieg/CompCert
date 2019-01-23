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

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Machblock Conventions Asmblock.
Require Import Asmblockgenproof0.
Require Import PostpassScheduling.

Local Open Scope error_monad_scope.

Definition match_prog (p tp: Asmblock.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Inductive bblock_equiv (ge: Genv.t fundef unit) (f: function) (bb bb': bblock) :=
  | bblock_equiv_intro:
      (forall rs m,
      exec_bblock ge f bb rs m = exec_bblock ge f bb' rs m) ->
      bblock_equiv ge f bb bb'.

Lemma app_nonil {A: Type} (l l': list A) : l <> nil -> l ++ l' <> nil.
Proof.
  intros. destruct l; simpl.
  - contradiction.
  - discriminate.
Qed.

Lemma app_nonil2 {A: Type} : forall (l': list A) l, l' <> nil -> l ++ l' <> nil.
Proof.
  induction l'; try contradiction.
  intros. cutrewrite (l ++ a :: l' = (l ++ a :: nil) ++ l'). apply app_nonil.
Admitted.

Program Definition concat2 (bb bb': bblock) : res bblock :=
  match (exit bb) with
  | None => 
      match (header bb') with
      | nil => 
          match (exit bb') with 
          | Some (PExpand (Pbuiltin _ _ _)) => Error (msg "PostpassSchedulingproof.concat2: builtin not alone")
          | _ => OK {| header := header bb; body := body bb ++ body bb'; exit := exit bb' |}
          end
      | _ => Error (msg "PostpassSchedulingproof.concat2")
      end
  | _ => Error (msg "PostpassSchedulingproof.concat2")
  end.
Next Obligation.
  apply wf_bblock_refl. constructor.
  - destruct bb' as [hd' bdy' ex' WF']. destruct bb as [hd bdy ex WF]. simpl in *.
    apply wf_bblock_refl in WF'. apply wf_bblock_refl in WF.
    inversion_clear WF'. inversion_clear WF. clear H1 H3.
    inversion H2; inversion H0.
    + left. apply app_nonil. auto.
    + right. auto.
    + left. apply app_nonil2. auto.
    + right. auto.
  - unfold builtin_alone. intros. rewrite H0 in H.
    assert (Some (PExpand (Pbuiltin ef args res)) <> Some (PExpand (Pbuiltin ef args res))).
    apply (H ef args res). contradict H1. auto.
Qed.

Fixpoint concat_all (lbb: list bblock) : res bblock :=
  match lbb with
  | nil => Error (msg "PostpassSchedulingproof.concatenate: empty list")
  | bb::nil => OK bb
  | bb::lbb =>
      do bb' <- concat_all lbb;
      concat2 bb bb'
  end.

Axiom verified_schedule_correct:
  forall ge f bb lbb,
  verified_schedule bb = OK lbb ->
  exists tbb, 
     concat_all lbb = OK tbb
  /\ bblock_equiv ge f bb tbb.

Lemma concat_exec_bblock_nonil (ge: Genv.t fundef unit) (f: function) :
  forall a bb rs m lbb rs'' m'',
  lbb <> nil ->
  concat_all (a :: lbb) = OK bb ->
  exec_bblock ge f bb rs m = Next rs'' m'' ->
  exists bb' rs' m',
       concat_all lbb = OK bb'
    /\ exec_bblock ge f a rs m = Next rs' m'
    /\ rs' PC = Val.offset_ptr (rs PC) (Ptrofs.repr (size a))
    /\ exec_bblock ge f bb' rs' m' = Next rs'' m''.
Proof.
  
Admitted.

Lemma concat_all_size :
  forall a lbb bb bb',
  concat_all (a :: lbb) = OK bb ->
  concat_all lbb = OK bb' ->
  size bb = size a + size bb'.
Proof.
Admitted.

Lemma ptrofs_add_repr :
  forall a b,
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b)) = Ptrofs.unsigned (Ptrofs.repr (a + b)).
Proof.
  intros a b.
  rewrite Ptrofs.add_unsigned. repeat (rewrite Ptrofs.unsigned_repr_eq).
  rewrite <- Zplus_mod. auto.
Qed.

Theorem concat_exec_straight (ge: Genv.t fundef unit) (f: function) :
  forall lbb bb rs m rs' m' c,
  concat_all lbb = OK bb ->
  exec_bblock ge f bb rs m = Next rs' m' ->
  rs' PC = Val.offset_ptr (rs PC) (Ptrofs.repr (size bb)) ->
  exec_straight_blocks ge f (lbb++c) rs m c rs' m'.
Proof.
  induction lbb; try discriminate.
  intros until c. intros CONC EXEB.
  destruct lbb as [| b lbb].
  - simpl in CONC. inv CONC. simpl. econstructor; eauto.
  - exploit concat_exec_bblock_nonil; eauto; try discriminate. 
    intros (bb' & rs0 & m0 & CONC' & EXEB0 & PCeq & EXEB1). intros PCeq'.
    eapply exec_straight_blocks_trans; eauto.
    instantiate (3 := (b :: lbb) ++ c).
    econstructor; eauto.
    eapply IHlbb; eauto.
    rewrite PCeq. rewrite Val.offset_ptr_assoc.
    erewrite concat_all_size in PCeq'; eauto.
Admitted. (* FIXME - attention à l'hypothèse rs' PC qui n'est pas forcément vraie *)

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (size_blocks x.(fn_blocks))); inv EQ0.
  omega.
Qed.

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
  exists lbb,
     verified_schedule bb = OK lbb
  /\ exists c, code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) (lbb ++ c).
Proof.
Admitted.

Lemma transf_exec_bblock:
  forall f tf bb rs m,
  transf_function f = OK tf ->
  exec_bblock ge f bb rs m = exec_bblock tge tf bb rs m.
Proof.
Admitted.

Axiom TODO: False.

Lemma concat_all_equiv_cons:
  forall tge tf bb lbb tbb rs m rs'' m'',
  concat_all (bb::lbb) = OK tbb ->
  exec_bblock tge tf tbb rs m = Next rs'' m'' ->
  exists tbb' rs' m',
     exec_bblock tge tf bb rs m = Next rs' m'
  /\ rs' PC = Val.offset_ptr (rs PC) (Ptrofs.repr (size bb))
  /\ concat_all lbb = OK tbb'
  /\ exec_bblock tge tf tbb' rs' m' = Next rs'' m''.
Proof.
Admitted.

Lemma transf_step_simu:
  forall tf b lbb ofs c tbb rs m rs' m',
  Genv.find_funct_ptr tge b = Some (Internal tf) ->
  size_blocks (fn_blocks tf) <= Ptrofs.max_unsigned ->
  rs PC = Vptr b ofs ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) (lbb ++ c) ->
  concat_all lbb = OK tbb ->
  exec_bblock tge tf tbb rs m = Next rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  induction lbb.
  - intros until m'. simpl. intros. discriminate.
  - intros until m'. intros GFIND SIZE PCeq TAIL CONC EXEB.
    exploit concat_all_equiv_cons; eauto.
    intros (tbb0 & rs0 & m0 & EXEB0 & PCeq' & CONC0 & EXEB1).
    eapply plus_left.
    econstructor.
      3: eapply find_bblock_tail. rewrite <- app_comm_cons in TAIL. 3: eauto.
      all: eauto.
    eapply plus_star. eapply IHlbb; eauto. rewrite PCeq in PCeq'. simpl in PCeq'. all: eauto.
    eapply code_tail_next_int; eauto.
Qed.

Theorem transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus step tge s1' t s2' /\ match_states s2 s2').
Proof.
  induction 1; intros; inv MS.
  - exploit function_ptr_translated; eauto. intros (tf & FFP & TRANSF). monadInv TRANSF.
    exploit transf_find_bblock; eauto. intros (lbb & VES & c & TAIL).
    exploit verified_schedule_correct; eauto. intros (tbb & CONC & BBEQ).
    assert (NOOV: size_blocks x.(fn_blocks) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto. 
    erewrite transf_exec_bblock in H2; eauto.
    inv BBEQ. rewrite H3 in H2.
    exists (State rs' m'). split; try (constructor; auto).
    eapply transf_step_simu; eauto.
  - destruct TODO.
  - destruct TODO.
Admitted.

Theorem transf_program_correct:
  forward_simulation (Asmblock.semantics prog) (Asmblock.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  - apply senv_preserved.
  - apply transf_initial_states.
  - apply transf_final_states.
  - apply transf_step_correct.
Qed.

End PRESERVATION.
