(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Machblock Conventions Asmblock.
Require Import Asmblockgenproof0 Asmblockprops.
Require Import PostpassScheduling.
Require Import Asmblockgenproof.
Require Import Axioms.

Local Open Scope error_monad_scope.

Definition match_prog (p tp: Asmvliw.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Lemma regset_double_set_id:
  forall r (rs: regset) v1 v2,
  (rs # r <- v1 # r <- v2) = (rs # r <- v2).
Proof.
  intros. apply functional_extensionality. intros. destruct (preg_eq r x).
  - subst r. repeat (rewrite Pregmap.gss; auto).
  - repeat (rewrite Pregmap.gso); auto.
Qed.

Lemma exec_body_pc_var:
  forall l ge rs m rs' m' v,
  exec_body ge l rs m = Next rs' m' ->
  exec_body ge l (rs # PC <- v) m = Next (rs' # PC <- v) m'.
Proof.
  induction l.
  - intros. simpl. simpl in H. inv H. auto.
  - intros. simpl in *.
    destruct (exec_basic_instr ge a rs m) eqn:EXEBI; try discriminate.
    erewrite exec_basic_instr_pc_var; eauto.
Qed.

Lemma pc_set_add:
  forall rs v r x y,
  0 <= x <= Ptrofs.max_unsigned ->
  0 <= y <= Ptrofs.max_unsigned ->
  rs # r <- (Val.offset_ptr v (Ptrofs.repr (x + y))) = rs # r <- (Val.offset_ptr (rs # r <- (Val.offset_ptr v (Ptrofs.repr x)) r) (Ptrofs.repr y)).
Proof.
  intros. apply functional_extensionality. intros r0. destruct (preg_eq r r0).
  - subst. repeat (rewrite Pregmap.gss); auto.
    destruct v; simpl; auto.
    rewrite Ptrofs.add_assoc.
    enough (Ptrofs.repr (x + y) = Ptrofs.add (Ptrofs.repr x) (Ptrofs.repr y)) as ->; auto.
    unfold Ptrofs.add.
    enough (x + y = Ptrofs.unsigned (Ptrofs.repr x) + Ptrofs.unsigned (Ptrofs.repr y)) as ->; auto.
    repeat (rewrite Ptrofs.unsigned_repr); auto.
  - repeat (rewrite Pregmap.gso; auto).
Qed.

Lemma concat2_straight:
  forall a b bb rs m rs'' m'' f ge,
  concat2 a b = OK bb ->
  exec_bblock ge f bb rs m = Next rs'' m'' ->
  exists rs' m',
       exec_bblock ge f a rs m = Next rs' m'
    /\ rs' PC = Val.offset_ptr (rs PC) (Ptrofs.repr (size a))
    /\ exec_bblock ge f b rs' m' = Next rs'' m''.
Proof.
  intros until ge. intros CONC2 EXEB.
  exploit concat2_zlt_size; eauto. intros (LTA & LTB).
  exploit concat2_noexit; eauto. intros EXA.
  exploit concat2_decomp; eauto. intros. inv H.
  unfold exec_bblock in EXEB. destruct (exec_body ge (body bb) rs m) eqn:EXEB'; try discriminate.
  rewrite H0 in EXEB'. apply exec_body_app in EXEB'. destruct EXEB' as (rs1 & m1 & EXEB1 & EXEB2).
  eexists; eexists. split.
    unfold exec_bblock. rewrite EXEB1. rewrite EXA. simpl. eauto.
  split.
    exploit exec_body_pc. eapply EXEB1. intros. rewrite <- H. auto.
    unfold exec_bblock. unfold nextblock, incrPC. rewrite regset_same_assign. erewrite exec_body_pc_var; eauto.
    rewrite <- H1. unfold nextblock in EXEB. rewrite regset_double_set_id.
    assert (size bb = size a + size b).
    { unfold size. rewrite H0. rewrite H1. rewrite app_length. rewrite EXA. simpl. rewrite Nat.add_0_r.
      repeat (rewrite Nat2Z.inj_add). omega. }
    clear EXA H0 H1. rewrite H in EXEB.
    assert (rs1 PC = rs0 PC). { apply exec_body_pc in EXEB2. auto. }
    rewrite H0. rewrite <- pc_set_add; auto.
    exploit size_positive. instantiate (1 := a). intro. omega.
    exploit size_positive. instantiate (1 := b). intro. omega.
Qed.

Lemma concat_all_exec_bblock (ge: Genv.t fundef unit) (f: function) :
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
  intros until m''. intros Hnonil CONC EXEB.
  simpl in CONC.
  destruct lbb as [|b lbb]; try contradiction. clear Hnonil.
  monadInv CONC. exploit concat2_straight; eauto. intros (rs' & m' & EXEB1 & PCeq & EXEB2).
  exists x. repeat econstructor. all: eauto.
Qed.

Lemma ptrofs_add_repr :
  forall a b,
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b)) = Ptrofs.unsigned (Ptrofs.repr (a + b)).
Proof.
  intros a b.
  rewrite Ptrofs.add_unsigned. repeat (rewrite Ptrofs.unsigned_repr_eq).
  rewrite <- Zplus_mod. auto.
Qed.

Section PRESERVATION_ASMBLOCK.

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

Lemma tail_find_bblock:
  forall lbb pos bb,
  find_bblock pos lbb = Some bb ->
  exists c, code_tail pos lbb (bb::c).
Proof.
  induction lbb.
  - intros. simpl in H. inv H.
  - intros. simpl in H.
    destruct (zlt pos 0); try (inv H; fail).
    destruct (zeq pos 0).
    + inv H. exists lbb. constructor; auto.
    + apply IHlbb in H. destruct H as (c & TAIL). exists c.
      enough (pos = pos - size a + size a) as ->.
      apply code_tail_S; auto.
      omega.
Qed.

Lemma code_tail_head_app:
  forall l pos c1 c2,
  code_tail pos c1 c2 ->
  code_tail (pos + size_blocks l) (l++c1) c2.
Proof.
  induction l.
  - intros. simpl. rewrite Z.add_0_r. auto.
  - intros. apply IHl in H. simpl. rewrite (Z.add_comm (size a)). rewrite Z.add_assoc. apply code_tail_S. assumption.
Qed.

Lemma transf_blocks_verified:
  forall c tc pos bb c',
  transf_blocks c = OK tc ->
  code_tail pos c (bb::c') ->
  exists lbb,
     verified_schedule bb = OK lbb
  /\ exists tc', code_tail pos tc (lbb ++ tc').
Proof.
  induction c; intros.
  - simpl in H. inv H. inv H0.
  - inv H0.
    + monadInv H. exists x0.
      split; simpl; auto. eexists; eauto. econstructor; eauto.
    + unfold transf_blocks in H. fold transf_blocks in H. monadInv H.
      exploit IHc; eauto.
      intros (lbb & TRANS & tc' & TAIL).
(*       monadInv TRANS. *)
      repeat eexists; eauto.
      erewrite verified_schedule_size; eauto.
      apply code_tail_head_app.
      eauto.
Qed.

Lemma transf_find_bblock:
  forall ofs f bb tf,
  find_bblock (Ptrofs.unsigned ofs) (fn_blocks f) = Some bb ->
  transf_function f = OK tf ->
  exists lbb,
     verified_schedule bb = OK lbb
  /\ exists c, code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) (lbb ++ c).
Proof.
  intros.
  monadInv H0. destruct (zlt Ptrofs.max_unsigned (size_blocks (fn_blocks x))); try (inv EQ0; fail). inv EQ0.
  monadInv EQ. apply tail_find_bblock in H. destruct H as (c & TAIL).
  eapply transf_blocks_verified; eauto.
Qed.

Lemma symbol_address_preserved:
  forall l ofs, Genv.symbol_address ge l ofs = Genv.symbol_address tge l ofs.
Proof.
  intros. unfold Genv.symbol_address. repeat (rewrite symbols_preserved). reflexivity.
Qed.

Lemma head_tail {A: Type}:
  forall (l: list A) hd, hd::l = hd :: (tail (hd::l)).
Proof.
  intros. simpl. auto.
Qed.

Lemma verified_schedule_not_empty:
  forall bb lbb,
  verified_schedule bb = OK lbb -> lbb <> nil.
Proof.
  intros. apply verified_schedule_size in H.
  pose (size_positive bb). assert (size_blocks lbb > 0) by omega. clear H g.
  destruct lbb; simpl in *; discriminate.
Qed.

Lemma header_nil_label_pos_none:
  forall lbb l p,
  Forall (fun b => header b = nil) lbb -> label_pos l p lbb = None.
Proof.
  induction lbb.
  - intros. simpl. auto.
  - intros. inv H. simpl. unfold is_label. rewrite H2. destruct (in_dec l nil). { inv i. }
    auto.
Qed.

Lemma verified_schedule_label:
  forall bb tbb lbb l,
  verified_schedule bb = OK (tbb :: lbb) ->
     is_label l bb = is_label l tbb
  /\ label_pos l 0 lbb = None.
Proof.
  intros. exploit verified_schedule_header; eauto.
  intros (HdrEq & HdrNil).
  split.
  - unfold is_label. rewrite HdrEq. reflexivity.
  - apply header_nil_label_pos_none. assumption.
Qed.

Lemma label_pos_app_none:
  forall c c' l p p',
  label_pos l p c = None ->
  label_pos l (p' + size_blocks c) c' = label_pos l p' (c ++ c').
Proof.
  induction c.
  - intros. simpl in *. rewrite Z.add_0_r. reflexivity.
  - intros. simpl in *. destruct (is_label _ _) eqn:ISLABEL.
    + discriminate.
    + eapply IHc in H. rewrite Z.add_assoc. eauto.
Qed.

Remark label_pos_pvar_none_add:
  forall tc l p p' k,
  label_pos l (p+k) tc = None -> label_pos l (p'+k) tc = None.
Proof.
  induction tc.
  - intros. simpl. auto.
  - intros. simpl in *. destruct (is_label _ _) eqn:ISLBL.
    + discriminate.
    + pose (IHtc l p p' (k + size a)). repeat (rewrite Z.add_assoc in e). auto.
Qed.

Lemma label_pos_pvar_none:
  forall tc l p p',
  label_pos l p tc = None -> label_pos l p' tc = None.
Proof.
  intros. rewrite (Zplus_0_r_reverse p') at 1. rewrite (Zplus_0_r_reverse p) in H at 1.
  eapply label_pos_pvar_none_add; eauto.
Qed.

Remark label_pos_pvar_some_add_add:
  forall tc l p p' k k',
  label_pos l (p+k') tc = Some (p+k) -> label_pos l (p'+k') tc = Some (p'+k).
Proof.
  induction tc.
  - intros. simpl in H. discriminate.
  - intros. simpl in *. destruct (is_label _ _) eqn:ISLBL.
    + inv H. assert (k = k') by omega. subst. reflexivity.
    + pose (IHtc l p p' k (k' + size a)). repeat (rewrite Z.add_assoc in e). auto.
Qed.

Lemma label_pos_pvar_some_add:
  forall tc l p p' k,
  label_pos l p tc = Some (p+k) -> label_pos l p' tc = Some (p'+k).
Proof.
  intros. rewrite (Zplus_0_r_reverse p') at 1. rewrite (Zplus_0_r_reverse p) in H at 1.
  eapply label_pos_pvar_some_add_add; eauto.
Qed.

Remark label_pos_pvar_add:
  forall c tc l p p' k,
  label_pos l (p+k) c = label_pos l p tc ->
  label_pos l (p'+k) c = label_pos l p' tc.
Proof.
  induction c.
  - intros. simpl in *.
    exploit label_pos_pvar_none; eauto.
  - intros. simpl in *. destruct (is_label _ _) eqn:ISLBL.
    + exploit label_pos_pvar_some_add; eauto.
    + pose (IHc tc l p p' (k+size a)). repeat (rewrite Z.add_assoc in e). auto.
Qed.

Lemma label_pos_pvar:
  forall c tc l p p',
  label_pos l p c = label_pos l p tc ->
  label_pos l p' c = label_pos l p' tc.
Proof.
  intros. rewrite (Zplus_0_r_reverse p') at 1. rewrite (Zplus_0_r_reverse p) in H at 1.
  eapply label_pos_pvar_add; eauto.
Qed.

Lemma label_pos_head_app:
  forall c bb lbb l tc p,
  verified_schedule bb = OK lbb ->
  label_pos l p c = label_pos l p tc ->
  label_pos l p (bb :: c) = label_pos l p (lbb ++ tc).
Proof.
  intros. simpl. destruct lbb as [|tbb lbb].
  - apply verified_schedule_not_empty in H. contradiction.
  - simpl. exploit verified_schedule_label; eauto. intros (ISLBL & LBLPOS).
    rewrite ISLBL.
    destruct (is_label l tbb) eqn:ISLBL'; simpl; auto.
    eapply label_pos_pvar in H0. erewrite H0.
    erewrite verified_schedule_size; eauto. simpl size_blocks. rewrite Z.add_assoc.
    erewrite label_pos_app_none; eauto.
Qed.

Lemma label_pos_preserved:
  forall c tc l,
  transf_blocks c = OK tc -> label_pos l 0 c = label_pos l 0 tc.
Proof.
  induction c.
  - intros. simpl in *. inv H. reflexivity.
  - intros. unfold transf_blocks in H; fold transf_blocks in H. monadInv H. eapply IHc in EQ.
    eapply label_pos_head_app; eauto.
Qed.

Lemma label_pos_preserved_blocks:
  forall l f tf,
  transf_function f = OK tf ->
  label_pos l 0 (fn_blocks f) = label_pos l 0 (fn_blocks tf).
Proof.
  intros. monadInv H. monadInv EQ.
  destruct (zlt Ptrofs.max_unsigned _); try discriminate.
  monadInv EQ0. simpl. eapply label_pos_preserved; eauto.
Qed.

Lemma transf_exec_control:
  forall f tf ex rs m,
  transf_function f = OK tf ->
  exec_control ge f ex rs m = exec_control tge tf ex rs m.
Proof.
  intros. destruct ex; simpl; auto.
  assert (ge = Genv.globalenv prog). auto.
  assert (tge = Genv.globalenv tprog). auto.
  pose symbol_address_preserved.
  exploreInst; simpl; auto; try congruence;
    unfold par_goto_label; unfold par_eval_branch; unfold par_goto_label; erewrite label_pos_preserved_blocks; eauto.
Qed.

Lemma transf_exec_basic_instr:
  forall i rs m, exec_basic_instr ge i rs m = exec_basic_instr tge i rs m.
Proof.
  intros. pose symbol_address_preserved.
  unfold exec_basic_instr. unfold bstep. exploreInst; simpl; auto; try congruence.
  unfold parexec_arith_instr; unfold arith_eval_r; exploreInst; simpl; auto; try congruence.
Qed.

Lemma transf_exec_body:
  forall bdy rs m, exec_body ge bdy rs m = exec_body tge bdy rs m.
Proof.
  induction bdy; intros.
  - simpl. reflexivity.
  - simpl. rewrite transf_exec_basic_instr.
    destruct (exec_basic_instr _ _ _); auto.
Qed.

Lemma transf_exec_bblock:
  forall f tf bb rs m,
  transf_function f = OK tf ->
  exec_bblock ge f bb rs m = exec_bblock tge tf bb rs m.
Proof.
  intros. unfold exec_bblock. rewrite transf_exec_body. destruct (exec_body _ _ _ _); auto.
  eapply transf_exec_control; eauto.
Qed.

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
    destruct lbb.
    + simpl in *. clear IHlbb. inv CONC. eapply plus_one. econstructor; eauto. eapply find_bblock_tail; eauto.
    + exploit concat_all_exec_bblock; eauto; try discriminate.
    intros (tbb0 & rs0 & m0 & CONC0 & EXEB0 & PCeq' & EXEB1).
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
    exploit verified_schedule_correct; eauto. intros (tbb & CONC & BBEQ). inv CONC. rename H3 into CONC.
    assert (NOOV: size_blocks x.(fn_blocks) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto. 

    erewrite transf_exec_bblock in H2; eauto.
    unfold bblock_simu in BBEQ. rewrite BBEQ in H2; try congruence.
    exists (State rs' m'). split; try (constructor; auto).
    eapply transf_step_simu; eauto.

  - exploit function_ptr_translated; eauto. intros (tf & FFP & TRANSF). monadInv TRANSF.
    exploit transf_find_bblock; eauto. intros (lbb & VES & c & TAIL).
    exploit verified_schedule_builtin_idem; eauto. intros. subst lbb.

    remember (State (nextblock _ _) _) as s'. exists s'.
    split; try constructor; auto.
    eapply plus_one. subst s'.
    eapply exec_step_builtin.
      3: eapply find_bblock_tail. simpl in TAIL. 3: eauto.
      all: eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved. eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.

  - exploit function_ptr_translated; eauto. intros (tf & FFP & TRANSF). monadInv TRANSF.
    remember (State _ m') as s'. exists s'. split; try constructor; auto.
    subst s'. eapply plus_one. eapply exec_step_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
Qed.

Theorem transf_program_correct_Asmblock: 
  forward_simulation (Asmblock.semantics prog) (Asmblock.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  - apply senv_preserved.
  - apply transf_initial_states.
  - apply transf_final_states.
  - apply transf_step_correct.
Qed.

End PRESERVATION_ASMBLOCK.

Require Import Asmvliw.

Lemma verified_par_checks_alls_bundles lb x: forall bundle,
  verify_par lb = OK x ->
  List.In bundle lb -> verify_par_bblock bundle = OK tt.
Proof.
  induction lb; simpl; try tauto.
  intros bundle H; monadInv H.
  destruct 1; subst; eauto.
  destruct x0; auto.
Qed.

Lemma verified_schedule_nob_checks_alls_bundles bb lb bundle:
  verified_schedule_nob bb = OK lb ->
  List.In bundle lb -> verify_par_bblock bundle = OK tt.
Proof.
  unfold verified_schedule_nob. intros H;
  monadInv H. destruct x4.
  intros; eapply verified_par_checks_alls_bundles; eauto.
Qed.

Lemma verify_par_bblock_PExpand bb i:
  exit bb = Some (PExpand i) -> verify_par_bblock bb = OK tt.
Proof.
  destruct bb as [h bdy ext H]; simpl.
  intros; subst. destruct i.
  generalize H.
  rewrite <- wf_bblock_refl in H.
  destruct H as [H H0].
  unfold builtin_alone in H0. erewrite H0; eauto.
Qed.

Local Hint Resolve verified_schedule_nob_checks_alls_bundles: core.

Lemma verified_schedule_checks_alls_bundles bb lb bundle:
  verified_schedule bb = OK lb ->
  List.In bundle lb -> verify_par_bblock bundle = OK tt.
Proof.
  unfold verified_schedule. remember (exit bb) as exb.
  destruct exb as [c|]; eauto.
  destruct c as [i|]; eauto.
  destruct i; intros H. inversion_clear H; simpl.
  intuition subst.
  intros; eapply verify_par_bblock_PExpand; eauto.
Qed.

Lemma transf_blocks_checks_all_bundles lbb: forall lb bundle,
  transf_blocks lbb = OK lb ->
  List.In bundle lb -> verify_par_bblock bundle = OK tt.
Proof.
  induction lbb; simpl.
  - intros lb bundle H; inversion_clear H. simpl; try tauto.
  - intros lb bundle H0.
    monadInv H0.
    rewrite in_app. destruct 1; eauto.
    eapply verified_schedule_checks_alls_bundles; eauto.
Qed.

Lemma find_bblock_Some_in lb: 
  forall ofs b, find_bblock ofs lb = Some b -> List.In b lb.
Proof.
  induction lb; simpl; try congruence.
  intros ofs b.
  destruct (zlt ofs 0); try congruence.
  destruct (zeq ofs 0); eauto.
  intros X; inversion X; eauto.
Qed.

Section PRESERVATION_ASMVLIW.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma all_bundles_are_checked b ofs f bundle:
  Genv.find_funct_ptr (globalenv (Asmblock.semantics tprog)) b = Some (Internal f) ->
  find_bblock ofs (fn_blocks f) = Some bundle ->
  verify_par_bblock bundle = OK tt. 
Proof.
  unfold match_prog, match_program in TRANSL.
  unfold Genv.find_funct_ptr; simpl; intros X.
  destruct (Genv.find_def_match_2 TRANSL b) as [|f0 y H]; try congruence.
  destruct y as [tf0|]; try congruence.
  inversion X as [H1]. subst. clear X.
  remember (@Gfun fundef unit (Internal f)) as f2.
  destruct H as [ctx' f1 f2 H0|]; try congruence.
  inversion Heqf2 as [H2]. subst; clear Heqf2.
  unfold transf_fundef, transf_partial_fundef in H.
  destruct f1 as [f1|f1]; try congruence.
  unfold transf_function, transl_function in H.
  monadInv H. monadInv EQ.
  destruct (zlt Ptrofs.max_unsigned (size_blocks (fn_blocks _))); simpl in *|-; try congruence.
  injection EQ1; intros; subst.
  monadInv EQ0. simpl in * |-.
  intros; exploit transf_blocks_checks_all_bundles; eauto.
  intros; eapply find_bblock_Some_in; eauto.
Qed.

Lemma checked_bundles_are_parexec_equiv f bundle rs rs' m m':
  exec_bblock (globalenv (Asmblock.semantics tprog)) f bundle rs m = Next rs' m' ->
  verify_par_bblock bundle = OK tt ->
  det_parexec (globalenv (semantics tprog)) f bundle rs m rs' m'.
Proof.
  intros. unfold verify_par_bblock in H0. destruct (Asmblockdeps.bblock_para_check _) eqn:BPC; try discriminate. clear H0.
  simpl in H.
  eapply Asmblockdeps.bblock_para_check_correct; eauto.
Qed.

Lemma seqexec_parexec_equiv b ofs f bundle rs rs' m m':
  Genv.find_funct_ptr (globalenv (Asmblock.semantics tprog)) b = Some (Internal f) ->
  find_bblock (Ptrofs.unsigned ofs) (fn_blocks f) = Some bundle ->
  exec_bblock (globalenv (Asmblock.semantics tprog)) f bundle rs m = Next rs' m' ->
  det_parexec (globalenv (semantics tprog)) f bundle rs m rs' m'.
Proof.
  intros; eapply checked_bundles_are_parexec_equiv; eauto.
  eapply all_bundles_are_checked; eauto.
Qed.

Theorem transf_program_correct_Asmvliw: 
  forward_simulation (Asmblock.semantics tprog) (Asmvliw.semantics tprog).
Proof.
  eapply forward_simulation_step with (match_states:=fun (s1:Asmvliw.state) s2 => s1=s2); eauto.
  - intros; subst; auto.
  - intros s1 t s1' H s2 H0; subst; inversion H; clear H; subst; eexists; split; eauto.
    + eapply exec_step_internal; eauto.
      intros; eapply seqexec_parexec_equiv; eauto.
    + eapply exec_step_builtin; eauto.
    + eapply exec_step_external; eauto.
Qed.

End PRESERVATION_ASMVLIW.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Theorem transf_program_correct: 
  forward_simulation (Asmblock.semantics prog) (Asmvliw.semantics tprog).
Proof.
  eapply compose_forward_simulations.
  eapply transf_program_correct_Asmblock; eauto.
  eapply transf_program_correct_Asmvliw; eauto.
Qed.

End PRESERVATION.
