Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import Profiling.
Require Import Lia.

Local Open Scope positive.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Lemma pair_expand:
  forall { A B : Type } (p : A*B),
    p = ((fst p), (snd p)).
Proof.
  destruct p; simpl; trivial.
Qed.

Lemma inject_profiling_call_preserves:
  forall id body pc extra_pc ifso ifnot pc0,
    pc0 < extra_pc ->
    PTree.get pc0 (snd (inject_profiling_call id body pc extra_pc ifso ifnot)) = PTree.get pc0 body.
Proof.
  intros. simpl.
  rewrite PTree.gso by lia.
  apply PTree.gso.
  lia.
Qed.
    
Lemma inject_at_preserves :
  forall id body pc extra_pc pc0,
    pc0 < extra_pc ->
    pc0 <> pc ->
    PTree.get pc0 (snd (inject_at id body pc extra_pc)) = PTree.get pc0 body.
Proof.
  intros. unfold inject_at.
  destruct (PTree.get pc body) eqn:GET.
  - destruct i.
    all: try (rewrite inject_profiling_call_preserves; trivial; fail).
    rewrite inject_profiling_call_preserves by trivial.
    apply PTree.gso; lia.
  - apply inject_profiling_call_preserves; trivial.
Qed.

Lemma inject_profiling_call_increases:
  forall id body pc extra_pc ifso ifnot,
    fst (inject_profiling_call id body pc extra_pc ifso ifnot) = extra_pc + 2.
Proof.
  intros.
  simpl.
  lia.
Qed.

Lemma inject_at_increases:
  forall id body pc extra_pc,
    (fst (inject_at id body pc extra_pc)) = extra_pc + 2.
Proof.
  intros. unfold inject_at.
  destruct (PTree.get pc body).
  - destruct i; apply inject_profiling_call_increases.
  - apply inject_profiling_call_increases.
Qed.

Lemma inject_l_preserves :
  forall id injections body extra_pc pc0,
    pc0 < extra_pc ->
    List.forallb (fun injection => if peq injection pc0 then false else true) injections = true ->
    PTree.get pc0 (snd (inject_l id body extra_pc injections)) = PTree.get pc0 body.
Proof.
  induction injections;
    intros until pc0; intros BEFORE ALL; simpl; trivial.
  unfold inject_l.
  simpl in ALL.
  rewrite andb_true_iff in ALL.
  destruct ALL as [NEQ ALL].
  simpl.
  rewrite pair_expand with (p := inject_at id body a extra_pc).
  progress fold (inject_l id (snd (inject_at id body a extra_pc))
              (fst (inject_at id body a extra_pc))
              injections).
  rewrite IHinjections; trivial.
  - apply inject_at_preserves; trivial.
    destruct (peq a pc0); congruence.
  - rewrite inject_at_increases.
    lia.
Qed.

Lemma transf_function_at:
  forall f pc i
    (CODE : f.(fn_code)!pc = Some i)
    (INSTR : match i with
             | Icond _ _ _ _ _ => False
             | _ => True
             end),
    (transf_function f).(fn_code)!pc = Some i.
Proof.
  intros.
  unfold transf_function; simpl.
  rewrite inject_l_preserves.
  assumption.
  - pose proof (max_pc_function_sound f pc i CODE) as LE.
    unfold Ple in LE.
    lia.
  - rewrite forallb_forall.
    intros x IN.
    destruct peq; trivial.
    subst x.
    unfold gen_conditions in IN.
    rewrite in_map_iff in IN.
    destruct IN as [[pc' i'] [EQ IN]].
    simpl in EQ.
    subst pc'.
    apply PTree.elements_complete in IN.
    rewrite PTree.gfilter1 in IN.
    rewrite CODE in IN.
    destruct i; try discriminate; contradiction.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
| match_frames_intro: forall res f sp pc rs,
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp pc rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp pc rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef f) args m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Lemma funsig_preserved:
  forall fd,
    funsig (transf_fundef fd) = funsig fd.
Proof.
  destruct fd; simpl; trivial.
Qed.

Hint Resolve symbols_preserved funsig_preserved : profiling.

Lemma step_simulation:
  forall s1 t s2 (STEP : step ge s1 t s2)
  s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.
  - econstructor; split.
    + apply plus_one. apply exec_Inop.
      erewrite transf_function_at; eauto. apply I.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one. apply exec_Iop with (op:=op) (args:=args).
      * erewrite transf_function_at; eauto. apply I.
      * rewrite eval_operation_preserved with (ge1:=ge);
          eauto with profiling.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one. apply exec_Iload with (trap:=trap) (chunk:=chunk)
                                            (addr:=addr) (args:=args) (a:=a).
      erewrite transf_function_at; eauto. apply I.
      rewrite eval_addressing_preserved with (ge1:=ge).
      all: eauto with profiling.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one. apply exec_Iload_notrap1 with (chunk:=chunk)
                                            (addr:=addr) (args:=args).
      erewrite transf_function_at; eauto. apply I.
      rewrite eval_addressing_preserved with (ge1:=ge).
      all: eauto with profiling.
    + constructor; auto.
  -  econstructor; split.
    + apply plus_one. apply exec_Iload_notrap2 with (chunk:=chunk)
                                            (addr:=addr) (args:=args) (a:=a).
      erewrite transf_function_at; eauto. apply I.
      rewrite eval_addressing_preserved with (ge1:=ge).
      all: eauto with profiling.
    + constructor; auto.
  -  econstructor; split.
    + apply plus_one. apply exec_Istore with (chunk:=chunk) (src := src)
                                            (addr:=addr) (args:=args) (a:=a).
      erewrite transf_function_at; eauto. apply I.
      rewrite eval_addressing_preserved with (ge1:=ge).
      all: eauto with profiling.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one. apply exec_Icall with (sig:=(funsig fd)) (ros:=ros).
      erewrite transf_function_at; eauto. apply I.
      apply find_function_translated with (fd := fd).
      all: eauto with profiling.
    + constructor; auto.
      constructor; auto.
      constructor.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inv STACKS. inv H1.
    econstructor; split.
    + apply plus_one. apply exec_return.
    + constructor; auto.
Admitted.

(*
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Inop; eauto with firstnop.
    + constructor; auto with firstnop.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Iop with (v:=v); eauto with firstnop.
      rewrite <- H0.
      apply eval_operation_preserved.
      apply symbols_preserved.
    + constructor; auto with firstnop.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Iload with (v:=v); eauto with firstnop.
      all: rewrite <- H0.
      all: auto using eval_addressing_preserved, symbols_preserved.
    + constructor; auto with firstnop.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Iload_notrap1; eauto with firstnop.
      all: rewrite <- H0;
      apply eval_addressing_preserved;
      apply symbols_preserved.
    + constructor; auto with firstnop.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Iload_notrap2; eauto with firstnop.
      all: rewrite <- H0;
      apply eval_addressing_preserved;
      apply symbols_preserved.
    + constructor; auto with firstnop.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Istore; eauto with firstnop.
      all: rewrite <- H0;
      apply eval_addressing_preserved;
      apply symbols_preserved.
    + constructor; auto with firstnop.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Icall.
      apply match_pc_same. exact H.
      apply find_function_translated.
      exact H0.
      apply sig_preserved.
    + constructor.
      constructor; auto.
      constructor.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Itailcall.
      apply match_pc_same. exact H.
      apply find_function_translated.
      exact H0.
      apply sig_preserved.
      unfold transf_function; simpl.
      eassumption.
    + constructor; auto.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Ibuiltin; eauto with firstnop.
      eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + constructor; auto.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Icond; eauto with firstnop.
    + constructor; auto.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Ijumptable; eauto with firstnop.
    + constructor; auto.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_Ireturn; eauto with firstnop.
    + constructor; auto.
  - left. econstructor. split.
    + eapply plus_two.
      * eapply exec_function_internal; eauto with firstnop.
      * eapply exec_Inop.
        unfold transf_function; simpl.
        rewrite PTree.gss.
        reflexivity.
      * auto.
    + constructor; auto.
  - left. econstructor. split.
    + eapply plus_one. eapply exec_function_external; eauto with firstnop.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + constructor; auto.
  - left.
    inv STACKS. inv H1.
    econstructor; split.
    + eapply plus_one. eapply exec_return; eauto.
    + constructor; auto.
Qed.
 *)

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
    eapply (Genv.init_mem_transf TRANSL); eauto.
    rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
    eapply function_ptr_translated; eauto.
    rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
