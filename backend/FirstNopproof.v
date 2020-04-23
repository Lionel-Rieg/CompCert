Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import FirstNop.
Require Import Lia.

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

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function f).(fn_code)!pc = Some i.
Proof.
  intros until i. intro Hcode.
  unfold transf_function; simpl.
  destruct (peq pc (Pos.succ (max_pc_function f))) as [EQ | NEQ].
  { assert (pc <= (max_pc_function f))%positive as LE by (eapply max_pc_function_sound; eassumption).
    subst pc.
    lia.
  }
  rewrite PTree.gso by congruence.
  assumption.
Qed.

Hint Resolve transf_function_at : firstnop.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ |- _ ] =>
        generalize (transf_function_at _ _ _ A); intros
  end.


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

(*
Lemma match_pc_refl : forall f pc, match_pc f pc pc.
Proof.
  unfold match_pc.
  left.
  trivial.
Qed.

Hint Resolve match_pc_refl : firstnop.

Lemma initial_jump:
  forall f,
  (fn_code (transf_function f)) ! (Pos.succ (max_pc_function f)) =
  Some (Inop (fn_entrypoint f)).
Proof.
  intros. unfold transf_function. simpl.
  apply PTree.gss.
Qed.

Hint Resolve initial_jump : firstnop.
 *)

Lemma match_pc_same :
  forall f pc i,
    PTree.get pc (fn_code f) = Some i ->
    PTree.get pc (fn_code (transf_function f)) = Some i.
Proof.
  intros.
  unfold transf_function. simpl.
  rewrite <- H.
  apply PTree.gso.
  pose proof (max_pc_function_sound f pc i H) as LE.
  unfold Ple in LE.
  lia.
Qed.

Hint Resolve match_pc_same : firstnop.


Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 0%nat
  | Callstate _ _ _ _ => 1%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.
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
  eapply forward_simulation_star.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
