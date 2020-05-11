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
  rewrite <- (Pos2Nat.id (Pos.succ (Pos.succ extra_pc))).
  rewrite <- (Pos2Nat.id (extra_pc + 2)).
  rewrite !Pos2Nat.inj_succ.
  rewrite !Pos2Nat.inj_add.
  apply f_equal.
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

Fixpoint inject_l_position extra_pc
         (injections : list node)
         (k : nat) {struct injections} : node :=
  match injections with
  | nil => extra_pc
  | pc::l' =>
    match k with
    | O => extra_pc
    | S k' => inject_l_position (extra_pc + 2) l' k'
    end
  end.

Lemma inject_l_position_increases : forall injections pc k,
    pc <= inject_l_position pc injections k.
Proof.
  induction injections; simpl; intros.
  lia.
  destruct k.
  lia.
  specialize IHinjections with (pc := pc + 2) (k := k).
  lia.
Qed.

Lemma inject_l_injected_pc:
  forall f_id injections cond args ifso ifnot expected body injnum pc extra_pc
         (INSTR : body ! pc = Some  (Icond cond args ifso ifnot expected))
         (BELOW : forallb (fun pc => pc <? extra_pc) injections = true)
         (NOREPET : list_norepet injections)
         (NUMBER : nth_error injections injnum = Some pc),
    PTree.get pc (snd (inject_l f_id body extra_pc injections)) =
    Some (Icond cond args
                (Pos.succ (inject_l_position extra_pc injections injnum))
                (inject_l_position extra_pc injections injnum) expected).
Proof.
  induction injections; simpl; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER. }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  rewrite Pos.ltb_lt in BELOW1.
  unfold inject_l.
  simpl fold_left.
  rewrite pair_expand with (p := inject_at f_id body a extra_pc).
  progress fold (inject_l f_id (snd (inject_at f_id body a extra_pc))
              (fst (inject_at f_id body a extra_pc))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - unfold inject_at.
      rewrite INSTR.
      unfold inject_profiling_call. simpl.
      rewrite PTree.gso by lia.
      rewrite PTree.gso by lia.
      apply PTree.gss.
    - rewrite inject_at_increases.
      lia.
    - inv NOREPET.
      rewrite forallb_forall.
      intros x IN.
      destruct peq as [EQ | ]; trivial.
      subst x.
      contradiction.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (ifso := ifso) (ifnot := ifnot).
  - rewrite inject_at_preserves; trivial.
    + rewrite forallb_forall in BELOW2.
      rewrite <- Pos.ltb_lt.
      apply nth_error_In in NUMBER.
      auto.
    + inv NOREPET.
      intro ZZZ.
      subst a.
      apply nth_error_In in NUMBER.
      auto.

  - rewrite forallb_forall in BELOW2.
    rewrite forallb_forall.
    intros.
    specialize BELOW2 with x.
    rewrite Pos.ltb_lt in *.
    intuition lia.
  - inv NOREPET. trivial.
  - trivial.
Qed.
 
Lemma inject_l_injected0:
  forall f_id  cond args ifso ifnot expected injections body injnum pc extra_pc
         (INSTR : body ! pc = Some  (Icond cond args ifso ifnot expected))
         (BELOW : forallb (fun pc => pc <? extra_pc) injections = true)
         (NOREPET : list_norepet injections)
         (NUMBER : nth_error injections injnum = Some pc),
    PTree.get (inject_l_position extra_pc injections injnum)
              (snd (inject_l f_id body extra_pc injections)) =
    Some (Ibuiltin (EF_profiling (branch_id f_id pc) 0%Z) nil BR_none ifnot).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER. }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  simpl fold_left.
  rewrite pair_expand with (p := inject_at f_id body a extra_pc).
  progress fold (inject_l f_id (snd (inject_at f_id body a extra_pc))
              (fst (inject_at f_id body a extra_pc))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - unfold inject_at.
      rewrite INSTR.
      unfold inject_profiling_call. simpl.
      rewrite PTree.gso by lia.
      apply PTree.gss.
    - rewrite inject_at_increases.
      lia.
    -  rewrite forallb_forall.
      rewrite forallb_forall in BELOW2.
      intros loc IN.
      specialize BELOW2 with loc.
      apply BELOW2 in IN.
      destruct peq as [EQ | ]; trivial.
      rewrite EQ in IN.
      rewrite Pos.ltb_lt in IN.
      lia.
  }
  simpl.
  rewrite inject_at_increases.
  
  apply IHinjections.
  - rewrite inject_at_preserves; trivial.
    + rewrite forallb_forall in BELOW2.
      rewrite <- Pos.ltb_lt.
      apply nth_error_In in NUMBER.
      auto.
    + inv NOREPET.
      intro ZZZ.
      subst a.
      apply nth_error_In in NUMBER.
      auto.

  - rewrite forallb_forall in BELOW2.
    rewrite forallb_forall.
    intros.
    specialize BELOW2 with x.
    rewrite Pos.ltb_lt in *.
    intuition lia.
  - inv NOREPET. trivial.
  - trivial.
Qed.

Lemma inject_l_injected1:
  forall f_id  cond args ifso ifnot expected injections body injnum pc extra_pc
         (INSTR : body ! pc = Some  (Icond cond args ifso ifnot expected))
         (BELOW : forallb (fun pc => pc <? extra_pc) injections = true)
         (NOREPET : list_norepet injections)
         (NUMBER : nth_error injections injnum = Some pc),
    PTree.get (Pos.succ (inject_l_position extra_pc injections injnum))
              (snd (inject_l f_id body extra_pc injections)) =
    Some (Ibuiltin (EF_profiling (branch_id f_id pc) 1%Z) nil BR_none ifso).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER. }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  simpl fold_left.
  rewrite pair_expand with (p := inject_at f_id body a extra_pc).
  progress fold (inject_l f_id (snd (inject_at f_id body a extra_pc))
              (fst (inject_at f_id body a extra_pc))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - unfold inject_at.
      rewrite INSTR.
      unfold inject_profiling_call. simpl.
      apply PTree.gss.
    - rewrite inject_at_increases.
      lia.
    -  rewrite forallb_forall.
      rewrite forallb_forall in BELOW2.
      intros loc IN.
      specialize BELOW2 with loc.
      apply BELOW2 in IN.
      destruct peq as [EQ | ]; trivial.
      rewrite EQ in IN.
      rewrite Pos.ltb_lt in IN.
      lia.
  }
  simpl.
  rewrite inject_at_increases.
  
  apply IHinjections.
  - rewrite inject_at_preserves; trivial.
    + rewrite forallb_forall in BELOW2.
      rewrite <- Pos.ltb_lt.
      apply nth_error_In in NUMBER.
      auto.
    + inv NOREPET.
      intro ZZZ.
      subst a.
      apply nth_error_In in NUMBER.
      auto.

  - rewrite forallb_forall in BELOW2.
    rewrite forallb_forall.
    intros.
    specialize BELOW2 with x.
    rewrite Pos.ltb_lt in *.
    intuition lia.
  - inv NOREPET. trivial.
  - trivial.
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

Lemma stacksize_preserved:
  forall f,
    fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  destruct f; simpl; trivial.
Qed.

Hint Resolve symbols_preserved funsig_preserved external_call_symbols_preserved senv_preserved stacksize_preserved : profiling.

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
  - econstructor; split.
    + apply plus_one. apply exec_Itailcall with (sig:=(funsig fd)) (ros:=ros).
      erewrite transf_function_at; eauto. apply I.
      apply find_function_translated with (fd := fd).
      all: eauto with profiling.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one.
      apply exec_Ibuiltin with (ef:=ef) (args:=args) (vargs:=vargs).
      erewrite transf_function_at; eauto. apply I.
      apply eval_builtin_args_preserved with (ge1:=ge).
      all: eauto with profiling.
    + constructor; auto.
  - destruct b.
    + assert (In pc (gen_conditions (fn_code f))) as IN.
              { unfold gen_conditions.
                rewrite in_map_iff.
                exists (pc,  (Icond cond args ifso ifnot predb)).
                split; simpl; trivial.
                apply PTree.elements_correct.
                rewrite PTree.gfilter1.
                rewrite H.
                reflexivity.
              }
      apply In_nth_error in IN.
      destruct IN as [n IN].
      econstructor; split.
      * eapply plus_two.
        ++ eapply exec_Icond with (cond := cond) (args := args) (predb := predb) (b := true).
           unfold transf_function. simpl.
           erewrite inject_l_injected_pc with (cond := cond) (args := args).
           ** reflexivity.
           ** eassumption.
           ** unfold gen_conditions.
              rewrite forallb_forall.
              intros x INx.
              rewrite in_map_iff in INx.
              destruct INx as [[x' i'] [EQ INx]].
              simpl in EQ.
              subst x'.
              apply PTree.elements_complete in INx.
              rewrite PTree.gfilter1 in INx.
              assert (x <= max_pc_function f) as MAX.
              { destruct ((fn_code f) ! x) eqn:CODEx.
                2: discriminate.
                apply max_pc_function_sound with (i:=i).
                assumption.
              }
              rewrite Pos.ltb_lt.
              lia.
           ** unfold gen_conditions.
              apply PTree.elements_keys_norepet.
           ** exact IN.
           ** assumption.
           ** reflexivity.
        ++ apply exec_Ibuiltin with (ef :=  (EF_profiling (branch_id (function_id f) pc) 1%Z)) (args := nil) (vargs := nil).
           apply inject_l_injected1 with (cond := cond) (args := args) (ifso := ifso) (ifnot := ifnot) (expected := predb).
           ** exact H.
           ** unfold gen_conditions.
              rewrite forallb_forall.
              intros x INx.
              rewrite in_map_iff in INx.
              destruct INx as [[x' i'] [EQ INx]].
              simpl in EQ.
              subst x'.
              apply PTree.elements_complete in INx.
              rewrite PTree.gfilter1 in INx.
              assert (x <= max_pc_function f) as MAX.
              { destruct ((fn_code f) ! x) eqn:CODEx.
                2: discriminate.
                apply max_pc_function_sound with (i:=i).
                assumption.
              }
              rewrite Pos.ltb_lt.
              lia.
           ** unfold gen_conditions.
              apply PTree.elements_keys_norepet.
           ** exact IN.
           ** constructor.
           ** constructor.
        ++ reflexivity.
      * simpl. constructor; auto.
        
    + assert (In pc (gen_conditions (fn_code f))) as IN.
              { unfold gen_conditions.
                rewrite in_map_iff.
                exists (pc,  (Icond cond args ifso ifnot predb)).
                split; simpl; trivial.
                apply PTree.elements_correct.
                rewrite PTree.gfilter1.
                rewrite H.
                reflexivity.
              }
      apply In_nth_error in IN.
      destruct IN as [n IN].
      econstructor; split.
      * eapply plus_two.
        ++ eapply exec_Icond with (cond := cond) (args := args) (predb := predb) (b := false).
           unfold transf_function. simpl.
           erewrite inject_l_injected_pc with (cond := cond) (args := args).
           ** reflexivity.
           ** eassumption.
           ** unfold gen_conditions.
              rewrite forallb_forall.
              intros x INx.
              rewrite in_map_iff in INx.
              destruct INx as [[x' i'] [EQ INx]].
              simpl in EQ.
              subst x'.
              apply PTree.elements_complete in INx.
              rewrite PTree.gfilter1 in INx.
              assert (x <= max_pc_function f) as MAX.
              { destruct ((fn_code f) ! x) eqn:CODEx.
                2: discriminate.
                apply max_pc_function_sound with (i:=i).
                assumption.
              }
              rewrite Pos.ltb_lt.
              lia.
           ** unfold gen_conditions.
              apply PTree.elements_keys_norepet.
           ** exact IN.
           ** assumption.
           ** reflexivity.
        ++ apply exec_Ibuiltin with (ef :=  (EF_profiling (branch_id (function_id f) pc) 0%Z)) (args := nil) (vargs := nil).
           apply inject_l_injected0 with (cond := cond) (args := args) (ifso := ifso) (ifnot := ifnot) (expected := predb).
           ** exact H.
           ** unfold gen_conditions.
              rewrite forallb_forall.
              intros x INx.
              rewrite in_map_iff in INx.
              destruct INx as [[x' i'] [EQ INx]].
              simpl in EQ.
              subst x'.
              apply PTree.elements_complete in INx.
              rewrite PTree.gfilter1 in INx.
              assert (x <= max_pc_function f) as MAX.
              { destruct ((fn_code f) ! x) eqn:CODEx.
                2: discriminate.
                apply max_pc_function_sound with (i:=i).
                assumption.
              }
              rewrite Pos.ltb_lt.
              lia.
           ** unfold gen_conditions.
              apply PTree.elements_keys_norepet.
           ** exact IN.
           ** constructor.
           ** constructor.
        ++ reflexivity.
      * simpl. constructor; auto.
        
  - econstructor; split.
    + apply plus_one.
      apply exec_Ijumptable with (arg:=arg) (tbl:=tbl) (n:=n).
      erewrite transf_function_at; eauto. apply I.
      all: eauto with profiling.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one.
      apply exec_Ireturn.
      erewrite transf_function_at; eauto. apply I.
      rewrite stacksize_preserved. eassumption.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one. apply exec_function_internal.
      rewrite stacksize_preserved. eassumption.
    + constructor; auto.
  - econstructor; split.
    + apply plus_one. apply exec_function_external.
      eauto with profiling.
    + constructor; auto.
  - inv STACKS. inv H1.
    econstructor; split.
    + apply plus_one. apply exec_return.
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
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
