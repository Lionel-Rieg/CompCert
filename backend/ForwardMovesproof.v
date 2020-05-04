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

Require Import FunInd.
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import ForwardMoves.


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
  destruct f; trivial.
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
  (transf_function f).(fn_code)!pc =
    Some(transf_instr (forward_map f) pc i).
Proof.
  intros until i. intro CODE.
  unfold transf_function; simpl.
  rewrite PTree.gmap.
  unfold option_map.
  rewrite CODE.
  reflexivity.
Qed.

(*
Definition fmap_sem (fmap : option (PMap.t RB.t)) (pc : node) (rs : regset) :=
  forall x : reg,
    (rs # (subst_arg fmap pc x)) = (rs # x).
 *)

Lemma apply_instr'_bot :
  forall code,
  forall pc,
    RB.eq (apply_instr' code pc RB.bot) RB.bot.
Proof.
  reflexivity.
Qed.

Definition get_rb_sem (rb : RB.t) (rs : regset) :=
  match rb with
  | None => False
  | Some rel =>
    forall x : reg,
      (rs # (get_r rel x)) = (rs # x)
  end.

Lemma get_rb_sem_ge:
  forall rb1 rb2 : RB.t,
    (RB.ge rb1 rb2) ->
    forall rs : regset,
      (get_rb_sem rb2 rs) -> (get_rb_sem rb1 rs).
Proof.
  destruct rb1 as [r1 | ];
    destruct rb2 as [r2 | ];
    unfold get_rb_sem;
    simpl;
    intros GE rs RB2RS;
    try contradiction.
  unfold RELATION.ge in GE.
  unfold get_r in *.
  intro x.
  pose proof (GE x) as GEx.
  pose proof (RB2RS x) as RB2RSx.
  destruct (r1 ! x) as [r1x | ] in *;
    destruct (r2 ! x) as [r2x | ] in *;
    congruence.
Qed.

Definition fmap_sem (fmap : option (PMap.t RB.t))
  (pc : node) (rs : regset) :=
  match fmap with
  | None => True
  | Some m => get_rb_sem (PMap.get pc m) rs
  end.

Lemma subst_arg_ok:
  forall f,
  forall pc,
  forall rs,
  forall arg,
    fmap_sem (forward_map f) pc rs ->
    rs # (subst_arg (forward_map f) pc arg) = rs # arg.
Proof.
  intros until arg.
  intro SEM.
  unfold fmap_sem in SEM.
  destruct (forward_map f) as [map |]in *; trivial.
  simpl.
  unfold get_rb_sem in *.
  destruct (map # pc).
  2: contradiction.
  apply SEM.
Qed.

Lemma subst_args_ok:
  forall f,
  forall pc,
  forall rs,
  fmap_sem (forward_map f) pc rs ->
  forall args,
    rs ## (subst_args (forward_map f) pc args) = rs ## args.
Proof.
  induction args; trivial.
  simpl.
  f_equal.
  apply subst_arg_ok; assumption.
  assumption.
Qed.

Lemma kill_ok:
  forall dst,
  forall mpc,
  forall rs,
  forall v,
    get_rb_sem (Some mpc) rs ->
    get_rb_sem (Some (kill dst mpc)) rs # dst <- v.
Proof.
  unfold get_rb_sem.
  intros until v.
  intros SEM x.
  destruct (Pos.eq_dec x dst) as [EQ | NEQ].
  {
    subst dst.
    rewrite Regmap.gss.
    unfold kill, get_r.
    rewrite PTree.gfilter1.
    rewrite PTree.grs.
    apply Regmap.gss.
  }
  rewrite (Regmap.gso v rs NEQ).
  unfold kill, get_r in *.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by assumption.
  pose proof (SEM x) as SEMx.
  destruct (mpc ! x).
  {
    destruct (Pos.eq_dec dst r).
    {
      subst dst.
      rewrite Regmap.gso by assumption.
      reflexivity.
    }
    rewrite Regmap.gso by congruence.
    assumption.
  }
  rewrite Regmap.gso by assumption.
  reflexivity.
Qed.

Lemma kill_weaken:
  forall dst,
  forall mpc,
  forall rs,
    get_rb_sem (Some mpc) rs ->
    get_rb_sem (Some (kill dst mpc)) rs.
Proof.
  unfold get_rb_sem.
  intros until rs.
  intros SEM x.
  destruct (Pos.eq_dec x dst) as [EQ | NEQ].
  {
    subst dst.
    unfold kill, get_r.
    rewrite PTree.gfilter1.
    rewrite PTree.grs.
    reflexivity.
  }
  unfold kill, get_r in *.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by assumption.
  pose proof (SEM x) as SEMx.
  destruct (mpc ! x).
  {
    destruct (Pos.eq_dec dst r).
    {
      reflexivity.
    }
    assumption.
  }
  reflexivity.
Qed.

Lemma top_ok :
  forall rs, get_rb_sem (Some RELATION.top) rs.
Proof.
  unfold get_rb_sem, RELATION.top.
  intros.
  unfold get_r.
  rewrite PTree.gempty.
  reflexivity.
Qed.

Lemma move_ok:
  forall mpc : RELATION.t,
  forall src res : reg,
  forall rs : regset,
    get_rb_sem (Some mpc) rs ->
    get_rb_sem (Some (move src res mpc)) (rs # res <- (rs # src)).
Proof.
  unfold get_rb_sem, move.
  intros until rs.
  intros SEM x.
  unfold get_r in *.
  destruct (Pos.eq_dec res x).
  {
    subst res.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    pose proof (SEM src) as SEMsrc.
    destruct (mpc ! src) as [mpcsrc | ] in *.
    {
      destruct (Pos.eq_dec x mpcsrc).
      {
        subst mpcsrc.
        rewrite Regmap.gss.
        reflexivity.
      }
      rewrite Regmap.gso by congruence.
      assumption.
    }
    destruct (Pos.eq_dec x src).
    {
      subst src.
      rewrite Regmap.gss.
      reflexivity.
    }
    rewrite Regmap.gso by congruence.
    reflexivity.
  }
  rewrite PTree.gso by congruence.
  rewrite Regmap.gso with (i := x) by congruence.
  unfold kill.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by congruence.
  pose proof (SEM x) as SEMx.
  destruct (mpc ! x) as [ r |].
  {
    destruct (Pos.eq_dec res r).
    {
      subst r.
      rewrite Regmap.gso by congruence.
      trivial.
    }
    rewrite Regmap.gso by congruence.
    assumption.
  }
  rewrite Regmap.gso by congruence.
  reflexivity.
Qed.
  
Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ |- _ ] =>
        generalize (transf_function_at _ _ _ A); intros
  end.

Definition is_killed_in_map (map : PMap.t RB.t) pc res :=
  match PMap.get pc map with
  | None => True
  | Some rel => exists rel', RELATION.ge rel (kill res rel')
  end.

Definition is_killed_in_fmap fmap pc res :=
  match fmap with
  | None => True
  | Some map => is_killed_in_map map pc res
  end.

Definition killed_twice:
  forall rel : RELATION.t,
  forall res,
    RELATION.eq (kill res rel) (kill res (kill res rel)).
Proof.
  unfold kill, RELATION.eq.
  intros.
  rewrite PTree.gfilter1.
  rewrite PTree.gfilter1.
  destruct (Pos.eq_dec res x).
  {
    subst res.
    rewrite PTree.grs.
    rewrite PTree.grs.
    reflexivity.
  }
  rewrite PTree.gro by congruence. 
  rewrite PTree.gro by congruence. 
  rewrite PTree.gfilter1.
  rewrite PTree.gro by congruence.
  destruct (rel ! x) as [relx | ]; trivial.
  destruct (Pos.eq_dec res relx); trivial.
  destruct (Pos.eq_dec res relx); congruence.
Qed.

Lemma get_rb_killed:
  forall mpc,
  forall rs,
  forall rel,
  forall res,
  forall vres,
    (get_rb_sem (Some mpc) rs) ->
    (RELATION.ge mpc (kill res rel)) ->
    (get_rb_sem (Some mpc) rs # res <- vres).
Proof.
  simpl.
  intros until vres.
  intros SEM GE x.
  pose proof (GE x) as GEx.
  pose proof (SEM x) as SEMx.
  unfold get_r in *.
  destruct (mpc ! x) as [mpcx | ] in *; trivial.
  unfold kill in GEx.
  rewrite PTree.gfilter1 in GEx.
  destruct (Pos.eq_dec res x) as [ | res_NE_x].
  {
    subst res.
    rewrite PTree.grs in GEx.
    discriminate.
  }
  rewrite PTree.gro in GEx by congruence.
  rewrite Regmap.gso with (i := x) by congruence.
  destruct (rel ! x) as [relx | ]; try discriminate.
  destruct (Pos.eq_dec res relx) as [ res_EQ_relx | res_NE_relx] in *; try discriminate.
  rewrite Regmap.gso by congruence.
  congruence.
Qed.
  
Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
| match_frames_intro: forall res f sp pc rs,
    (fmap_sem (forward_map f) pc rs) ->
    (is_killed_in_fmap (forward_map f) pc res) ->
      match_frames (Stackframe res f sp pc rs)
                 (Stackframe res (transf_function f) sp pc rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
                                 (STACKS: list_forall2 match_frames stk stk'),
      (fmap_sem (forward_map f) pc rs) ->
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

Lemma op_cases:
  forall op,
  forall args,
  forall dst,
  forall s,
  forall x,
    (exists src, op=Omove /\ args = src :: nil /\
                 (apply_instr (Iop op args dst s) x) = Some (move src dst x))
    \/
    (apply_instr (Iop op args dst s) x) = Some (kill dst x).
Proof.
  destruct op; try (right; simpl; reflexivity).
  destruct args as [| arg0 args0t]; try (right; simpl; reflexivity).
  destruct args0t as [| arg1 args1t]; try (right; simpl; reflexivity).
  left.
  eauto.
Qed.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
              exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try TR_AT.
- (* nop *)
  econstructor; split. eapply exec_Inop; eauto.
  constructor; auto.
  
  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply get_rb_sem_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl. tauto.
  }
  unfold apply_instr'.
  unfold get_rb_sem in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
- (* op *)
  econstructor; split.
  eapply exec_Iop with (v := v); eauto.
  rewrite <- H0.
  rewrite subst_args_ok by assumption.
  apply eval_operation_preserved. exact symbols_preserved.
  constructor; auto.

  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  assert (RB.ge (map # pc') (apply_instr' (fn_code f) pc (map # pc))) as GE.
  {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
  }
  unfold apply_instr' in GE.
  rewrite MPC in GE.
  rewrite H in GE.
  
  destruct (op_cases op args res pc' mpc) as [[src [OP [ARGS MOVE]]] | KILL].
  {
    subst op.
    subst args.
    rewrite MOVE in GE.
    simpl in H0.
    simpl in GE.
    apply get_rb_sem_ge with (rb2 := Some (move src res mpc)).
    assumption.
    replace v with (rs # src) by congruence.
    apply move_ok.
    assumption.
  }
  rewrite KILL in GE.
  apply get_rb_sem_ge with (rb2 := Some (kill res mpc)).
  assumption.
  apply kill_ok.
  assumption.
  
(* load *)
- econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0.
  apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload; eauto.
  rewrite subst_args_ok; assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply get_rb_sem_ge with (rb2 := Some (kill dst mpc)).
  {
    replace (Some (kill dst mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_ok.
  assumption.
  
- (* load notrap1 *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = None).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload_notrap1; eauto.
  rewrite subst_args_ok; assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply get_rb_sem_ge with (rb2 := Some (kill dst mpc)).
  {
    replace (Some (kill dst mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_ok.
  assumption.
  
- (* load notrap2 *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload_notrap2; eauto.
  rewrite subst_args_ok; assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply get_rb_sem_ge with (rb2 := Some (kill dst mpc)).
  {
    replace (Some (kill dst mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_ok.
  assumption.
  
- (* store *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Istore; eauto.
  rewrite subst_args_ok; assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply get_rb_sem_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl. tauto.
  }
  unfold apply_instr'.
  unfold get_rb_sem in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
  
(* call *)
- econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  rewrite subst_args_ok by assumption.
  constructor. constructor; auto. constructor.

  {
  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply get_rb_sem_ge with (rb2 := Some (kill res mpc)).
  {
    replace (Some (kill res mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_weaken.
  assumption.
  }
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  assert (RB.ge (map # pc') (apply_instr' (fn_code f) pc (map # pc))) as GE.
  {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
  }
  unfold apply_instr' in GE.
  unfold fmap_sem in *.
  destruct (map # pc) as [mpc |] in *; try contradiction.
  rewrite H in GE.
  simpl in GE.
  unfold is_killed_in_fmap, is_killed_in_map.
  unfold RB.ge in GE.
  destruct (map # pc') as [mpc'|] eqn:MPC' in *; trivial.
  eauto.
  
(* tailcall *)
- econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  rewrite subst_args_ok by assumption.
  constructor. auto.
  
(* builtin *)
- econstructor; split.
  eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  
  apply get_rb_sem_ge with (rb2 := Some RELATION.top).
  {
    replace (Some RELATION.top) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply top_ok.
  
(* cond *)
- econstructor; split.
  eapply exec_Icond; eauto.
  rewrite subst_args_ok; eassumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply get_rb_sem_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl.
    destruct b; tauto.
  }
  unfold apply_instr'.
  unfold get_rb_sem in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
  
(* jumptbl *)
- econstructor; split.
  eapply exec_Ijumptable; eauto.
  rewrite subst_arg_ok; eassumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply get_rb_sem_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl.
    apply list_nth_z_in with (n := Int.unsigned n).
    assumption.
  }
  unfold apply_instr'.
  unfold get_rb_sem in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
  
(* return *)
- destruct or as [arg | ].
  {
    econstructor; split.
    eapply exec_Ireturn; eauto.
    unfold regmap_optget.
    rewrite subst_arg_ok by eassumption.
    constructor; auto.
  }
    econstructor; split.
    eapply exec_Ireturn; eauto.
    constructor; auto.
  
  
(* internal function *)
-  simpl. econstructor; split.
  eapply exec_function_internal; eauto.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply get_rb_sem_ge with (rb2 := Some RELATION.top).
  {
    eapply DS.fixpoint_entry with (code := fn_code f) (successors := successors_instr); try eassumption.
  }
  apply top_ok.
  
(* external function *)
- econstructor; split.
  eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto.

(* return *)
- inv STACKS. inv H1.
  econstructor; split.
  eapply exec_return; eauto.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  unfold is_killed_in_fmap in H8.
  unfold is_killed_in_map in H8.
  destruct (map # pc) as [mpc |] in *; try contradiction.
  destruct H8 as [rel' RGE].
  eapply get_rb_killed; eauto.
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
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
