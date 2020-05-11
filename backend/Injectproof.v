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
Require Import Memory Registers Op RTL Globalenvs Values Events.
Require Import Inject.
Require Import Lia.

Local Open Scope positive.

Lemma inject_list_preserves:
  forall l prog pc dst pc0,
    pc0 < pc ->
    PTree.get pc0 (snd (inject_list prog pc dst l)) = PTree.get pc0 prog.
Proof.
  induction l; intros; simpl.
  - apply PTree.gso. lia.
  - rewrite IHl by lia.
    apply PTree.gso. lia.
Qed.

Fixpoint pos_add_nat x n :=
  match n with
  | O => x
  | S n' => Pos.succ (pos_add_nat x n')
  end.

Lemma pos_add_nat_increases : forall x n, x <= (pos_add_nat x n).
Proof.
  induction n; simpl; lia.
Qed.

Lemma pos_add_nat_succ : forall n x,
    Pos.succ (pos_add_nat x n) = pos_add_nat (Pos.succ x) n.
Proof.
  induction n; simpl; intros; trivial.
  rewrite IHn.
  reflexivity.
Qed.

Lemma pos_add_nat_monotone : forall x n1 n2,
    (n1 < n2) % nat ->
    (pos_add_nat x n1) < (pos_add_nat x n2).
Proof.
  induction n1; destruct n2; intros.
  - lia.
  - simpl.
    pose proof (pos_add_nat_increases x n2).
    lia.
  - lia.
  - simpl.
    specialize IHn1 with n2.
    lia.
Qed.

Lemma inject_list_increases:
  forall l prog pc dst,
    (fst (inject_list prog pc dst l)) = pos_add_nat pc (S (List.length l)).
Proof.
  induction l; simpl; intros; trivial.
  rewrite IHl.
  simpl.
  rewrite <- pos_add_nat_succ.
  reflexivity.
Qed.

Program Fixpoint bounded_nth
  {T : Type} (k : nat) (l : list T) (BOUND : (k < List.length l)%nat) : T :=
  match k, l with
  | O, h::_ => h
  | (S k'), _::l' => bounded_nth k' l' _
  | _, nil => _
  end.
Obligation 1.
Proof.
  simpl in BOUND.
  lia.
Qed.
Obligation 2.
Proof.
  simpl in BOUND.
  omega.
Qed.

Program Definition bounded_nth_S_statement : Prop :=
  forall (T : Type) (k : nat) (h : T) (l : list T) (BOUND : (k < List.length l)%nat),
    bounded_nth (S k) (h::l) _ = bounded_nth k l BOUND.
Obligation 1.
lia.
Qed.

Lemma bounded_nth_proof_irr :
  forall {T : Type} (k : nat) (l : list T)
         (BOUND1 BOUND2 : (k < List.length l)%nat),
    (bounded_nth k l BOUND1) = (bounded_nth k l BOUND2).
Proof.
  induction k; destruct l; simpl; intros; trivial; omega.
Qed.

Lemma bounded_nth_S : bounded_nth_S_statement.
Proof.
  unfold bounded_nth_S_statement.
  induction k; destruct l; simpl; intros; trivial.
  1, 2: omega.
  apply bounded_nth_proof_irr.
Qed.

Lemma inject_list_injected:
  forall l prog pc dst k (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat pc k) (snd (inject_list prog pc dst l)) =
    Some (inject_instr (bounded_nth k l BOUND) (Pos.succ (pos_add_nat pc k))).
Proof.
  induction l; simpl; intros.
  - omega.
  - simpl.
    destruct k as [ | k]; simpl pos_add_nat.
    + simpl bounded_nth.
      rewrite inject_list_preserves by lia.
      apply PTree.gss.
    + rewrite pos_add_nat_succ.
      erewrite IHl.
      f_equal. f_equal.
      simpl.
      apply bounded_nth_proof_irr.
      Unshelve.
      lia.
Qed.

Lemma inject_list_injected_end:
  forall l prog pc dst,
    PTree.get (pos_add_nat pc (List.length l))
              (snd (inject_list prog pc dst l)) =
    Some (Inop dst).
Proof.
  induction l; simpl; intros.
  - apply PTree.gss.
  - rewrite pos_add_nat_succ.
    apply IHl.
Qed.
    
Lemma inject_at_preserves :
  forall prog pc extra_pc l pc0,
    pc0 < extra_pc ->
    pc0 <> pc ->
    PTree.get pc0 (snd (inject_at prog pc extra_pc l)) = PTree.get pc0 prog.
Proof.
  intros. unfold inject_at.
  destruct (PTree.get pc prog) eqn:GET.
  - rewrite inject_list_preserves; trivial.
    apply PTree.gso; lia.
  - apply inject_list_preserves; trivial.
Qed.

Lemma inject_at_redirects:
  forall prog pc extra_pc l i,
    pc < extra_pc ->
    PTree.get pc prog = Some i ->
    PTree.get pc (snd (inject_at prog pc extra_pc l)) =
    Some (alter_successor i extra_pc).
Proof.
  intros until i. intros BEFORE GET. unfold inject_at.
  rewrite GET.
  rewrite inject_list_preserves by trivial.
  apply PTree.gss.
Qed.

Lemma inject_at_redirects_none:
  forall prog pc extra_pc l,
    pc < extra_pc ->
    PTree.get pc prog = None ->
    PTree.get pc (snd (inject_at prog pc extra_pc l)) = None.
Proof.
  intros until l. intros BEFORE GET. unfold inject_at.
  rewrite GET.
  rewrite inject_list_preserves by trivial.
  assumption.
Qed.

Lemma inject_at_increases:
  forall prog pc extra_pc l,
    (fst (inject_at prog pc extra_pc l)) = pos_add_nat extra_pc (S (List.length l)).  
Proof.
  intros. unfold inject_at.
  destruct (PTree.get pc prog).
  all: apply inject_list_increases.
Qed.

Lemma inject_at_injected:
  forall l prog pc extra_pc k (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat extra_pc k) (snd (inject_at prog pc extra_pc l)) =
    Some (inject_instr (bounded_nth k l BOUND) (Pos.succ (pos_add_nat extra_pc k))).
Proof.
  intros. unfold inject_at.
  destruct (prog ! pc); apply inject_list_injected.
Qed.

Lemma inject_at_injected_end:
  forall l prog pc extra_pc i,
    PTree.get pc prog = Some i ->
    PTree.get (pos_add_nat extra_pc (List.length l))
              (snd (inject_at prog pc extra_pc l)) =
    Some (Inop (successor i)).
Proof.
  intros until i. intro REW. unfold inject_at.
  rewrite REW.
  apply inject_list_injected_end.
Qed.

Lemma pair_expand:
  forall { A B : Type } (p : A*B),
    p = ((fst p), (snd p)).
Proof.
  destruct p; simpl; trivial.
Qed.

Fixpoint inject_l_position extra_pc
         (injections : list (node * (list inj_instr)))
         (k : nat) {struct injections} : node :=
  match injections with
  | nil => extra_pc
  | (pc,l)::l' =>
    match k with
    | O => extra_pc
    | S k' =>
      inject_l_position
        (Pos.succ (pos_add_nat extra_pc (List.length l))) l' k'
    end
  end.

Lemma inject_l_position_increases : forall injections pc k,
    pc <= inject_l_position pc injections k.
Proof.
  induction injections; simpl; intros.
  lia.
  destruct a as [_ l].
  destruct k.
  lia.
  specialize IHinjections with (pc := (Pos.succ (pos_add_nat pc (Datatypes.length l)))) (k := k).
  assert (pc <= (pos_add_nat pc (Datatypes.length l))) by apply pos_add_nat_increases.
  lia.
Qed.
                    
Definition inject_l (prog : code) extra_pc injections :=
  List.fold_left (fun already (injection : node * (list inj_instr)) =>
                    inject_at' already (fst injection) (snd injection))
    injections
    (extra_pc, prog).

Lemma inject_l_preserves :
  forall injections prog extra_pc pc0,
    pc0 < extra_pc ->
    List.forallb (fun injection => if peq (fst injection) pc0 then false else true) injections = true ->
    PTree.get pc0 (snd (inject_l prog extra_pc injections)) = PTree.get pc0 prog.
Proof.
  induction injections;
    intros until pc0; intros BEFORE ALL; simpl; trivial.
  unfold inject_l.
  destruct a as [pc l]. simpl.
  simpl in ALL.
  rewrite andb_true_iff in ALL.
  destruct ALL as [NEQ ALL].
  rewrite pair_expand with (p := inject_at prog pc extra_pc l).
  fold (inject_l (snd (inject_at prog pc extra_pc l))
              (fst (inject_at prog pc extra_pc l))
              injections).
  rewrite IHinjections; trivial.
  - apply inject_at_preserves; trivial.
    destruct (peq pc pc0); congruence.
  - rewrite inject_at_increases.
    pose proof (pos_add_nat_increases extra_pc (S (Datatypes.length l))).
    lia.
Qed.

Lemma nth_error_nil : forall { T : Type} k,
    nth_error (@nil T) k = None.
Proof.
  destruct k; simpl; trivial.
Qed.

Lemma inject_l_injected:
  forall injections prog injnum pc l extra_pc k
         (BELOW : forallb (fun injection => (fst injection) <? extra_pc) injections = true)
         (NUMBER : nth_error injections injnum = Some (pc, l))
         (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat (inject_l_position extra_pc injections injnum) k)
              (snd (inject_l prog extra_pc injections)) =
    Some (inject_instr (bounded_nth k l BOUND)
       (Pos.succ (pos_add_nat (inject_l_position extra_pc injections injnum) k))).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER.
  }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  destruct a as [pc' l'].
  simpl fold_left.
  rewrite pair_expand with (p := inject_at prog pc' extra_pc l').
  progress fold (inject_l (snd (inject_at prog pc' extra_pc l'))
              (fst (inject_at prog pc' extra_pc l'))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - apply inject_at_injected.
    - rewrite inject_at_increases.
      apply pos_add_nat_monotone.
      lia.
    - rewrite forallb_forall.
      rewrite forallb_forall in BELOW2.
      intros loc IN.
      specialize BELOW2 with loc.
      apply BELOW2 in IN.
      destruct peq as [EQ | ]; trivial.
      rewrite EQ in IN.
      rewrite Pos.ltb_lt in IN.
      pose proof (pos_add_nat_increases extra_pc k).
      lia.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (pc := pc); trivial.
  rewrite forallb_forall.
  rewrite forallb_forall in BELOW2.
  intros loc IN.
  specialize BELOW2 with loc.
  apply BELOW2 in IN.
  pose proof (pos_add_nat_increases extra_pc (Datatypes.length l')).
  rewrite Pos.ltb_lt.
  rewrite Pos.ltb_lt in IN.
  lia.
Qed.

Lemma inject_l_injected_end:
  forall injections prog injnum pc i l extra_pc
         (BEFORE : PTree.get pc prog = Some i)
         (DISTINCT : list_norepet (map fst injections))
         (BELOW : forallb (fun injection => (fst injection) <? extra_pc) injections = true)
         (NUMBER : nth_error injections injnum = Some (pc, l)),
    PTree.get (pos_add_nat (inject_l_position extra_pc injections injnum)
                           (List.length l))
              (snd (inject_l prog extra_pc injections)) =
    Some (Inop (successor i)).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER.
  }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  destruct a as [pc' l'].
  simpl fold_left.
  rewrite pair_expand with (p := inject_at prog pc' extra_pc l').
  progress fold (inject_l (snd (inject_at prog pc' extra_pc l'))
              (fst (inject_at prog pc' extra_pc l'))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - apply inject_at_injected_end; trivial.
    - rewrite inject_at_increases.
      apply pos_add_nat_monotone.
      lia.
    - rewrite forallb_forall.
      rewrite forallb_forall in BELOW2.
      intros loc IN.
      specialize BELOW2 with loc.
      apply BELOW2 in IN.
      destruct peq as [EQ | ]; trivial.
      rewrite EQ in IN.
      rewrite Pos.ltb_lt in IN.
      pose proof (pos_add_nat_increases extra_pc (Datatypes.length l)).
      lia.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (pc := pc); trivial.
  {
    rewrite <- BEFORE.
    apply inject_at_preserves.
    {
      apply nth_error_In in NUMBER.
      rewrite forallb_forall in BELOW2.
      specialize BELOW2 with (pc, l).
      apply BELOW2 in NUMBER.
      apply Pos.ltb_lt in NUMBER.
      simpl in NUMBER.
      assumption.
    }
    simpl in DISTINCT.
    inv DISTINCT.
    intro SAME.
    subst pc'.
    apply nth_error_in in NUMBER.
    assert (In (fst (pc, l)) (map fst injections)) as Z.
    { apply in_map. assumption.
    }
    simpl in Z.
    auto.
  }
  { inv DISTINCT.
    assumption.
  }
  {
    rewrite forallb_forall.
    rewrite forallb_forall in BELOW2.
    intros loc IN.
    specialize BELOW2 with loc.
    apply BELOW2 in IN.
    pose proof (pos_add_nat_increases extra_pc (Datatypes.length l')).
    rewrite Pos.ltb_lt.
    rewrite Pos.ltb_lt in IN.
    assert (pos_add_nat extra_pc (Datatypes.length l') <
            pos_add_nat extra_pc (S (Datatypes.length l'))).
    { apply pos_add_nat_monotone.
      lia.
    }
    lia.
  }
Qed.


Lemma inject_l_redirects:
  forall injections prog injnum pc i l extra_pc
         (BEFORE : PTree.get pc prog = Some i)
         (DISTINCT : list_norepet (map fst injections))
         (BELOW : forallb (fun injection => (fst injection) <? extra_pc) injections = true)
         (NUMBER : nth_error injections injnum = Some (pc, l)),
    PTree.get pc (snd (inject_l prog extra_pc injections)) =
    Some (alter_successor i (inject_l_position extra_pc injections injnum)).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER.
  }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  destruct a as [pc' l'].
  simpl fold_left.
  rewrite pair_expand with (p := inject_at prog pc' extra_pc l').
  progress fold (inject_l (snd (inject_at prog pc' extra_pc l'))
              (fst (inject_at prog pc' extra_pc l'))
              injections).
  simpl in BELOW1.
  apply Pos.ltb_lt in BELOW1.
  inv DISTINCT.
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - apply inject_at_redirects; trivial.
    - rewrite inject_at_increases.
      pose proof (pos_add_nat_increases extra_pc (S (Datatypes.length l))).
      lia.
    - rewrite forallb_forall.
      intros loc IN.
      destruct loc as [pc' l'].
      simpl in *.
      destruct peq; trivial.
      subst pc'.
      apply in_map with (f := fst) in IN.
      simpl in IN.
      exfalso.
      auto.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (pc := pc) (l := l); trivial.
  {
    rewrite <- BEFORE.
    apply nth_error_In in NUMBER.
    rewrite forallb_forall in BELOW2.
    specialize BELOW2 with (pc, l).
    simpl in BELOW2.
    rewrite Pos.ltb_lt in BELOW2.
    apply inject_at_preserves; auto.
    assert (In (fst (pc, l)) (map fst injections)) as Z.
    { apply in_map. assumption.
    }
    simpl in Z.
    intro EQ.
    subst pc'.
    auto.
  }
  {
    rewrite forallb_forall.
    rewrite forallb_forall in BELOW2.
    intros loc IN.
    specialize BELOW2 with loc.
    apply BELOW2 in IN.
    pose proof (pos_add_nat_increases extra_pc (Datatypes.length l')).
    rewrite Pos.ltb_lt.
    rewrite Pos.ltb_lt in IN.
    assert (pos_add_nat extra_pc (Datatypes.length l') <
            pos_add_nat extra_pc (S (Datatypes.length l'))).
    { apply pos_add_nat_monotone.
      lia.
    }
    lia.
  }
Qed.

(*
Lemma inject'_preserves :
  forall injections prog extra_pc pc0,
    pc0 < extra_pc ->
    PTree.get pc0 injections = None ->
    PTree.get pc0 (snd (inject' prog extra_pc injections)) = PTree.get pc0 prog.
Proof.
  intros. unfold inject'.
  rewrite PTree.fold_spec.
  change (fold_left
        (fun (a : node * code) (p : positive * list inj_instr) =>
         inject_at' a (fst p) (snd p)) (PTree.elements injections)
        (extra_pc, prog)) with (inject_l prog extra_pc (PTree.elements injections)).
  apply inject_l_preserves; trivial.
  rewrite List.forallb_forall.
  intros injection IN.
  destruct injection as [pc l].
  simpl.
  apply PTree.elements_complete in IN.
  destruct (peq pc pc0); trivial.
  congruence.
Qed.

Lemma inject_preserves :
  forall injections prog extra_pc pc0,
    pc0 < extra_pc ->
    PTree.get pc0 injections = None ->
    PTree.get pc0 (inject prog extra_pc injections) = PTree.get pc0 prog.
Proof.
  unfold inject'.
  apply inject'_preserves.
Qed.
*)

Section INJECTOR.
  Variable gen_injections : function -> node -> reg -> PTree.t (list inj_instr).

  Definition match_prog (p tp: RTL.program) :=
    match_program (fun ctx f tf => transf_fundef gen_injections f = OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transf_program gen_injections p = OK tp -> match_prog p tp.
  Proof.
    intros. eapply match_transform_partial_program; eauto.
  Qed.

  Section PRESERVATION.

    Variables prog tprog: program.
    Hypothesis TRANSF: match_prog prog tprog.
    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Definition match_regs (f : function) (rs rs' : regset) :=
      forall r, r <= max_reg_function f -> (rs'#r = rs#r).

    Lemma match_regs_refl : forall f rs, match_regs f rs rs.
    Proof.
      unfold match_regs. intros. trivial.
    Qed.

    Lemma match_regs_trans : forall f rs1 rs2 rs3,
        match_regs f rs1 rs2 -> match_regs f rs2 rs3 -> match_regs f rs1 rs3.
    Proof.
      unfold match_regs. intros until rs3. intros M12 M23 r.
      specialize M12 with r.
      specialize M23 with r.
      intuition congruence.
    Qed.

    Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
    | match_frames_intro: forall res f tf sp pc pc' rs trs
        (FUN : transf_function gen_injections f = OK tf)
        (REGS : match_regs f rs trs)
        (STAR:
           forall ts m trs1,
           exists trs2,
             (match_regs f trs1 trs2) /\
             Smallstep.star RTL.step tge
                                      (State ts tf sp pc' trs1 m) E0
                                      (State ts tf sp pc trs2 m)),
        match_frames (Stackframe res f sp pc rs)
                     (Stackframe res tf sp pc' trs).

    Inductive match_states: state -> state -> Prop :=
    | match_states_intro:
      forall s f tf sp pc rs trs m ts
        (FUN : transf_function gen_injections f = OK tf)
        (STACKS: list_forall2 match_frames s ts)
        (REGS: match_regs f rs trs),
      match_states (State s f sp pc rs m) (State ts tf sp pc trs m)
    | match_states_call:
        forall s fd tfd args m ts
        (FUN : transf_fundef gen_injections fd = OK tfd)
        (STACKS: list_forall2 match_frames s ts),
          match_states (Callstate s fd args m) (Callstate ts tfd args m)
    | match_states_return:
        forall s res m ts
               (STACKS: list_forall2 match_frames s ts),
          match_states (Returnstate s res m)
                       (Returnstate ts res m).

    Lemma functions_translated:
      forall (v: val) (f: RTL.fundef),
        Genv.find_funct ge v = Some f ->
        exists tf,
          Genv.find_funct tge v = Some tf /\
          transf_fundef gen_injections f = OK tf.
    Proof.
      apply (Genv.find_funct_transf_partial TRANSF).
    Qed.

    Lemma function_ptr_translated:
      forall (b: block) (f: RTL.fundef),
        Genv.find_funct_ptr ge b = Some f ->
        exists tf,
          Genv.find_funct_ptr tge b = Some tf /\
          transf_fundef gen_injections f = OK tf.
    Proof.
      apply (Genv.find_funct_ptr_transf_partial TRANSF).
    Qed.

    Lemma symbols_preserved:
      forall id,
        Genv.find_symbol tge id = Genv.find_symbol ge id.
    Proof.
      apply (Genv.find_symbol_match TRANSF).
    Qed.

    Lemma senv_preserved:
      Senv.equiv ge tge.
    Proof.
      apply (Genv.senv_match TRANSF).
    Qed.

    Lemma sig_preserved:
      forall f tf, transf_fundef gen_injections f = OK tf
                   -> funsig tf = funsig f.
    Proof.
      destruct f; simpl; intros; monadInv H; trivial.
      unfold transf_function in *.
      destruct valid_injections1 in EQ.
      2: discriminate.
      inv EQ.
      reflexivity.
    Qed.

    Lemma stacksize_preserved:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_stacksize tf = fn_stacksize f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma params_preserved:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_params tf = fn_params f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma entrypoint_preserved:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_entrypoint tf = fn_entrypoint f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma sig_preserved2:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_sig tf = fn_sig f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma transf_initial_states:
      forall S1, RTL.initial_state prog S1 ->
                 exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
    Proof.
      intros. inversion H.
      exploit function_ptr_translated; eauto.
      intros (tf & A & B).
      exists (Callstate nil tf nil m0); split.
      - econstructor; eauto.
        + eapply (Genv.init_mem_match TRANSF); eauto.
        + replace (prog_main tprog) with (prog_main prog).
          rewrite symbols_preserved. eauto.
          symmetry. eapply match_program_main; eauto.
        + rewrite <- H3. eapply sig_preserved; eauto.
      - constructor; trivial.
        constructor.
    Qed.

    Lemma transf_final_states:
      forall S1 S2 r, match_states S1 S2 ->
                      final_state S1 r -> final_state S2 r.
    Proof.
      intros. inv H0. inv H. inv STACKS. constructor.
    Qed.

    Lemma assign_above:
      forall f trs res v,
        (max_reg_function f) < res ->
        match_regs f trs trs # res <- v.
    Proof.
      unfold match_regs.
      intros.
      apply Regmap.gso.
      lia.
    Qed.
    
    Lemma transf_function_inj_step:
      forall ts f tf sp pc trs m ii
        (FUN : transf_function gen_injections f = OK tf)
        (GET : (fn_code tf) ! pc = Some (inject_instr ii (Pos.succ pc)))
        (VALID : valid_injection_instr (max_reg_function f) ii = true),
      exists trs',
        RTL.step tge
              (State ts tf sp pc trs m) E0
              (State ts tf sp (Pos.succ pc) trs' m) /\
        match_regs (f : function) trs trs'.
    Proof.
      destruct ii as [ |op args res | chunk addr args res]; simpl; intros.
      - exists trs.
        split.
        * apply exec_Inop; assumption.
        * apply match_regs_refl.
      - repeat rewrite andb_true_iff in VALID.
        rewrite negb_true_iff in VALID.
        destruct VALID as (MAX_REG & NOTRAP & LENGTH).
        rewrite Pos.ltb_lt in MAX_REG.
        rewrite Nat.eqb_eq in LENGTH.
        destruct (eval_operation ge sp op trs ## args m) as [v | ] eqn:EVAL.
        + exists (trs # res <- v).
          split.
          * apply exec_Iop with (op := op) (args := args) (res := res); trivial.
            rewrite eval_operation_preserved with (ge1 := ge).
            assumption.
            exact symbols_preserved.
          * apply assign_above; auto.
        + exfalso.
          generalize EVAL.
          apply is_trapping_op_sound; trivial.
          rewrite map_length.
          assumption.
      - rewrite Pos.ltb_lt in VALID.
        destruct (eval_addressing ge sp addr trs ## args) as [a | ] eqn:ADDR.
        + destruct (Mem.loadv chunk m a) as [v | ] eqn:LOAD.
          * exists (trs # res <- v).
            split.
            ** apply exec_Iload with (trap := NOTRAP) (chunk := chunk) (addr := addr) (args := args) (dst := res) (a := a); trivial.
               all: try rewrite eval_addressing_preserved with (ge1 := ge).
               all: auto using symbols_preserved.
            ** apply assign_above; auto.
          * exists (trs # res <- Vundef).
            split.
            ** apply exec_Iload_notrap2 with (chunk := chunk) (addr := addr) (args := args) (dst := res) (a := a); trivial.
               all: rewrite eval_addressing_preserved with (ge1 := ge).
               all: auto using symbols_preserved.
            ** apply assign_above; auto.
        + exists (trs # res <- Vundef).
          split.
          * apply exec_Iload_notrap1 with (chunk := chunk) (addr := addr) (args := args) (dst := res); trivial.
            all: rewrite eval_addressing_preserved with (ge1 := ge).
            all: auto using symbols_preserved.
          * apply assign_above; auto.
    Qed.

    Lemma bounded_nth_In: forall {T : Type} (l : list T) k LESS,
        In (bounded_nth k l LESS) l.
    Proof.
      induction l; simpl; intros.
      lia.
      destruct k; simpl.
      - left; trivial.
      - right. apply IHl.
    Qed.

    Lemma transf_function_inj_starstep_rec :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n =
               Some (src_pc, inj_code))
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n = inj_pc)
        (k : nat)
        (CUR : (k <= (List.length inj_code))%nat)
        (trs : regset),
      exists trs',
        match_regs (f : function) trs trs' /\
        Smallstep.star RTL.step tge
              (State ts tf sp (pos_add_nat inj_pc
                                    ((List.length inj_code) - k)%nat) trs m) E0
              (State ts tf sp (pos_add_nat inj_pc (List.length inj_code)) trs' m).
    Proof.
      induction k; simpl; intros.
      { rewrite Nat.sub_0_r.
        exists trs.
        split.
        - apply match_regs_refl.
        - constructor.
      }
      assert (k <= Datatypes.length inj_code)%nat as KK by lia.
      pose proof (IHk KK) as IH.
      clear IHk KK.
      pose proof FUN as VALIDATE.
      unfold transf_function, valid_injections1 in VALIDATE.
      destruct forallb eqn:FORALL in VALIDATE.
      2: discriminate.
      injection VALIDATE.
      intro TF.
      symmetry in TF.
      pose proof (inject_l_injected (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) (fn_code f) inj_n src_pc inj_code (Pos.succ (max_pc_function f)) ((List.length inj_code) - (S k))%nat) as INJECTED.
      lapply INJECTED.
      { clear INJECTED.
        intro INJECTED.
        assert ((Datatypes.length inj_code - S k <
                 Datatypes.length inj_code)%nat) as LESS by lia.
        pose proof (INJECTED INJ LESS) as INJ'.
        replace (snd
            (inject_l (fn_code f) (Pos.succ (max_pc_function f))
                      (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))))) with (fn_code tf) in INJ'.
        2: rewrite TF; simpl; reflexivity.                                              apply transf_function_inj_step with (f:=f) (ts:=ts) (sp:=sp) (trs:=trs) (m := m) in INJ'.
        2: assumption.
        {
          destruct INJ' as [trs'' [STEP STEPMATCH]].
          destruct (IH trs'') as [trs' [STARSTEPMATCH STARSTEP]].
          exists trs'.
          split.
          { apply match_regs_trans with (rs2 := trs''); assumption. }
          eapply Smallstep.star_step with (t1:=E0) (t2:=E0).
          {
            rewrite POSITION in STEP.
            exact STEP.
          }
          {
            replace (Datatypes.length inj_code - k)%nat
              with (S (Datatypes.length inj_code - (S k)))%nat in STARSTEP by lia.
            simpl pos_add_nat in STARSTEP.
            exact STARSTEP.
          }
          constructor.
        }
        rewrite forallb_forall in FORALL.
        specialize FORALL with  (src_pc, inj_code).
        lapply FORALL.
        {
          simpl.
          rewrite andb_true_iff.
          intros (SRC & ALL_VALID).
          rewrite forallb_forall in ALL_VALID.
          apply ALL_VALID.
          apply bounded_nth_In.
        }
        apply nth_error_In with (n := inj_n).
        assumption.
      }
      rewrite forallb_forall in FORALL.
      rewrite forallb_forall.
      intros x INx.
      rewrite Pos.ltb_lt.
      pose proof (FORALL x INx) as ALLx.
      rewrite andb_true_iff in ALLx.
      destruct ALLx as [ALLx1 ALLx2].
      rewrite Pos.leb_le in ALLx1.
      lia.
    Qed.
    
    Lemma transf_function_inj_starstep :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n =
               Some (src_pc, inj_code))
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n = inj_pc)
        (trs : regset),
      exists trs',
        match_regs (f : function) trs trs' /\
        Smallstep.star RTL.step tge
              (State ts tf sp inj_pc trs m) E0
              (State ts tf sp (pos_add_nat inj_pc (List.length inj_code)) trs' m).
    Proof.
      intros.
      replace (State ts tf sp inj_pc trs m) with (State ts tf sp (pos_add_nat inj_pc ((List.length inj_code) - (List.length inj_code))%nat) trs m).
      eapply transf_function_inj_starstep_rec; eauto.
      f_equal.
      rewrite <- minus_n_n.
      reflexivity.
    Qed.

    Lemma transf_function_inj_end :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code i
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n =
               Some (src_pc, inj_code))
        (SRC: (fn_code f) ! src_pc = Some i)
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n = inj_pc)
        (trs : regset),
        RTL.step tge
          (State ts tf sp (pos_add_nat inj_pc (List.length inj_code)) trs m) E0
          (State ts tf sp (successor i) trs m).
    Proof.
      intros.
      pose proof FUN as VALIDATE.
      unfold transf_function, valid_injections1 in VALIDATE.
      destruct forallb eqn:FORALL in VALIDATE.
      2: discriminate.
      injection VALIDATE.
      intro TF.
      symmetry in TF.
      pose proof (inject_l_injected_end (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) (fn_code f) inj_n src_pc i inj_code (Pos.succ (max_pc_function f))) as INJECTED.
      lapply INJECTED.
      2: assumption.
      clear INJECTED.
      intro INJECTED.
      lapply INJECTED.
      2: apply (PTree.elements_keys_norepet (gen_injections f (max_pc_function f) (max_reg_function f))); fail.
      clear INJECTED.
      intro INJECTED.
      lapply INJECTED.
      { clear INJECTED.
        intro INJECTED.
        pose proof (INJECTED INJ) as INJ'.
        clear INJECTED.
        replace (snd
                   (inject_l (fn_code f) (Pos.succ (max_pc_function f))
                             (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))))) with (fn_code tf) in INJ'.
        2: rewrite TF; simpl; reflexivity.
        rewrite POSITION in INJ'.
        apply exec_Inop.
        assumption.
      }
      clear INJECTED.
      rewrite forallb_forall in FORALL.
      rewrite forallb_forall.
      intros x INx.
      rewrite Pos.ltb_lt.
      pose proof (FORALL x INx) as ALLx.
      rewrite andb_true_iff in ALLx.
      destruct ALLx as [ALLx1 ALLx2].
      rewrite Pos.leb_le in ALLx1.
      lia.
    Qed.

    Lemma transf_function_inj_plusstep :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code i
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n =
               Some (src_pc, inj_code))
        (SRC: (fn_code f) ! src_pc = Some i)
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) inj_n = inj_pc)
        (trs : regset),
      exists trs',
        match_regs (f : function) trs trs' /\
        Smallstep.plus RTL.step tge
              (State ts tf sp inj_pc trs m) E0
              (State ts tf sp (successor i) trs' m).
    Proof.
      intros.
      destruct (transf_function_inj_starstep ts f tf sp m inj_n src_pc inj_pc inj_code FUN INJ POSITION trs) as [trs' [MATCH PLUS]].
      exists trs'.
      split. assumption.
      eapply Smallstep.plus_right.
      exact PLUS.
      eapply transf_function_inj_end; eassumption.
      reflexivity.
    Qed.
    
    Lemma transf_function_preserves:
      forall f tf pc 
        (FUN : transf_function gen_injections f = OK tf)
        (LESS : pc <= max_pc_function f)
        (NOCHANGE : (gen_injections f (max_pc_function f) (max_reg_function f)) ! pc = None),
        (fn_code tf) ! pc = (fn_code f) ! pc.
    Proof.
      intros.
      unfold transf_function in FUN.
      destruct valid_injections1 in FUN.
      2: discriminate.
      inv FUN.
      simpl.
      apply inject_l_preserves.
      lia.
      rewrite forallb_forall.
      intros x INx.
      destruct peq; trivial.
      subst pc.
      exfalso.
      destruct x as [pc ii].
      simpl in *.
      apply PTree.elements_complete in INx.
      congruence.
    Qed.
    
    Lemma transf_function_redirects:
      forall f tf pc injl ii
        (FUN : transf_function gen_injections f = OK tf)
        (LESS : pc <= max_pc_function f)
        (INJECTION : (gen_injections f (max_pc_function f) (max_reg_function f)) ! pc = Some injl)
        (INSTR: (fn_code f) ! pc = Some ii),
      exists pc' : node,
        (fn_code tf) ! pc = Some (alter_successor ii pc') /\
        (forall ts sp m trs,
            exists trs',
            match_regs f trs trs' /\
            Smallstep.plus RTL.step tge
              (State ts tf sp pc' trs m) E0
              (State ts tf sp (successor ii) trs' m)).        
    Proof.
      intros.
      apply PTree.elements_correct in INJECTION.
      apply In_nth_error in INJECTION.
      destruct INJECTION as [injn INJECTION].
      exists (inject_l_position (Pos.succ (max_pc_function f))
                                (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) injn).
      split.
      { unfold transf_function in FUN.
        destruct (valid_injections1) eqn:VALID in FUN.
        2: discriminate.
        inv FUN.
        simpl.
        apply inject_l_redirects with (l := injl); auto.
        apply PTree.elements_keys_norepet.
        unfold valid_injections1 in VALID.
        rewrite forallb_forall in VALID.
        rewrite forallb_forall.
        intros x INx.
        pose proof (VALID x INx) as VALIDx.
        clear VALID.
        rewrite andb_true_iff in VALIDx.
        rewrite Pos.leb_le in VALIDx.
        destruct VALIDx as [VALIDx1 VALIDx2].
        rewrite Pos.ltb_lt.
        lia.
      }
      intros.
      pose proof (transf_function_inj_plusstep ts f tf sp m injn pc
                 (inject_l_position (Pos.succ (max_pc_function f))
                                    (PTree.elements (gen_injections f (max_pc_function f) (max_reg_function f))) injn)
                 injl ii FUN INJECTION INSTR) as TRANS.
      lapply TRANS.
      2: reflexivity.
      clear TRANS.
      intro TRANS.
      exact (TRANS trs).
    Qed.

    Lemma transf_function_preserves_uses:
      forall f tf pc rs trs ii
        (FUN : transf_function gen_injections f = OK tf)
        (MATCH : match_regs f rs trs)
        (INSTR : (fn_code f) ! pc = Some ii),
        trs ## (instr_uses ii) = rs ## (instr_uses ii).
    Proof.
      intros.
      assert (forall r, In r (instr_uses ii) ->
                        trs # r = rs # r) as SAME.
      {
        intros r INr.
        apply MATCH.
        apply (max_reg_function_use f pc ii); auto.
      }
      induction (instr_uses ii); simpl; trivial.
      f_equal.
      - apply SAME. constructor; trivial.
      - apply IHl. intros.
        apply SAME. right. assumption.
    Qed.

    (*
    Lemma transf_function_preserves_builtin_arg:
      forall rs trs ef res sp m pc'
        (arg : builtin_arg reg)
        (SAME : (forall r,
                    In r (instr_uses (Ibuiltin ef args res pc')) ->
                    trs # r = rs # r) )
        varg
        (EVAL : eval_builtin_arg ge (fun r => rs#r) sp m arg varg),
        eval_builtin_arg ge (fun r => trs#r) sp m arg varg.
    Proof.
     *)
    
    Lemma transf_function_preserves_builtin_args_rec:
      forall rs trs ef res sp m pc'
        (args : list (builtin_arg reg))
        (SAME : (forall r,
                    In r (instr_uses (Ibuiltin ef args res pc')) ->
                       trs # r = rs # r) )
        (vargs : list val)
        (EVAL : eval_builtin_args ge (fun r => rs#r) sp m args vargs),
        eval_builtin_args ge (fun r => trs#r) sp m args vargs.
    Proof.
      unfold eval_builtin_args.
      induction args; intros; inv EVAL.
      - constructor.
      - constructor.
        + induction H1.
          all: try (constructor; auto; fail).
          * rewrite <- SAME.
            apply eval_BA.
            simpl.
            left. reflexivity.
          * constructor.
            ** apply IHeval_builtin_arg1.
               intros r INr.
               apply SAME.
               simpl.
               simpl in INr.
               rewrite in_app in INr.
               rewrite in_app.
               rewrite in_app.
               tauto.
            ** apply IHeval_builtin_arg2.
               intros r INr.
               apply SAME.
               simpl.
               simpl in INr.
               rewrite in_app in INr.
               rewrite in_app.
               rewrite in_app.
               tauto.
          * constructor.
            ** apply IHeval_builtin_arg1.
               intros r INr.
               apply SAME.
               simpl.
               simpl in INr.
               rewrite in_app in INr.
               rewrite in_app.
               rewrite in_app.
               tauto.
            ** apply IHeval_builtin_arg2.
               intros r INr.
               apply SAME.
               simpl.
               simpl in INr.
               rewrite in_app in INr.
               rewrite in_app.
               rewrite in_app.
               tauto.
        + apply IHargs.
          2: assumption.
          intros r INr.
          apply SAME.
          simpl.
          apply in_or_app.
          right.
          exact INr.
    Qed.
    
    Lemma transf_function_preserves_builtin_args:
      forall f tf pc rs trs ef res sp m pc'
        (args : list (builtin_arg reg))
        (FUN : transf_function gen_injections f = OK tf)
        (MATCH : match_regs f rs trs)
        (INSTR : (fn_code f) ! pc = Some (Ibuiltin ef args res pc'))
        (vargs : list val)
        (EVAL : eval_builtin_args ge (fun r => rs#r) sp m args vargs),
        eval_builtin_args ge (fun r => trs#r) sp m args vargs.
    Proof.
      intros.
      apply transf_function_preserves_builtin_args_rec with (rs := rs) (ef := ef) (res := res) (pc' := pc').
      intros r INr.
      apply MATCH.
      apply (max_reg_function_use f pc (Ibuiltin ef args res pc')).
      all: auto.
    Qed.
    
    Lemma match_regs_write:
      forall f rs trs res v
             (MATCH : match_regs f rs trs),
        match_regs f (rs # res <- v) (trs # res <- v).
    Proof.
      intros.
      intros r LESS.
      destruct (peq r res).
      {
        subst r.
        rewrite Regmap.gss.
        symmetry.
        apply Regmap.gss.
      }
      rewrite Regmap.gso.
      rewrite Regmap.gso.
      all: trivial.
      apply MATCH.
      trivial.
    Qed.

    Lemma match_regs_setres:
      forall f res rs trs vres
             (MATCH : match_regs f rs trs),
        match_regs f (regmap_setres res vres rs) (regmap_setres res vres trs).
    Proof.
      induction res; simpl; intros; trivial.
      apply match_regs_write; auto.
    Qed.
    
    Lemma transf_function_preserves_ros:
      forall f tf pc rs trs ros args res fd pc' sig
        (FUN : transf_function gen_injections f = OK tf)
        (MATCH : match_regs f rs trs)
        (INSTR : (fn_code f) ! pc = Some (Icall sig ros args res pc'))
        (FIND : find_function ge ros rs = Some fd),
      exists tfd, find_function tge ros trs = Some tfd
                  /\ transf_fundef gen_injections fd = OK tfd.
    Proof.
      intros; destruct ros as  [r|id].
      - apply functions_translated; auto.
        replace (trs # r) with (hd Vundef (trs ## (instr_uses (Icall sig (inl r) args res pc')))) by reflexivity.
        rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
      - simpl. rewrite symbols_preserved.
        simpl in FIND.
        destruct (Genv.find_symbol ge id); try congruence.
        eapply function_ptr_translated; eauto.
    Qed.

    Lemma transf_function_preserves_ros_tail:
      forall f tf pc rs trs ros args fd sig
        (FUN : transf_function gen_injections f = OK tf)
        (MATCH : match_regs f rs trs)
        (INSTR : (fn_code f) ! pc = Some (Itailcall sig ros args))
        (FIND : find_function ge ros rs = Some fd),
      exists tfd, find_function tge ros trs = Some tfd
                  /\ transf_fundef gen_injections fd = OK tfd.
    Proof.
      intros; destruct ros as  [r|id].
      - apply functions_translated; auto.
        replace (trs # r) with (hd Vundef (trs ## (instr_uses (Itailcall sig (inl r) args)))) by reflexivity.
        rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
      - simpl. rewrite symbols_preserved.
        simpl in FIND.
        destruct (Genv.find_symbol ge id); try congruence.
        eapply function_ptr_translated; eauto.
    Qed.
      
    Theorem transf_step_correct:
      forall s1 t s2, step ge s1 t s2 ->
         forall ts1 (MS: match_states s1 ts1),
         exists ts2, Smallstep.plus step tge ts1 t ts2 /\ match_states s2 ts2.
    Proof.
      induction 1; intros ts1 MS; inv MS; try (inv TRC).
      - (* nop *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m) (trs := trs).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Inop.
               exact ALTER.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** reflexivity.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := trs); assumption.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Inop.
            rewrite transf_function_preserves with (f:=f); eauto.
            eapply max_pc_function_sound; eauto.
          * constructor; trivial.
            
      - (* op *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m)
             (trs := trs # res <- v).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Iop with (op := op) (args := args).
               exact ALTER.
               rewrite eval_operation_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iop op args res pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
                 simpl.
                 eassumption.
               }
               exact symbols_preserved.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** reflexivity.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := trs # res <- v); trivial.
            apply match_regs_write.
            assumption.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Iop with (op := op) (args := args).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** rewrite eval_operation_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iop op args res pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
                 simpl.
                 eassumption.
               }
               exact symbols_preserved.
          * constructor; trivial.
            apply match_regs_write.
            assumption.

      - (* load *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m)
             (trs := trs # dst <- v).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Iload with (trap := trap) (chunk := chunk) (addr := addr) (args := args) (a := a).
               exact ALTER.
               rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iload trap chunk addr args dst pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
               eassumption.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** reflexivity.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := trs # dst <- v); trivial.
            apply match_regs_write.
            assumption.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Iload with (trap := trap) (chunk := chunk) (addr := addr) (args := args) (a := a).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iload trap chunk addr args dst pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
            ** eassumption.
          * constructor; trivial.
            apply match_regs_write.
            assumption.
        
      - (* load notrap1 *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m)
             (trs := trs # dst <- Vundef).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Iload_notrap1 with (chunk := chunk) (addr := addr) (args := args).
               exact ALTER.
               rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iload NOTRAP chunk addr args dst pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** reflexivity.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := trs # dst <- Vundef); trivial.
            apply match_regs_write.
            assumption.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Iload_notrap1 with (chunk := chunk) (addr := addr) (args := args).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iload NOTRAP chunk addr args dst pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
          * constructor; trivial.
            apply match_regs_write.
            assumption.

      - (* load notrap2 *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m)
             (trs := trs # dst <- Vundef).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Iload_notrap2 with (chunk := chunk) (addr := addr) (args := args) (a := a).
               exact ALTER.
               rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iload NOTRAP chunk addr args dst pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
               eassumption.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** reflexivity.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := trs # dst <- Vundef); trivial.
            apply match_regs_write.
            assumption.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Iload_notrap2 with (chunk := chunk) (addr := addr) (args := args) (a := a).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace args with (instr_uses (Iload NOTRAP chunk addr args dst pc')) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
            ** eassumption.
          * constructor; trivial.
            apply match_regs_write.
            assumption.
        
      - (* store *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m') (trs := trs).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Istore with (chunk := chunk) (addr := addr) (args := args) (a := a) (src := src).
               exact ALTER.
               rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace (trs ## args) with (tl (trs ## (instr_uses (Istore chunk addr args src pc')))) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
               replace (trs # src) with (hd Vundef (trs ## (instr_uses (Istore chunk addr args src pc')))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               simpl.
               eassumption.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** reflexivity.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := trs); trivial.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Istore with (chunk := chunk) (addr := addr) (args := args) (a := a) (src := src).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** rewrite eval_addressing_preserved with (ge1 := ge).
               {
                 replace (trs ## args) with (tl (trs ## (instr_uses (Istore chunk addr args src pc')))) by reflexivity.
                 rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               }
               exact symbols_preserved.
            ** replace (trs # src) with (hd Vundef (trs ## (instr_uses (Istore chunk addr args src pc')))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               simpl.
               eassumption.
          * constructor; trivial.
      - (* call *)
        destruct (transf_function_preserves_ros f tf pc rs trs ros args res fd pc' (funsig fd) FUN REGS H H0) as [tfd [TFD1 TFD2]].
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          simpl in ALTER.
          econstructor; split.
          * eapply Smallstep.plus_one.
            apply exec_Icall with (args := args) (sig := (funsig fd)) (ros := ros).
            exact ALTER.
            exact TFD1.
            apply sig_preserved; auto.
          * destruct ros as [r | id].
            ** replace (trs ## args) with (tl (trs ## (instr_uses (Icall (funsig fd) (inl r) args res pc')))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
               constructor; auto.
               constructor; auto.

               intros.
               destruct (SKIP ts0 sp m0 trs1) as [trs2 [MATCH PLUS]].
               exists trs2. split. assumption.
               apply Smallstep.plus_star. exact PLUS.
               
            ** replace (trs ## args) with (trs ## (instr_uses (Icall (funsig fd) (inr id) args res pc'))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
               constructor; auto.
               constructor; auto.

               intros.
               destruct (SKIP ts0 sp m0 trs1) as [trs2 [MATCH PLUS]].
               exists trs2. split. assumption.
               apply Smallstep.plus_star. exact PLUS.
               
        + econstructor; split.
          * eapply Smallstep.plus_one.
            apply exec_Icall with (args := args) (sig := (funsig fd)) (ros := ros).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** exact TFD1.
            ** apply sig_preserved; auto.
          * destruct ros as [r | id].
            ** replace (trs ## args) with (tl (trs ## (instr_uses (Icall (funsig fd) (inl r) args res pc')))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
               constructor; auto.
               constructor; auto.

               intros. exists trs1. split.
               apply match_regs_refl. constructor.
               
            ** replace (trs ## args) with (trs ## (instr_uses (Icall (funsig fd) (inr id) args res pc'))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
               constructor; auto.
               constructor; auto.

               intros. exists trs1. split.
               apply match_regs_refl. constructor.
        
      -  (* tailcall *)
        destruct (transf_function_preserves_ros_tail f tf pc rs trs ros args fd (funsig fd) FUN REGS H H0) as [tfd [TFD1 TFD2]].
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          simpl in ALTER.
          econstructor; split.
          * eapply Smallstep.plus_one.
            apply exec_Itailcall with (args := args) (sig := (funsig fd)) (ros := ros).
            exact ALTER.
            exact TFD1.
            apply sig_preserved; auto.
            rewrite stacksize_preserved with (f:=f) by trivial.
            eassumption.
          * destruct ros as [r | id].
            ** replace (trs ## args) with (tl (trs ## (instr_uses (Itailcall (funsig fd) (inl r) args)))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
            ** replace (trs ## args) with (trs ## (instr_uses (Itailcall (funsig fd) (inr id) args))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
        + econstructor; split.
          * eapply Smallstep.plus_one.
            apply exec_Itailcall with (args := args) (sig := (funsig fd)) (ros := ros).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** exact TFD1.
            ** apply sig_preserved; auto.
            ** rewrite stacksize_preserved with (f:=f) by trivial.
               eassumption.
          * destruct ros as [r | id].
            ** replace (trs ## args) with (tl (trs ## (instr_uses (Itailcall (funsig fd) (inl r) args)))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.
            ** replace (trs ## args) with (trs ## (instr_uses (Itailcall (funsig fd) (inr id) args))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               apply match_states_call; auto.

      - (* builtin *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m')
             (trs := (regmap_setres res vres trs)).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * eapply Smallstep.plus_left.
            ** apply exec_Ibuiltin with (ef := ef) (args := args) (res := res) (vargs := vargs).
               *** exact ALTER.
               *** apply eval_builtin_args_preserved with (ge1 := ge); eauto.
                   exact symbols_preserved.
                   apply transf_function_preserves_builtin_args with (f:=f) (tf:=tf) (pc:=pc) (rs:=rs) (ef:=ef) (res0:=res) (pc':=pc'); auto.
               *** eapply external_call_symbols_preserved; eauto. apply senv_preserved.
            ** apply Smallstep.plus_star.
               exact PLUS.
            ** symmetry. apply E0_right.
          * constructor; trivial.
            apply match_regs_trans with (rs2 := (regmap_setres res vres trs)); trivial.
            apply match_regs_setres.
            assumption.
        + econstructor; split.
          * eapply Smallstep.plus_one.
            apply exec_Ibuiltin with (ef := ef) (args := args) (res := res) (vargs := vargs).
            ** rewrite transf_function_preserves with (f:=f); eauto.
               eapply max_pc_function_sound; eauto.
            ** apply eval_builtin_args_preserved with (ge1 := ge); eauto.
               exact symbols_preserved.
               apply transf_function_preserves_builtin_args with (f:=f) (tf:=tf) (pc:=pc) (rs:=rs) (ef:=ef) (res0:=res) (pc':=pc'); auto.
            ** eapply external_call_symbols_preserved; eauto. apply senv_preserved.
          * constructor; auto.
            apply match_regs_setres.
            assumption.
            
      - (* cond *)
        destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + destruct b eqn:B.
          ++ exploit transf_function_redirects; eauto.
             { eapply max_pc_function_sound; eauto. }
             intros [pc_inj [ALTER SKIP]].
             specialize SKIP with (ts := ts) (sp := sp) (m := m) (trs := trs).
             destruct SKIP as [trs' [MATCH PLUS]].
             econstructor; split.
             * eapply Smallstep.plus_left.
               ** apply exec_Icond with (b := true) (cond := cond) (args := args) (ifso := pc_inj) (ifnot := ifnot) (predb := predb).
                   exact ALTER.
                   replace args with (instr_uses (Icond cond args ifso ifnot predb)) by reflexivity.
                   rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
                   simpl. reflexivity.
               ** apply Smallstep.plus_star.
                  exact PLUS.
               ** reflexivity.
             * simpl. constructor; auto.
               apply match_regs_trans with (rs2:=trs); auto.

          ++ exploit transf_function_redirects; eauto.
             { eapply max_pc_function_sound; eauto. }
             intros [pc_inj [ALTER SKIP]].
             specialize SKIP with (ts := ts) (sp := sp) (m := m) (trs := trs).
             destruct SKIP as [trs' [MATCH PLUS]].
             econstructor; split.
             * eapply Smallstep.plus_one.
               apply exec_Icond with (b := false) (cond := cond) (args := args) (ifso := pc_inj) (ifnot := ifnot) (predb := predb).
               exact ALTER.
               replace args with (instr_uses (Icond cond args ifso ifnot predb)) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               simpl. reflexivity.
             * simpl. constructor; auto.
        + destruct b eqn:B.
          * econstructor; split.
            ** eapply Smallstep.plus_one.
               apply exec_Icond with (b := true) (cond := cond) (args := args) (ifso := ifso) (ifnot := ifnot) (predb := predb).
               *** rewrite transf_function_preserves with (f:=f); eauto.
                   eapply max_pc_function_sound; eauto.
               *** replace args with (instr_uses (Icond cond args ifso ifnot predb)) by reflexivity.
                   rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               *** reflexivity.
            ** constructor; auto.
          *  econstructor; split.
            ** eapply Smallstep.plus_one.
               apply exec_Icond with (b := false) (cond := cond) (args := args) (ifso := ifso) (ifnot := ifnot) (predb := predb).
               *** rewrite transf_function_preserves with (f:=f); eauto.
                   eapply max_pc_function_sound; eauto.
               *** replace args with (instr_uses (Icond cond args ifso ifnot predb)) by reflexivity.
                   rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               *** reflexivity.
            ** constructor; auto.
                       
      - destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := sp) (m := m) (trs := trs).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Ijumptable with (arg := arg) (tbl := tbl) (n := n); trivial.
            replace (trs # arg) with (hd Vundef (trs ## (instr_uses (Ijumptable arg tbl)))) by reflexivity.
            rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
            eassumption.
          * constructor; trivial.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Ijumptable with (arg := arg) (tbl := tbl) (n := n); trivial.
            rewrite transf_function_preserves with (f:=f); eauto.
            eapply max_pc_function_sound; eauto.
            replace (trs # arg) with (hd Vundef (trs ## (instr_uses (Ijumptable arg tbl)))) by reflexivity.
            rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
            eassumption.
          * constructor; trivial.
      - (* return *)
         destruct ((gen_injections f (max_pc_function f) (max_reg_function f)) ! pc) eqn:INJECTION.
        + exploit transf_function_redirects; eauto.
          { eapply max_pc_function_sound; eauto. }
          intros [pc_inj [ALTER SKIP]].
          specialize SKIP with (ts := ts) (sp := (Vptr stk Ptrofs.zero)) (m := m) (trs := trs).
          destruct SKIP as [trs' [MATCH PLUS]].
          econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Ireturn.
            exact ALTER.
            rewrite stacksize_preserved with (f:=f); eassumption.
          * destruct or as [r | ]; simpl.
            ** replace (trs # r) with (hd Vundef (trs ## (instr_uses (Ireturn (Some r))))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               constructor; auto.
            ** constructor; auto.
        + econstructor; split.
          * apply Smallstep.plus_one.
            apply exec_Ireturn.
            rewrite transf_function_preserves with (f:=f); eauto.
            eapply max_pc_function_sound; eauto.
            rewrite stacksize_preserved with (f:=f); eassumption.
          * destruct or as [r | ]; simpl.
            ** replace (trs # r) with (hd Vundef (trs ## (instr_uses (Ireturn (Some r))))) by reflexivity.
               rewrite transf_function_preserves_uses with (f := f) (tf := tf) (pc := pc) (rs := rs); trivial.
               constructor; auto.
            ** constructor; auto.

      - (* internal call *)
        monadInv FUN.
        econstructor; split.
        + apply Smallstep.plus_one.
          apply exec_function_internal.
          rewrite stacksize_preserved with (f:=f) by assumption.
          eassumption.
        + rewrite entrypoint_preserved with (f:=f)(tf:=x) by assumption.
          constructor; auto.
          rewrite params_preserved with (f:=f)(tf:=x) by assumption.
          apply match_regs_refl.
      - (* external call *)
        monadInv FUN.
        econstructor; split.
        + apply Smallstep.plus_one.
          apply exec_function_external.
          eapply external_call_symbols_preserved; eauto. apply senv_preserved.
        + constructor; auto.
        
      - (* return *)
        inv STACKS. inv H1.
        destruct (STAR bl m (trs # res <- vres)) as [trs2 [MATCH' STAR']].
        econstructor; split.
        + eapply Smallstep.plus_left.
          * apply exec_return.
          * exact STAR'.
          * reflexivity.
        + constructor; trivial.
          apply match_regs_trans with (rs2 := (trs # res <- vres)).
          apply match_regs_write.
          assumption.
          assumption.
    Qed.

    Theorem transf_program_correct:
      Smallstep.forward_simulation (semantics prog) (semantics tprog).
    Proof.
      eapply Smallstep.forward_simulation_plus.
      apply senv_preserved.
      eexact transf_initial_states.
      eexact transf_final_states.
      eexact transf_step_correct.
    Qed.
    
End PRESERVATION.
End INJECTOR.
