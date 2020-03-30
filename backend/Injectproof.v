Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.
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
  lia.
Qed.

Program Definition bounded_nth_S_statement : Prop :=
  forall {T : Type} (k : nat) (h : T) (l : list T) (BOUND : (k < List.length l)%nat),
    bounded_nth (S k) (h::l) _ = bounded_nth k l BOUND.
Obligation 1.
lia.
Qed.

Lemma bounded_nth_proof_irr :
  forall {T : Type} (k : nat) (l : list T)
         (BOUND1 BOUND2 : (k < List.length l)%nat),
    (bounded_nth k l BOUND1) = (bounded_nth k l BOUND2).
Proof.
  induction k; destruct l; simpl; intros; trivial; lia.
Qed.

Lemma bounded_nth_S : bounded_nth_S_statement.
Proof.
  unfold bounded_nth_S_statement.
  induction k; destruct l; simpl; intros; trivial.
  1, 2: lia.
  apply bounded_nth_proof_irr.
Qed.

Lemma inject_list_injected:
  forall l prog pc dst k (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat pc k) (snd (inject_list prog pc dst l)) =
    Some (inject_instr (bounded_nth k l BOUND) (Pos.succ (pos_add_nat pc k))).
Proof.
  induction l; simpl; intros.
  - lia.
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

Definition inject_l (prog : code) extra_pc injections :=
  List.fold_left (fun already (injection : node * (list inj_instr)) =>
                    inject_at' already (fst injection) (snd injection))
    injections
    (extra_pc, prog).

(*
Lemma inject_l_position_ok:
  forall injections prog extra_pc,
    (fst (inject_l prog extra_pc injections)) =
    inject_l_position extra_pc injections.
Proof.
  induction injections; intros; simpl; trivial.
  destruct a as [pc l].
  unfold inject_l. simpl.
  rewrite (pair_expand (inject_at prog pc extra_pc l)).
  fold (inject_l (snd (inject_at prog pc extra_pc l)) (fst (inject_at prog pc extra_pc l)) injections).
  rewrite IHinjections.
  f_equal.
  rewrite inject_at_increases.
  reflexivity.
Qed.
*)
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
