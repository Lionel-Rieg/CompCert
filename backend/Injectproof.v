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
    destruct k as [ | k].
    + admit.
    + simpl pos_add_nat.
      rewrite pos_add_nat_succ.
      erewrite IHl.
      f_equal. f_equal.
      simpl.
      apply bounded_nth_proof_irr.
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

Definition inject_l (prog : code) extra_pc injections :=
  List.fold_left (fun already (injection : node * (list inj_instr)) =>
                    inject_at' already (fst injection) (snd injection))
    injections
    (extra_pc, prog).

Lemma pair_expand:
  forall { A B : Type } (p : A*B),
    p = ((fst p), (snd p)).
Proof.
  destruct p; simpl; trivial.
Qed.

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
