Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps CSE2deps.
Require Import HashedSet.

Module RELATION <: SEMILATTICE_WITHOUT_BOTTOM.
  Definition t := PSet.t.
  Definition eq (x : t) (y : t) := x = y.
  
  Lemma eq_refl: forall x, eq x x.
  Proof.
    unfold eq. trivial.
  Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. congruence.
  Qed.

  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. congruence.
  Qed.
  
  Definition beq (x y : t) := if PSet.eq x y then true else false.
  
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq.
    intros.
    destruct PSet.eq; congruence.
  Qed.
  
  Definition ge (x y : t) := (PSet.is_subset x y) = true.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge.
    intros.
    subst y.
    apply PSet.is_subset_spec.
    trivial.
  Qed.
  
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge.
    intros.
    rewrite PSet.is_subset_spec in *.
    intuition.
  Qed.
  
  Definition lub := PSet.inter.
  
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge, lub.
    intros.
    apply PSet.is_subset_spec.
    intro.
    rewrite PSet.ginter.
    rewrite andb_true_iff.
    intuition.
  Qed.
  
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge, lub.
    intros.
    apply PSet.is_subset_spec.
    intro.
    rewrite PSet.ginter.
    rewrite andb_true_iff.
    intuition.
  Qed.
End RELATION.

Module RB := ADD_BOTTOM(RELATION).
Module DS := Dataflow_Solver(RB)(NodeSetForward).

Inductive sym_op : Type :=
| SOp : operation -> sym_op
| SLoad : memory_chunk -> addressing -> sym_op.

Record equation :=
  mkequation
    { eq_lhs : reg;
      eq_op : sym_op;
      eq_args : list reg }.

Definition eq_id := positive.

Definition add_i_j (i : reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  Regmap.set i (PSet.add j (Regmap.get i m)) m.

Lemma add_i_j_adds : forall i j m,
    PSet.contains (Regmap.get i (add_i_j i j m)) j = true.
Proof.
  intros.
  unfold add_i_j.
  rewrite Regmap.gss.
  auto with pset.
Qed.

Lemma add_i_j_monotone : forall i j i' j' m,
    PSet.contains (Regmap.get i' m) j' = true ->
    PSet.contains (Regmap.get i' (add_i_j i j m)) j' = true.
Proof.
  intros.
  unfold add_i_j.
  destruct (peq i i').
  - subst i'.
    rewrite Regmap.gss.
    destruct (peq j j').
    + subst j'.
      apply PSet.gadds.
    + eauto with pset.
  - rewrite Regmap.gso.
    assumption.
    congruence.
Qed.

Definition add_ilist_j (ilist : list reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  List.fold_left (fun already i => add_i_j i j already) ilist m.

Lemma add_ilist_j_monotone : forall ilist j i' j' m,
    PSet.contains (Regmap.get i' m) j' = true ->
    PSet.contains (Regmap.get i' (add_ilist_j ilist j m)) j' = true.
Proof.
  induction ilist; simpl; intros until m; intro CONTAINS; trivial.
  apply IHilist.
  apply add_i_j_monotone.
  assumption.
Qed.

Lemma add_ilist_j_adds : forall ilist j m,
    forall i, In i ilist ->
              PSet.contains (Regmap.get i (add_ilist_j ilist j m)) j = true.
Proof.
  induction ilist; simpl; intros until i; intro IN.
  contradiction.
  destruct IN as [HEAD | TAIL].
  - subst a.
    apply add_ilist_j_monotone.
    apply add_i_j_adds.
  - apply IHilist.
    assumption.
Qed.
    
Definition xget_kills (eqs : PTree.t equation) :=
  PTree.fold (fun already (eqno : eq_id) (eq : equation) =>
                add_i_j (eq_lhs eq) eqno
                  (add_ilist_j (eq_args eq) eqno already)). 
             
Definition totoro := RELATION.lub.
