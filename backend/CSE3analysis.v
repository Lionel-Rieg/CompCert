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

Definition totoro := RELATION.lub.
