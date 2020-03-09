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

Definition eq_id := node.

Definition add_i_j (i : reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  Regmap.set i (PSet.add j (Regmap.get i m)) m.

Definition add_ilist_j (ilist : list reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  List.fold_left (fun already i => add_i_j i j already) ilist m.

Definition get_kills (eqs : PTree.t equation) :
  Regmap.t PSet.t :=
  PTree.fold (fun already (eqno : eq_id) (eq : equation) =>
                add_i_j (eq_lhs eq) eqno
                        (add_ilist_j (eq_args eq) eqno already)) eqs
             (PMap.init PSet.empty).

Definition is_move (op : operation) :
  { op = Omove } + { op <> Omove }.
Proof.
  destruct op; try (right ; congruence).
  left; trivial.
Qed.

Definition is_smove (sop : sym_op) :
  { sop = SOp Omove } + { sop <> SOp Omove }.
Proof.
  destruct sop; try (right ; congruence).
  destruct (is_move o).
  - left; congruence.
  - right; congruence.
Qed.

Definition get_move (eq : equation) :=
  if is_smove (eq_op eq)
  then match eq_args eq with
       | h::nil => Some h
       | _ => None
       end
  else None.

Definition get_moves (eqs : PTree.t equation) :
  Regmap.t PSet.t :=
  PTree.fold (fun already (eqno : eq_id) (eq : equation) =>
                match get_move eq with
                | Some rhs => add_i_j (eq_lhs eq) rhs already
                | None => already
                end) eqs (PMap.init PSet.empty).

Record eq_context := mkeqcontext
                       { eq_catalog : node -> option equation;
                         eq_kills : reg -> PSet.t }.

Section OPERATIONS.
  Context {ctx : eq_context}.
  
  Definition kill_reg (r : reg) (rel : RELATION.t) : RELATION.t :=
    PSet.subtract rel (eq_kills ctx r).
End OPERATIONS.

Definition totoro := RELATION.lub.
