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
Hint Resolve add_i_j_adds: cse3.

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

Hint Resolve add_i_j_monotone: cse3.

Definition add_ilist_j (ilist : list reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  List.fold_left (fun already i => add_i_j i j already) ilist m.

Lemma add_ilist_j_monotone : forall ilist j i' j' m,
    PSet.contains (Regmap.get i' m) j' = true ->
    PSet.contains (Regmap.get i' (add_ilist_j ilist j m)) j' = true.
Proof.
  induction ilist; simpl; intros until m; intro CONTAINS; auto with cse3.
Qed.
Hint Resolve add_ilist_j_monotone: cse3.

Lemma add_ilist_j_adds : forall ilist j m,
    forall i, In i ilist ->
              PSet.contains (Regmap.get i (add_ilist_j ilist j m)) j = true.
Proof.
  induction ilist; simpl; intros until i; intro IN.
  contradiction.
  destruct IN as [HEAD | TAIL]; subst; auto with cse3.
Qed.
Hint Resolve add_ilist_j_adds: cse3.

Definition get_kills (eqs : PTree.t equation) :
  Regmap.t PSet.t :=
  PTree.fold (fun already (eqno : eq_id) (eq : equation) =>
                add_i_j (eq_lhs eq) eqno
                        (add_ilist_j (eq_args eq) eqno already)) eqs
  (PMap.init PSet.empty). 

Definition xlget_kills (eqs : list (eq_id * equation)) (m :  Regmap.t PSet.t) :
  Regmap.t PSet.t :=
  List.fold_left (fun already (item : eq_id * equation) =>
    add_i_j (eq_lhs (snd item)) (fst item)
            (add_ilist_j (eq_args (snd item)) (fst item) already)) eqs m. 

Lemma xlget_kills_monotone :
  forall eqs m i j,
    PSet.contains (Regmap.get i m) j = true ->
    PSet.contains (Regmap.get i (xlget_kills eqs m)) j = true.
Proof.
  induction eqs; simpl; trivial.
  intros.
  auto with cse3.
Qed.

Hint Resolve xlget_kills_monotone : cse3.

Lemma xlget_kills_has_lhs :
  forall eqs m lhs sop args j,
    In (j, {| eq_lhs := lhs;
              eq_op  := sop;
              eq_args:= args |}) eqs ->
    PSet.contains (Regmap.get lhs (xlget_kills eqs m)) j = true.
Proof.
  induction eqs; simpl.
  contradiction.
  intros until j.
  intro HEAD_TAIL.
  destruct HEAD_TAIL as [HEAD | TAIL]; subst; simpl.
  - auto with cse3.
  - eapply IHeqs. eassumption.
Qed.
Hint Resolve xlget_kills_has_lhs : cse3.

Lemma xlget_kills_has_arg :
  forall eqs m lhs sop arg args j,
    In (j, {| eq_lhs := lhs;
              eq_op  := sop;
              eq_args:= args |}) eqs ->
    In arg args ->
    PSet.contains (Regmap.get arg (xlget_kills eqs m)) j = true.
Proof.
  induction eqs; simpl.
  contradiction.
  intros until j.
  intros HEAD_TAIL ARG.
  destruct HEAD_TAIL as [HEAD | TAIL]; subst; simpl.
  - auto with cse3.
  - eapply IHeqs; eassumption.
Qed.

Hint Resolve xlget_kills_has_arg : cse3.


Lemma get_kills_has_lhs :
  forall eqs lhs sop args j,
    PTree.get j eqs = Some {| eq_lhs := lhs;
                              eq_op  := sop;
                              eq_args:= args |} ->
    PSet.contains (Regmap.get lhs (get_kills eqs)) j = true.
Proof.
  unfold get_kills.
  intros.
  rewrite PTree.fold_spec.
  change (fold_left
       (fun (a : Regmap.t PSet.t) (p : positive * equation) =>
        add_i_j (eq_lhs (snd p)) (fst p)
          (add_ilist_j (eq_args (snd p)) (fst p) a))) with xlget_kills.
  eapply xlget_kills_has_lhs.
  apply PTree.elements_correct.
  eassumption.
Qed.

Lemma get_kills_has_arg :
  forall eqs lhs sop arg args j,
    PTree.get j eqs = Some {| eq_lhs := lhs;
                              eq_op  := sop;
                              eq_args:= args |} ->
    In arg args ->
    PSet.contains (Regmap.get arg (get_kills eqs)) j = true.
Proof.
  unfold get_kills.
  intros.
  rewrite PTree.fold_spec.
  change (fold_left
       (fun (a : Regmap.t PSet.t) (p : positive * equation) =>
        add_i_j (eq_lhs (snd p)) (fst p)
          (add_ilist_j (eq_args (snd p)) (fst p) a))) with xlget_kills.
  eapply xlget_kills_has_arg.
  - apply PTree.elements_correct.
    eassumption.
  - assumption.
Qed.

(*
Lemma xget_kills_monotone :
  forall eqs m i j,
    PSet.contains (Regmap.get i m) j = true ->
    PSet.contains (Regmap.get i (xget_kills eqs m)) j = true.
Proof.
  unfold xget_kills.
  intros eqs m.
  rewrite PTree.fold_spec.
  generalize (PTree.elements eqs).
  intro.
  generalize m.
  clear m.
  induction l; simpl; trivial.
  intros.
  apply IHl.
  apply add_i_j_monotone.
  apply add_ilist_j_monotone.
  assumption.
Qed.
*)
Lemma xget_kills_has_lhs :
  forall eqs m lhs sop args j,
    PTree.get j eqs = Some {| eq_lhs := lhs;
                              eq_op  := sop;
                              eq_args:= args |} ->
    PSet.contains (Regmap.get lhs (xget_kills eqs m)) j = true.

Definition eq_involves (eq : equation) (i : reg) :=
  i = (eq_lhs eq) \/ In i (eq_args eq).


Definition totoro := RELATION.lub.
