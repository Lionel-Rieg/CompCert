
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE3analysis CSE2deps CSE2depsproof HashedSet.
Require Import Lia.

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

Definition eq_involves (eq : equation) (i : reg) :=
  i = (eq_lhs eq) \/ In i (eq_args eq).

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

  Variable eq_catalog : PTree.t equation.
  
  Definition sem_eq (eq : equation) (rs : regset) (m : mem) :=
    match eq_op eq with
    | SOp op =>
      match eval_operation genv sp op (rs ## (eq_args eq)) m with
      | Some v => rs # (eq_lhs eq) = v
      | None => False
      end
    | SLoad chunk addr =>
      match
        match eval_addressing genv sp addr rs##(eq_args eq) with
        | Some a => Mem.loadv chunk m a
        | None => None
        end
      with
      | Some dat => rs # (eq_lhs eq) = dat
      | None => rs # (eq_lhs eq) = default_notrap_load_value chunk
      end
    end.

  Definition sem_rel (rel : RELATION.t) (rs : regset) (m : mem) :=
    forall i eq,
      PSet.contains rel i = true ->
      PTree.get i eq_catalog = Some eq ->
      sem_eq eq rs m.
End SOUNDNESS.
