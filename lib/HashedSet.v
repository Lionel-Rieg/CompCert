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

Require Import ZArith.
Require Import Bool.
Require Import List.
Require Coq.Logic.Eqdep_dec.

(* begin from Maps *)
Fixpoint prev_append (i j: positive) {struct i} : positive :=
  match i with
  | xH => j
  | xI i' => prev_append i' (xI j)
  | xO i' => prev_append i' (xO j)
  end.

Definition prev (i: positive) : positive :=
  prev_append i xH.

Lemma prev_append_prev i j:
  prev (prev_append i j) = prev_append j i.
Proof.
  revert j. unfold prev.
  induction i as [i IH|i IH|]. 3: reflexivity.
  intros j. simpl. rewrite IH. reflexivity.
  intros j. simpl. rewrite IH. reflexivity.
Qed.

Lemma prev_involutive i :
  prev (prev i) = i.
Proof (prev_append_prev i xH).

Lemma prev_append_inj i j j' :
  prev_append i j = prev_append i j' -> j = j'.
Proof.
  revert j j'.
  induction i as [i Hi|i Hi|]; intros j j' H; auto;
    specialize (Hi _ _ H); congruence.
Qed.

(* end from Maps *)

Lemma orb_idem: forall b, orb b b = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma andb_idem: forall b, andb b b = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma andb_negb_false: forall b, andb b (negb b) = false.
Proof.
  destruct b; reflexivity.
Qed.

Hint Rewrite orb_false_r andb_false_r andb_true_r orb_true_r orb_idem andb_idem  andb_negb_false : pset.

Module PSet_internals.
Inductive pset : Type :=
| Empty : pset
| Node : pset -> bool -> pset -> pset.

Definition empty := Empty.

Definition is_empty x :=
  match x with
  | Empty => true
  | Node _ _ _ => false
  end.

Fixpoint wf x :=
  match x with
  | Empty => true
  | Node b0 f b1 =>
    (wf b0) && (wf b1) &&
    ((negb (is_empty b0)) || f || (negb (is_empty b1)))
  end.

Definition iswf x := (wf x)=true.
  
Lemma empty_wf : iswf empty.
Proof.
  reflexivity.
Qed.

Definition pset_eq :
  forall s s': pset, { s=s' } + { s <> s' }.
Proof.
  induction s; destruct s'; repeat decide equality.
Qed.

Fixpoint contains (s : pset) (i : positive) {struct i} : bool :=
  match s with
  | Empty => false
  | Node b0 f b1 =>
    match i with
    | xH => f
    | xO ii => contains b0 ii
    | xI ii => contains b1 ii
    end
  end.

Lemma gempty :
  forall i : positive,
    contains Empty i = false.
Proof.
  destruct i; simpl; reflexivity.
Qed.

Hint Resolve gempty : pset.
Hint Rewrite gempty : pset.

Definition node (b0 : pset) (f : bool) (b1 : pset) : pset :=
  match b0, f, b1 with
  | Empty, false, Empty => Empty
  | _, _, _ => Node b0 f b1
  end.

Lemma wf_node :
  forall b0 f b1,
    iswf b0 -> iswf b1 -> iswf (node b0 f b1).
Proof.
  destruct b0; destruct f; destruct b1; simpl.
  all: unfold iswf; simpl; intros; trivial.
  all: autorewrite with pset; trivial.
  all: rewrite H.
  all: rewrite H0.
  all: reflexivity.
Qed.

Hint Resolve wf_node: pset.

Lemma gnode :
  forall b0 f b1 i,
    contains (node b0 f b1) i =
    contains (Node b0 f b1) i.
Proof.
  destruct b0; simpl; trivial.
  destruct f; simpl; trivial.
  destruct b1; simpl; trivial.
  intro.
  rewrite gempty.
  destruct i; simpl; trivial.
  all: symmetry; apply gempty.
Qed.

Hint Rewrite gnode : pset.

Fixpoint add (i : positive) (s : pset) {struct i} : pset :=
  match s with
  | Empty =>
    match i with
    | xH => Node Empty true Empty
    | xO ii => Node (add ii Empty) false Empty
    | xI ii => Node Empty false (add ii Empty)
    end
  | Node b0 f b1 =>
    match i with
    | xH => Node b0 true b1
    | xO ii => Node (add ii b0) f b1
    | xI ii => Node b0 f (add ii b1)
    end
  end.

Lemma add_nonempty:
  forall i s, is_empty (add i s) = false.
Proof.
  induction i; destruct s; simpl; trivial.
Qed.

Hint Rewrite add_nonempty : pset.
Hint Resolve add_nonempty : pset.

Lemma wf_add:
  forall i s, (iswf s) -> (iswf (add i s)).
Proof.
  induction i; destruct s; simpl; trivial.
  all: unfold iswf in *; simpl.
  all: autorewrite with pset; simpl; trivial.
  1,3: auto with pset.
  all: intro Z.
  all: repeat rewrite andb_true_iff in Z.
  all: intuition.
Qed.

Hint Resolve wf_add : pset.

Theorem gadds :
  forall i : positive,
  forall s : pset,
    contains (add i s) i = true.
Proof.
  induction i; destruct s; simpl; auto.
Qed.

Hint Resolve gadds : pset.
Hint Rewrite gadds : pset.

Theorem gaddo :
  forall i j : positive,
  forall s : pset,
    i <> j ->
    contains (add i s) j = contains s j.
Proof.
  induction i; destruct j; destruct s; simpl; intro; auto with pset.
  5, 6: congruence.
  all: rewrite IHi by congruence.
  all: trivial.
  all: apply gempty.
Qed.

Hint Resolve gaddo : pset.

Fixpoint remove (i : positive) (s : pset) { struct i } : pset :=
  match i with
  | xH =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => node b0 false b1
    end
  | xO ii =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => node (remove ii b0) f b1
    end
  | xI ii =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => node b0 f (remove ii b1)
    end
  end.

Lemma wf_remove :
  forall i s, (iswf s) -> (iswf (remove i s)).
Proof.
  induction i; destruct s; simpl; trivial.
  all: unfold iswf in *; simpl.
  all: intro Z.
  all: repeat rewrite andb_true_iff in Z.
  all: apply wf_node.
  all: intuition.
  all: apply IHi.
  all: assumption.
Qed.
  

Fixpoint remove_noncanon (i : positive) (s : pset) { struct i } : pset :=
  match i with
  | xH =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => Node b0 false b1
    end
  | xO ii =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => Node (remove_noncanon ii b0) f b1
    end
  | xI ii =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => Node b0 f (remove_noncanon ii b1)
    end
  end.

Lemma remove_noncanon_same:
  forall i j s, (contains (remove i s) j) = (contains (remove_noncanon i s) j).
Proof.
  induction i; destruct s; simpl; trivial.
  all: rewrite gnode.
  3: reflexivity.
  all: destruct j; simpl; trivial.
Qed.

Lemma remove_empty :
  forall i, remove i Empty = Empty.
Proof.
  induction i; simpl; trivial.
Qed.

Hint Rewrite remove_empty : pset.
Hint Resolve remove_empty : pset.

Lemma gremove_noncanon_s :
  forall i : positive,
  forall s : pset,
    contains (remove_noncanon i s) i = false.
Proof.
  induction i; destruct s; simpl; trivial.
Qed.

Theorem gremoves :
  forall i : positive,
  forall s : pset,
    contains (remove i s) i = false.
Proof.
  intros.
  rewrite remove_noncanon_same.
  apply gremove_noncanon_s.
Qed.

Hint Resolve gremoves : pset.
Hint Rewrite gremoves : pset.

Lemma gremove_noncanon_o :
  forall i j : positive,
  forall s : pset,
    i<>j ->
    contains (remove_noncanon i s) j = contains s j.
Proof.
  induction i; destruct j; destruct s; simpl; intro; trivial.
  1, 2: rewrite IHi by congruence.
  1, 2: reflexivity.
  congruence.
Qed.

Theorem gremoveo :
  forall i j : positive,
  forall s : pset,
    i<>j ->
    contains (remove i s) j = contains s j.
Proof.
  intros.
  rewrite remove_noncanon_same.
  apply gremove_noncanon_o.
  assumption.
Qed.

Hint Resolve gremoveo : pset.

Fixpoint union_nonopt (s s' : pset) : pset :=
  match s, s' with
  | Empty, _ => s'
  | _, Empty => s
  | (Node b0 f b1), (Node b0' f' b1') =>
    Node (union_nonopt b0 b0') (orb f f') (union_nonopt b1 b1')
  end.

Theorem gunion_nonopt:
  forall s s' : pset,
  forall j : positive,
    (contains (union_nonopt s s')) j = orb (contains s j) (contains s' j).
Proof.
  induction s; destruct s'; intro; simpl; autorewrite with pset; simpl; trivial.
  destruct j; simpl; trivial.
Qed.


Fixpoint union (s s' : pset) : pset :=
  if pset_eq s s' then s else
  match s, s' with
  | Empty, _ => s'
  | _, Empty => s
  | (Node b0 f b1), (Node b0' f' b1') =>
    Node (union b0 b0') (orb f f') (union b1 b1')
  end.

Lemma union_nonempty1:
  forall s s',
    (is_empty s) = false -> is_empty (union s s')= false.
Proof.
  induction s; destruct s'; simpl; try discriminate.
  all: destruct pset_eq; simpl; trivial.
Qed.

Lemma union_nonempty2:
  forall s s',
    (is_empty s') = false -> is_empty (union s s')= false.
Proof.
  induction s; destruct s'; simpl; try discriminate.
  all: destruct pset_eq; simpl; trivial; discriminate.
Qed.

Hint Resolve union_nonempty1 union_nonempty2 : pset.

Lemma wf_union :
  forall s s', (iswf s) -> (iswf s') -> (iswf (union s s')).
Proof.
  induction s; destruct s'; intros; simpl.
  all: destruct pset_eq; trivial.
  unfold iswf in *. simpl in *.
  repeat rewrite andb_true_iff in H.
  repeat rewrite andb_true_iff in H0.
  rewrite IHs1.
  rewrite IHs2.
  simpl.
  all: intuition.
  repeat rewrite orb_true_iff in H2, H3.
  repeat rewrite negb_true_iff in H2, H3.
  repeat rewrite orb_true_iff.
  repeat rewrite negb_true_iff.
  intuition auto with pset.
Qed.

Hint Resolve wf_union : pset.

Theorem gunion:
  forall s s' : pset,
  forall j : positive,
    (contains (union s s')) j = orb (contains s j) (contains s' j).
Proof.
  induction s; destruct s'; intro; simpl.
  all: destruct pset_eq as [EQ | NEQ]; try congruence.
  all: autorewrite with pset; simpl; trivial.
  - rewrite <- EQ.
    symmetry.
    apply orb_idem.
  - destruct j; simpl; trivial.
Qed.

Fixpoint inter_noncanon (s s' : pset) : pset :=
  if pset_eq s s' then s else
  match s, s' with
  | Empty, _ | _, Empty => Empty
  | (Node b0 f b1), (Node b0' f' b1') =>
    Node (inter_noncanon b0 b0') (andb f f') (inter_noncanon b1 b1')
  end.

Lemma ginter_noncanon:
  forall s s' : pset,
  forall j : positive,
    (contains (inter_noncanon s s')) j = andb (contains s j) (contains s' j).
Proof.
  induction s; destruct s'; intro; simpl.
  all: destruct pset_eq as [EQ | NEQ]; try congruence.
  all: autorewrite with pset; simpl; trivial.
  - rewrite <- EQ.
    symmetry.
    apply andb_idem.
  - destruct j; simpl; trivial.
Qed.

Fixpoint inter (s s' : pset) : pset :=
  if pset_eq s s' then s else
  match s, s' with
  | Empty, _ | _, Empty => Empty
  | (Node b0 f b1), (Node b0' f' b1') =>
    node (inter b0 b0') (andb f f') (inter b1 b1')
  end.

Lemma wf_inter :
  forall s s', (iswf s) -> (iswf s') -> (iswf (inter s s')).
Proof.
  induction s; destruct s'; intros; simpl.
  all: destruct pset_eq; trivial.
  unfold iswf in H, H0.
  simpl in H, H0.
  repeat rewrite andb_true_iff in H.
  repeat rewrite andb_true_iff in H0.
  fold (iswf s1) in *.
  fold (iswf s2) in *.
  intuition.
Qed.

Hint Resolve wf_inter : pset.

Lemma inter_noncanon_same:
  forall s s' j, (contains (inter s s') j) = (contains (inter_noncanon s s') j).
Proof.
  induction s; destruct s'; simpl; trivial.
  destruct pset_eq; trivial.
  destruct j; rewrite gnode; simpl; auto.
Qed.

Theorem ginter:
  forall s s' : pset,
  forall j : positive,
    (contains (inter s s')) j = andb (contains s j) (contains s' j).
Proof.
  intros.
  rewrite inter_noncanon_same.
  apply ginter_noncanon.
Qed.

Hint Resolve ginter gunion : pset.
Hint Rewrite ginter gunion : pset.

Fixpoint subtract_noncanon (s s' : pset) : pset :=
  if pset_eq s s' then Empty else
  match s, s' with
  | Empty, _ => Empty
  | _, Empty => s
  | (Node b0 f b1), (Node b0' f' b1') =>
    Node (subtract_noncanon b0 b0') (andb f (negb f')) (subtract_noncanon b1 b1')
  end.

Lemma gsubtract_noncanon:
  forall s s' : pset,
  forall j : positive,
    (contains (subtract_noncanon s s')) j = andb (contains s j) (negb (contains s' j)).
Proof.
  induction s; destruct s'; intro; simpl.
  all: destruct pset_eq as [EQ | NEQ]; try congruence.
  all: autorewrite with pset; simpl; trivial.
  - rewrite <- EQ.
    symmetry.
    apply andb_negb_false.
  - destruct j; simpl; trivial.
Qed.

Fixpoint subtract (s s' : pset) : pset :=
  if pset_eq s s' then Empty else
  match s, s' with
  | Empty, _ => Empty
  | _, Empty => s
  | (Node b0 f b1), (Node b0' f' b1') =>
    node (subtract b0 b0') (andb f (negb f')) (subtract b1 b1')
  end.

Lemma wf_subtract :
  forall s s', (iswf s) -> (iswf s') -> (iswf (subtract s s')).
Proof.
  induction s; destruct s'; intros; simpl.
  all: destruct pset_eq; trivial.
  reflexivity.
  
  unfold iswf in H, H0.
  simpl in H, H0.
  
  repeat rewrite andb_true_iff in H.
  repeat rewrite andb_true_iff in H0.
  fold (iswf s1) in *.
  fold (iswf s2) in *.
  intuition.
Qed.

Hint Resolve wf_subtract : pset.

Lemma subtract_noncanon_same:
  forall s s' j, (contains (subtract s s') j) = (contains (subtract_noncanon s s') j).
Proof.
  induction s; destruct s'; simpl; trivial.
  destruct pset_eq; trivial.
  destruct j; rewrite gnode; simpl; auto.
Qed.

Theorem gsubtract:
  forall s s' : pset,
  forall j : positive,
    (contains (subtract s s')) j = andb (contains s j) (negb (contains s' j)).
Proof.
  intros.
  rewrite subtract_noncanon_same.
  apply gsubtract_noncanon.
Qed.

Hint Resolve gsubtract : pset.
Hint Rewrite gsubtract : pset.

Lemma wf_is_nonempty :
  forall s, iswf s -> is_empty s = false -> exists i, contains s i = true.
Proof.
  induction s; simpl; trivial.
  discriminate.
  intro WF.
  unfold iswf in WF.
  simpl in WF.
  repeat rewrite andb_true_iff in WF.
  repeat rewrite orb_true_iff in WF.
  repeat rewrite negb_true_iff in WF.
  fold (iswf s1) in WF.
  fold (iswf s2) in WF.
  intuition.
  - destruct H5 as [i K].
    exists (xO i).
    simpl.
    assumption.
  - exists xH.
    simpl.
    assumption.
  - destruct H5 as [i K].
    exists (xI i).
    simpl.
    assumption.
Qed.

Hint Resolve wf_is_nonempty : pset.

Lemma wf_is_empty1 :
  forall s, iswf s -> (forall i, (contains s i) = false) -> is_empty s = true.
Proof.
  induction s; trivial.
  intro WF.
  unfold iswf in WF.
  simpl in WF.
  repeat rewrite andb_true_iff in WF.
  fold (iswf s1) in WF.
  fold (iswf s2) in WF.
  intro ALL.
  intuition.
  exfalso.
  repeat rewrite orb_true_iff in H0.
  repeat rewrite negb_true_iff in H0.
  intuition.
  - rewrite H in H0. discriminate.
    intro i.
    specialize ALL with (xO i).
    simpl in ALL.
    assumption.
  - specialize ALL with xH.
    simpl in ALL.
    congruence.
  - rewrite H3 in H4. discriminate.
    intro i.
    specialize ALL with (xI i).
    simpl in ALL.
    assumption.
Qed.
  
Hint Resolve wf_is_empty1 : pset.

Lemma wf_eq :
  forall s s', iswf s -> iswf s' -> s <> s' ->
               exists i, (contains s i) <> (contains s' i).
Proof.
  induction s; destruct s'; intros WF WF' DIFF; simpl.
  - congruence.
  - assert (exists i, (contains (Node s'1 b s'2) i)= true) as K by auto with pset.
    destruct K as [i Z].
    exists i.
    rewrite Z.
    rewrite gempty.
    discriminate.
  - assert (exists i, (contains (Node s1 b s2) i)= true) as K by auto with pset.
    destruct K as [i Z].
    exists i.
    rewrite Z.
    rewrite gempty.
    discriminate.
  - destruct (pset_eq s1 s'1).
    + subst s'1.
      destruct (pset_eq s2 s'2).
      * subst s'2.
        exists xH.
        simpl.
        congruence.
      * specialize IHs2 with s'2.
        unfold iswf in WF.
        simpl in WF.
        repeat rewrite andb_true_iff in WF.
        fold (iswf s1) in WF.
        fold (iswf s2) in WF.
        unfold iswf in WF'.
        simpl in WF'.
        repeat rewrite andb_true_iff in WF'.
        fold (iswf s'2) in WF'.
        intuition.
        destruct H1 as [i K].
        exists (xI i).
        simpl.
        assumption.
    + specialize IHs1 with s'1.
      unfold iswf in WF.
      simpl in WF.
      repeat rewrite andb_true_iff in WF.
      fold (iswf s1) in WF.
      fold (iswf s2) in WF.
      unfold iswf in WF'.
      simpl in WF'.
      repeat rewrite andb_true_iff in WF'.
      fold (iswf s'1) in WF'.
      fold (iswf s'2) in WF'.
      intuition.
      destruct H1 as [i K].
      exists (xO i).
      simpl.
      assumption.
Qed.

Theorem eq_correct:
  forall s s',
    (iswf s) -> (iswf s') ->
    (forall i, (contains s i) = (contains s' i)) <-> s = s'.
Proof.
  intros s s' WF WF'.
  split.
  {
    intro ALL.
    destruct (pset_eq s s') as [ | INEQ]; trivial.
    exfalso.
    destruct (wf_eq s s' WF WF' INEQ) as [i K].
    specialize ALL with i.
    congruence.
  }
  intro EQ.
  subst s'.
  trivial.
Qed.

Lemma wf_irrelevant:
  forall s,
  forall WF WF' : iswf s, WF = WF'.
Proof.
  unfold iswf.
  intros.
  apply Coq.Logic.Eqdep_dec.eq_proofs_unicity_on.
  decide equality.
Qed.
  
Fixpoint xelements (s : pset) (i : positive)
                       (k: list positive) {struct s}
                       : list positive :=
  match s with
  | Empty => k
  | Node b0 false b1 =>
    xelements b0 (xO i) (xelements b1 (xI i) k)
  | Node b0 true b1 =>
    xelements b0 (xO i) ((prev i) :: xelements b1 (xI i) k)
  end.

Definition elements (m : pset) := xelements m xH nil.

  Remark xelements_append:
    forall (m: pset) i k1 k2,
    xelements m i (k1 ++ k2) = xelements m i k1 ++ k2.
  Proof.
    induction m; intros; simpl.
  - auto.
  - destruct b; rewrite IHm2; rewrite <- IHm1; auto.
  Qed.

  Remark xelements_empty:
    forall i, xelements Empty i nil = nil.
  Proof.
    intros; reflexivity.
  Qed.

  Remark xelements_node:
    forall (m1: pset) o (m2: pset) i,
    xelements (Node m1 o m2) i nil =
       xelements m1 (xO i) nil
    ++ (if o then (prev i) :: nil else nil)
    ++ xelements m2 (xI i) nil.
  Proof.
    intros. simpl. destruct o; simpl;
    rewrite <- xelements_append; trivial.
  Qed.

  Lemma xelements_incl:
    forall (m: pset) (i : positive) k x,
      In x k -> In x (xelements m i k).
  Proof.
    induction m; intros; simpl.
    auto.
    destruct b.
    apply IHm1. simpl; right; auto.
    auto.
  Qed.

  Lemma xelements_correct:
    forall (m: pset) (i j : positive) k,
      contains m i=true -> In (prev (prev_append i j)) (xelements m j k).
  Proof.
    induction m; intros; simpl.
    - rewrite gempty in H. discriminate.
    - destruct b; destruct i; simpl; simpl in H; auto.
      + apply xelements_incl. simpl.
        right. auto.
      + apply xelements_incl. simpl.
        left. trivial.
      + apply xelements_incl. auto.
      + discriminate.
    Qed.

  Theorem elements_correct:
    forall (m: pset) (i: positive),
    contains m i = true -> In i (elements m).
  Proof.
    intros m i H.
    generalize (xelements_correct m i xH nil H). rewrite prev_append_prev. exact id.
  Qed.

  Lemma in_xelements:
    forall (m: pset) (i k: positive),
    In k (xelements m i nil) ->
    exists j, k = prev (prev_append j i) /\ contains m j = true.
  Proof.
    induction m; intros.
  - rewrite xelements_empty in H. contradiction.
  - rewrite xelements_node in H. rewrite ! in_app_iff in H. destruct H as [P | [P | P]].
    + specialize IHm1 with (k := k) (i := xO i).
      intuition.
      destruct H as [j [Q R]].
      exists (xO j).
      auto.
    + destruct b; simpl in P; intuition auto. subst k. exists xH; auto.
    + specialize IHm2 with (k := k) (i := xI i).
      intuition.
      destruct H as [j [Q R]].
      exists (xI j).
      auto.
  Qed.

  Theorem elements_complete:
    forall (m: pset) (i: positive),
    In i (elements m) -> contains m i = true.
  Proof.
    unfold elements. intros m i H.
    destruct (in_xelements m 1 i H) as [j [P Q]].
    rewrite prev_append_prev in P. change i with (prev_append 1 i) in P.
    replace j with i in * by (apply prev_append_inj; auto).
    assumption.
  Qed.


  Fixpoint xfold {B: Type} (f: B -> positive -> B)
                 (i: positive) (m: pset) (v: B) {struct m} : B :=
    match m with
    | Empty => v
    | Node l false r =>
        let v1 := xfold f (xO i) l v in
        xfold f (xI i) r v1
    | Node l true r =>
        let v1 := xfold f (xO i) l v in
        let v2 := f v1 (prev i) in
        xfold f (xI i) r v2
    end.

  Definition fold {B : Type} (f: B -> positive -> B) (m: pset) (v: B) :=
    xfold f xH m v.


  Lemma xfold_xelements:
    forall {B: Type} (f: B -> positive -> B) m i v l,
    List.fold_left f l (xfold f i m v) =
    List.fold_left f (xelements m i l) v.
  Proof.
    induction m; intros; simpl; trivial.
    destruct b; simpl.
    all: rewrite <- IHm1; simpl; rewrite <- IHm2; trivial.
  Qed.

  Theorem fold_spec:
    forall {B: Type} (f: B -> positive -> B) (v: B) (m: pset),
    fold f m v =
    List.fold_left f (elements m) v.
  Proof.
    intros. unfold fold, elements. rewrite <- xfold_xelements. auto.
  Qed.

  Fixpoint is_subset (s s' : pset) {struct s} :=
    if pset_eq s s' then true else
    match s, s' with
    | Empty, _ => true
    | _, Empty => false
    | (Node b0 f b1), (Node b0' f' b1') =>
      ((negb f) || f') &&
      (is_subset b0 b0') &&
      (is_subset b1 b1')
    end.

  Theorem is_subset_spec1:
    forall s s',
      is_subset s s' = true ->
      (forall i, contains s i = true -> contains s' i = true).
  Proof.
    induction s; destruct s'; simpl; intros; trivial.
    all: destruct pset_eq.
    all: try discriminate.
    all: try rewrite gempty in *.
    all: try discriminate.
    { congruence.
    }
    repeat rewrite andb_true_iff in H.
    repeat rewrite orb_true_iff in H.
    repeat rewrite negb_true_iff in H.
    specialize IHs1 with (s' := s'1).
    specialize IHs2 with (s' := s'2).
    intuition.
    - destruct i; simpl in *; auto. congruence.
    - destruct i; simpl in *; auto.
  Qed.
  
  Theorem is_subset_spec2:
    forall s s',
      iswf s ->
      (forall i, contains s i = true -> contains s' i = true) ->
      is_subset s s' = true.
  Proof.
    induction s; destruct s'; simpl.
    all: intro WF.
    all: unfold iswf in WF.
    all: simpl in WF.
    all: repeat rewrite andb_true_iff in WF.
    all: destruct pset_eq; trivial.
    all: fold (iswf s1) in WF.
    all: fold (iswf s2) in WF.
    - repeat rewrite orb_true_iff in WF.
      repeat rewrite negb_true_iff in WF.
      intuition.
      + destruct (wf_is_nonempty s1 H2 H1) as [i K].
        specialize H with (xO i).
        simpl in H.
        auto.
      + specialize H with xH.
        simpl in H.
        auto.
      + destruct (wf_is_nonempty s2 H3 H0) as [i K].
        specialize H with (xI i).
        simpl in H.
        auto.
    - intro CONTAINS.
      repeat rewrite andb_true_iff.
      specialize IHs1 with (s' := s'1).
      specialize IHs2 with (s' := s'2).
      intuition.
      + specialize CONTAINS with xH.
        simpl in CONTAINS.
        destruct b; destruct b0; intuition congruence.
      + apply H.
        intros.
        specialize CONTAINS with (xO i).
        simpl in CONTAINS.
        auto.
      + apply H3.
        intros.
        specialize CONTAINS with (xI i).
        simpl in CONTAINS.
        auto.
  Qed.

  Fixpoint xfilter (fn : positive -> bool)
           (s : pset) (i : positive) {struct s} : pset :=
  match s with
  | Empty => Empty
  | Node b0 f b1 =>
    node (xfilter fn b0 (xO i))
         (f && (fn (prev i)))
         (xfilter fn b1 (xI i))
  end.
  
  Lemma gxfilter:
    forall fn s j i,
      contains (xfilter fn s i) j =
      contains s j &&
      (fn (prev (prev_append j i))).
  Proof.
    induction s; simpl; intros; trivial.
    {
      rewrite gempty.
      trivial.
    }
    rewrite gnode.
    destruct j; simpl; auto.
  Qed.

  Definition filter (fn : positive -> bool) m := xfilter fn m xH.

  Lemma gfilter:
    forall fn s j,
      contains (filter fn s) j =
      contains s j && (fn j).
  Proof.
    intros.
    unfold filter.
    rewrite gxfilter.
    rewrite prev_append_prev.
    reflexivity.
  Qed.

  Lemma wf_xfilter:
    forall fn s j,
      iswf s -> iswf (xfilter fn s j).
  Proof.
    induction s; intros; trivial.
    simpl.
    unfold iswf in H.
    simpl in H.
    repeat rewrite andb_true_iff in H.
    fold (iswf s1) in H.
    fold (iswf s2) in H.
    intuition.
  Qed.

  Lemma wf_filter:
    forall fn s,
      iswf s -> iswf (filter fn s).
  Proof.
    intros.
    apply wf_xfilter; auto.
  Qed.
End PSet_internals.

Module Type POSITIVE_SET.
Parameter t : Type.
Parameter empty : t.

Parameter contains: t -> positive -> bool.

Axiom gempty :
  forall i : positive,
    contains empty i = false.

Parameter add : positive -> t -> t.

Axiom gaddo :
  forall i j : positive,
  forall s : t,
    i <> j ->
    contains (add i s) j = contains s j.

Axiom gadds :
  forall i : positive,
  forall s : t,
    contains (add i s) i = true.

Parameter remove : positive -> t -> t.

Axiom gremoves :
  forall i : positive,
  forall s : t,
    contains (remove i s) i = false.

Axiom gremoveo :
  forall i j : positive,
  forall s : t,
    i<>j ->
    contains (remove i s) j = contains s j.

Parameter union : t -> t -> t.

Axiom gunion:
  forall s s' : t,
  forall j : positive,
    (contains (union s s')) j = orb (contains s j) (contains s' j).

Parameter inter : t -> t -> t.

Axiom ginter:
  forall s s' : t,
  forall j : positive,
    (contains (inter s s')) j = andb (contains s j) (contains s' j).

Parameter subtract : t -> t -> t.

Axiom gsubtract:
  forall s s' : t,
  forall j : positive,
    (contains (subtract s s')) j = andb (contains s j) (negb (contains s' j)).

Axiom uneq_exists :
  forall s s', s <> s' ->
               exists i, (contains s i) <> (contains s' i).

Parameter eq:
  forall s s' : t, {s = s'} + {s <> s'}.

Axiom eq_spec :
  forall s s',
    (forall i, (contains s i) = (contains s' i)) <-> s = s'.

Parameter elements : t -> list positive.

Axiom elements_correct:
  forall (m: t) (i: positive),
    contains m i = true -> In i (elements m).

Axiom elements_complete:
  forall (m: t) (i: positive),
    In i (elements m) -> contains m i = true.

Axiom elements_spec:
  forall (m: t) (i: positive),
    In i (elements m) <-> contains m i = true.

Parameter fold:
  forall {B : Type},
    (B -> positive -> B) -> t -> B -> B.

Axiom fold_spec:
  forall {B: Type} (f: B -> positive -> B) (v: B) (m: t),
    fold f m v =
    List.fold_left f (elements m) v.

Parameter is_subset : t -> t -> bool.

Axiom is_subset_spec1:
  forall s s',
    is_subset s s' = true ->
    (forall i, contains s i = true -> contains s' i = true).

Axiom is_subset_spec2:
  forall s s',
    (forall i, contains s i = true -> contains s' i = true) ->
    is_subset s s' = true.

Axiom is_subset_spec:
  forall s s',
    is_subset s s' = true <->
    (forall i, contains s i = true -> contains s' i = true).

Parameter filter: (positive -> bool) -> t -> t.

Axiom gfilter:
  forall fn s j,
    contains (filter fn s) j =
    contains s j && (fn j).
  
End POSITIVE_SET.

Module PSet : POSITIVE_SET.

Record pset : Type := mkpset
{
  pset_x : PSet_internals.pset ;
  pset_wf : PSet_internals.wf pset_x = true
}.

Definition t := pset.

Program Definition empty : t := mkpset PSet_internals.empty _.

Definition contains (s : t) (i : positive) :=
  PSet_internals.contains (pset_x s) i.

Theorem gempty :
  forall i : positive,
    contains empty i = false.
Proof.
  intro.
  unfold empty, contains.
  simpl.
  auto with pset.
Qed.

Program Definition add (i : positive) (s : t) :=
  mkpset (PSet_internals.add i (pset_x s)) _.
Obligation 1.
  destruct s.
  apply PSet_internals.wf_add.
  simpl.
  assumption.
Qed.

Theorem gaddo :
  forall i j : positive,
  forall s : t,
    i <> j ->
    contains (add i s) j = contains s j.
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Theorem gadds :
  forall i : positive,
  forall s : pset,
    contains (add i s) i = true.
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Program Definition remove (i : positive) (s : t) :=
  mkpset (PSet_internals.remove i (pset_x s)) _.
Obligation 1.
  destruct s.
  apply PSet_internals.wf_remove.
  simpl.
  assumption.
Qed.

Theorem gremoves :
  forall i : positive,
  forall s : pset,
    contains (remove i s) i = false.
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Theorem gremoveo :
  forall i j : positive,
  forall s : pset,
    i<>j ->
    contains (remove i s) j = contains s j.
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Program Definition union (s s' : t) :=
  mkpset (PSet_internals.union (pset_x s) (pset_x s')) _.
Obligation 1.
  destruct s; destruct s'.
  apply PSet_internals.wf_union; simpl; assumption.
Qed.

Theorem gunion:
  forall s s' : pset,
  forall j : positive,
    (contains (union s s')) j = orb (contains s j) (contains s' j).
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Program Definition inter (s s' : t) :=
  mkpset (PSet_internals.inter (pset_x s) (pset_x s')) _.
Obligation 1.
  destruct s; destruct s'.
  apply PSet_internals.wf_inter; simpl; assumption.
Qed.

Theorem ginter:
  forall s s' : pset,
  forall j : positive,
    (contains (inter s s')) j = andb (contains s j) (contains s' j).
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Program Definition subtract (s s' : t) :=
  mkpset (PSet_internals.subtract (pset_x s) (pset_x s')) _.
Obligation 1.
  destruct s; destruct s'.
  apply PSet_internals.wf_subtract; simpl; assumption.
Qed.

Theorem gsubtract:
  forall s s' : pset,
  forall j : positive,
    (contains (subtract s s')) j = andb (contains s j) (negb (contains s' j)).
Proof.
  intros.
  unfold contains.
  simpl.
  auto with pset.
Qed.

Theorem uneq_exists :
  forall s s', s <> s' ->
               exists i, (contains s i) <> (contains s' i).
Proof.
  destruct s as [s WF]; destruct s' as [s' WF']; simpl.
  intro UNEQ.
  destruct (PSet_internals.pset_eq s s').
  { subst s'.
    pose proof (PSet_internals.wf_irrelevant s WF WF').
    subst WF'.
    congruence.
  }
  unfold contains; simpl.
  apply PSet_internals.wf_eq; trivial.
Qed.

Definition eq:
  forall s s' : t, {s = s'} + {s <> s'}.
Proof.
  destruct s as [s WF].
  destruct s' as [s' WF'].
  destruct (PSet_internals.pset_eq s s'); simpl.
  {
    subst s'.
    left.
    pose proof (PSet_internals.wf_irrelevant s WF WF').
    subst WF'.
    reflexivity.
  }
  right.
  congruence.
Qed.

Theorem eq_spec :
  forall s s',
    (forall i, (contains s i) = (contains s' i)) <-> s = s'.
Proof.
  intros.
  split; intro K.
  2: subst s'; reflexivity.
  destruct s as [s WF].
  destruct s' as [s' WF'].
  unfold contains in K.
  simpl in K.
  fold (PSet_internals.iswf s) in WF.
  fold (PSet_internals.iswf s') in WF'.
  assert (s = s').
  {
    apply PSet_internals.eq_correct; assumption.
  }
  subst s'.
  pose proof (PSet_internals.wf_irrelevant s WF WF').
  subst WF'.
  reflexivity.
Qed.


Definition elements (m : t) := PSet_internals.elements (pset_x m).


Theorem elements_correct:
  forall (m: pset) (i: positive),
    contains m i = true -> In i (elements m).
Proof.
  destruct m; unfold elements, contains; simpl.
  apply PSet_internals.elements_correct.
Qed.

Theorem elements_complete:
  forall (m: pset) (i: positive),
    In i (elements m) -> contains m i = true.
Proof.
  destruct m; unfold elements, contains; simpl.
  apply PSet_internals.elements_complete.
Qed.


Theorem elements_spec:
  forall (m: pset) (i: positive),
    In i (elements m) <-> contains m i = true.
Proof.
  intros. split.
  - apply elements_complete.
  - apply elements_correct.
Qed.

Definition fold {B : Type} (f : B -> positive -> B) (m : t) (v : B) : B :=
  PSet_internals.fold f (pset_x m) v.

Theorem fold_spec:
  forall {B: Type} (f: B -> positive -> B) (v: B) (m: pset),
    fold f m v =
    List.fold_left f (elements m) v.
Proof.
  destruct m; unfold fold, elements; simpl.
  apply PSet_internals.fold_spec.
Qed.

Definition is_subset (s s' : t) := PSet_internals.is_subset (pset_x s) (pset_x s').

Theorem is_subset_spec1:
  forall s s',
    is_subset s s' = true ->
    (forall i, contains s i = true -> contains s' i = true).
Proof.
  unfold is_subset, contains.
  intros s s' H.
  apply PSet_internals.is_subset_spec1.
  assumption.
Qed.

Theorem is_subset_spec2:
  forall s s',
    (forall i, contains s i = true -> contains s' i = true) ->
    is_subset s s' = true.
Proof.
  destruct s; destruct s';
    unfold is_subset, contains;
    intros.
  apply PSet_internals.is_subset_spec2.
  all: simpl.
  all: assumption.
Qed.

Hint Resolve is_subset_spec1 is_subset_spec2 : pset.

Theorem is_subset_spec:
  forall s s',
    is_subset s s' = true <->
    (forall i, contains s i = true -> contains s' i = true).
Proof.
  intros.
  split;
  eauto with pset.
Qed.

Program Definition filter (fn : positive -> bool) (m : t) : t :=
  (mkpset (PSet_internals.filter fn (pset_x m)) _).
Obligation 1.
  apply PSet_internals.wf_filter.
  unfold PSet_internals.iswf.
  destruct m.
  assumption.
Qed.

Theorem gfilter:
  forall fn s j,
    contains (filter fn s) j =
    contains s j && (fn j).
Proof.
  unfold contains, filter.
  simpl.
  intros.
  apply PSet_internals.gfilter.
Qed.
End PSet.

Hint Resolve PSet.gaddo PSet.gadds PSet.gremoveo PSet.gremoves PSet.gunion PSet.ginter PSet.gsubtract PSet.gfilter PSet.is_subset_spec1 PSet.is_subset_spec2 : pset.

Hint Rewrite PSet.gadds PSet.gremoves PSet.gunion PSet.ginter PSet.gsubtract PSet.gfilter : pset.
