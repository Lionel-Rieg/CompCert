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

Hint Rewrite orb_false_r andb_false_r andb_true_r orb_true_r orb_idem andb_idem  andb_negb_false : pmap.

Parameter T : Type.
Parameter T_eq_dec : forall (x y : T), {x = y} + {x <> y}.

Inductive pmap : Type :=
| Empty : pmap
| Node : pmap -> option T -> pmap -> pmap.
Definition empty := Empty.

Definition is_empty x :=
  match x with
  | Empty => true
  | Node _ _ _ => false
  end.

Definition is_some (x : option T) :=
  match x with
  | Some _ => true
  | None => false
  end.

Fixpoint wf x :=
  match x with
  | Empty => true
  | Node b0 f b1 =>
    (wf b0) && (wf b1) &&
    ((negb (is_empty b0)) || (is_some f) || (negb (is_empty b1)))
  end.

Definition iswf x := (wf x)=true.
  
Lemma empty_wf : iswf empty.
Proof.
  reflexivity.
Qed.

Definition pmap_eq :
  forall s s': pmap, { s=s' } + { s <> s' }.
Proof.
  generalize T_eq_dec.
  induction s; destruct s'; repeat decide equality.
Qed.

Fixpoint get (i : positive) (s : pmap) {struct i} : option T :=
  match s with
  | Empty => None
  | Node b0 f b1 =>
    match i with
    | xH => f
    | xO ii => get ii b0
    | xI ii => get ii b1
    end
  end.

Lemma gempty :
  forall i : positive,
    get i Empty = None.
Proof.
  destruct i; simpl; reflexivity.
Qed.

Hint Resolve gempty : pmap.
Hint Rewrite gempty : pmap.

Definition node (b0 : pmap) (f : option T) (b1 : pmap) : pmap :=
  match b0, f, b1 with
  | Empty, None, Empty => Empty
  | _, _, _ => Node b0 f b1
  end.

Lemma wf_node :
  forall b0 f b1,
    iswf b0 -> iswf b1 -> iswf (node b0 f b1).
Proof.
  destruct b0; destruct f; destruct b1; simpl.
  all: unfold iswf; simpl; intros; trivial.
  all: autorewrite with pmap; trivial.
  all: rewrite H.
  all: rewrite H0.
  all: reflexivity.
Qed.

Hint Resolve wf_node: pmap.

Lemma gnode :
  forall b0 f b1 i,
    get i (node b0 f b1) =
    get i (Node b0 f b1).
Proof.
  destruct b0; simpl; trivial.
  destruct f; simpl; trivial.
  destruct b1; simpl; trivial.
  intro.
  rewrite gempty.
  destruct i; simpl; trivial.
  all: symmetry; apply gempty.
Qed.

Hint Rewrite gnode : pmap.

Fixpoint set (i : positive) (j : T) (s : pmap) {struct i} : pmap :=
  match s with
  | Empty =>
    match i with
    | xH => Node Empty (Some j) Empty
    | xO ii => Node (set ii j Empty) None Empty
    | xI ii => Node Empty None (set ii j Empty)
    end
  | Node b0 f b1 =>
    match i with
    | xH => Node b0 (Some j) b1
    | xO ii => Node (set ii j b0) f b1
    | xI ii => Node b0 f (set ii j b1)
    end
  end.

Lemma set_nonempty:
  forall i j s, is_empty (set i j s) = false.
Proof.
  induction i; destruct s; simpl; trivial.
Qed.

Hint Rewrite set_nonempty : pmap.
Hint Resolve set_nonempty : pmap.

Lemma wf_set:
  forall i j s, (iswf s) -> (iswf (set i j s)).
Proof.
  induction i; destruct s; simpl; trivial.
  all: unfold iswf in *; simpl.
  all: autorewrite with pmap; simpl; trivial.
  1,3: auto with pmap.
  all: intro Z.
  all: repeat rewrite andb_true_iff in Z.
  all: intuition.
Qed.

Hint Resolve wf_set : pset.

Theorem gss :
  forall (i : positive) (j : T) (s : pmap),
    get i (set i j s) = Some j.
Proof.
  induction i; destruct s; simpl; auto.
Qed.

Hint Resolve gss : pmap.
Hint Rewrite gss : pmap.

Theorem gso :
  forall (i j : positive) (k : T) (s : pmap),
    i <> j ->
    get j (set i k s) = get j s.
Proof.
  induction i; destruct j; destruct s; simpl; intro; auto with pmap.
  5, 6: congruence.
  all: rewrite IHi by congruence.
  all: trivial.
  all: apply gempty.
Qed.

Hint Resolve gso : pmap.

Fixpoint remove (i : positive) (s : pmap) { struct i } : pmap :=
  match i with
  | xH =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => node b0 None b1
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

Fixpoint remove_noncanon (i : positive) (s : pmap) { struct i } : pmap :=
  match i with
  | xH =>
    match s with
    | Empty => Empty
    | Node b0 f b1 => Node b0 None b1
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
  forall i j s, (get j (remove i s)) = (get j (remove_noncanon i s)).
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

Hint Rewrite remove_empty : pmap.
Hint Resolve remove_empty : pmap.

Lemma gremove_noncanon_s :
  forall i : positive,
  forall s : pmap,
    get i (remove_noncanon i s) = None.
Proof.
  induction i; destruct s; simpl; trivial.
Qed.

Theorem grs :
  forall i : positive,
  forall s : pmap,
    get i (remove i s) = None.
Proof.
  intros.
  rewrite remove_noncanon_same.
  apply gremove_noncanon_s.
Qed.

Hint Resolve grs : pmap.
Hint Rewrite grs : pmap.

Lemma gremove_noncanon_o :
  forall i j : positive,
  forall s : pmap,
    i<>j ->
    get j (remove_noncanon i s) = get j s.
Proof.
  induction i; destruct j; destruct s; simpl; intro; trivial.
  1, 2: rewrite IHi by congruence.
  1, 2: reflexivity.
  congruence.
Qed.

Theorem gro :
  forall (i j : positive) (s : pmap),
    i<>j ->
    get j (remove i s) = get j s.
Proof.
  intros.
  rewrite remove_noncanon_same.
  apply gremove_noncanon_o.
  assumption.
Qed.

Hint Resolve gro : pmap.

Section MAP2.
  
  Variable f : option T -> option T -> option T.

  Section NONE_NONE.
    Hypothesis f_none_none : f None None = None.

    Fixpoint map2_Empty (b : pmap) :=
      match b with
      | Empty => Empty
      | Node b0 bf b1 =>
        node (map2_Empty b0) (f None bf) (map2_Empty b1)
      end.

    Lemma gmap2_Empty: forall i b,
        get i (map2_Empty b) = f None (get i b).
    Proof.
      induction i; destruct b as [ | b0 bf b1]; intros; simpl in *.
      all: try congruence.
      - replace
          (match node (map2_Empty b0) (f None bf) (map2_Empty b1) with
           | Empty => None
           | Node _ _ c1 => get i c1
           end)
          with (get (xI i) (node (map2_Empty b0) (f None bf) (map2_Empty b1))).
        + rewrite gnode.
          simpl. apply IHi.
        + destruct node; auto with pmap.
      - replace
          (match node (map2_Empty b0) (f None bf) (map2_Empty b1) with
           | Empty => None
           | Node c0 _ _ => get i c0
           end)
          with (get (xO i) (node (map2_Empty b0) (f None bf) (map2_Empty b1))).
        + rewrite gnode.
          simpl. apply IHi.
        + destruct node; auto with pmap.
      - change (match node (map2_Empty b0) (f None bf) (map2_Empty b1) with
                | Empty => None
                | Node _ cf _ => cf
                end) with (get xH (node (map2_Empty b0) (f None bf) (map2_Empty b1))).
        rewrite gnode. reflexivity.
    Qed.
    
    Fixpoint map2 (a b : pmap) :=
      match a with
      | Empty => map2_Empty b
      | (Node a0 af a1) =>
        match b with
        | (Node b0 bf b1) =>
          node (map2 a0 b0) (f af bf) (map2 a1 b1)
        | Empty =>
          node (map2 a0 Empty) (f af None) (map2 a1 Empty)
        end
      end.
  
    Lemma gmap2: forall a b i,
        get i (map2 a b) = f (get i a) (get i b).
    Proof.
      induction a as [ | a0 IHa0 af a1 IHa1]; intros; simpl.
      { rewrite gmap2_Empty.
        rewrite gempty.
        reflexivity. }
      destruct b as [ | b0 bf b1 ]; simpl; rewrite gnode.
      - destruct i; simpl.
        + rewrite IHa1. rewrite gempty.
          reflexivity.
        + rewrite IHa0. rewrite gempty.
          reflexivity.
        + reflexivity.
      - destruct i; simpl; congruence.
    Qed.
  End NONE_NONE.

  Section IDEM.
    Hypothesis f_idem : forall x, f x x = x.
    
    Fixpoint map2_idem (a b : pmap) :=
      if pmap_eq a b then a else
      match a with
      | Empty => map2_Empty b
      | (Node a0 af a1) =>
        match b with
        | (Node b0 bf b1) =>
          node (map2_idem a0 b0) (f af bf) (map2_idem a1 b1)
        | Empty =>
          node (map2_idem a0 Empty) (f af None) (map2_idem a1 Empty)
        end
      end.
 
    Lemma gmap2_idem: forall a b i,
        get i (map2_idem a b) = f (get i a) (get i b).
    Proof.
      induction a as [ | a0 IHa0 af a1 IHa1]; intros; simpl.
      { destruct pmap_eq.
        - subst b. rewrite gempty. congruence.
        - rewrite gempty.
          rewrite gmap2_Empty by congruence.
          reflexivity.
      }
      destruct pmap_eq.
      { subst b.
        congruence.
      }
      destruct b as [ | b0 bf b1 ]; simpl; rewrite gnode.
      - destruct i; simpl.
        + rewrite IHa1. rewrite gempty.
          reflexivity.
        + rewrite IHa0. rewrite gempty.
          reflexivity.
        + reflexivity.
      - destruct i; simpl; congruence.
    Qed.
  End IDEM.
End MAP2.
