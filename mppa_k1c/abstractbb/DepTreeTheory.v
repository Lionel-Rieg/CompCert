(** Dependency Trees of Abstract Basic Blocks

with a purely-functional-but-exponential equivalence test.

*)


Require Setoid. (* in order to rewrite <-> *)
Require Export AbstractBasicBlocksDef.


Module Type PseudoRegDictionary.

Declare Module R: PseudoRegisters.

Parameter t: Type -> Type.

Parameter get: forall {A}, t A -> R.t -> option A.

Parameter set: forall {A}, t A -> R.t -> A -> t A.

Parameter set_spec_eq: forall A d x (v: A),
  get (set d x v) x = Some v.

Parameter set_spec_diff: forall A d x y (v: A),
  x <> y -> get (set d x v) y = get d y.

Parameter empty: forall {A}, t A.

Parameter empty_spec: forall A x,
  get (empty (A:=A)) x = None.

End PseudoRegDictionary.


(** * Computations of "bblock" Dependencies and application to the equality test *)

Module DepTree (L: SeqLanguage) (Dict: PseudoRegDictionary with Module R:=L.LP.R).

Export L.
Export LP.
Local Open Scope list.

Section DEPTREE.

Variable ge: genv.

(** Dependency Trees of these "bblocks" 

NB: each tree represents the successive computations in one given resource

*)

Inductive tree :=
  | Tname (x:R.t)
  | Top (o: op) (l: list_tree)
  | Terase (new old:tree) (* assignment in the resource: [new] replaces [old] *)
with list_tree :=
  | Tnil: list_tree
  | Tcons (t:tree) (l:list_tree):  list_tree
  .


Fixpoint tree_eval (t: tree) (m: mem): option value :=
  match t with
  | Tname x => Some (m x)
  | Top o l =>
     match list_tree_eval l m with
     | Some v => op_eval ge o v
     | _ => None
     end
  | Terase new old =>
     (* NB: we simply check whether the old computations has aborted *)
     match tree_eval old m with
     | Some _ => tree_eval new m
     | _ => None
     end
  end
with list_tree_eval (l: list_tree) (m: mem) {struct l}: option (list value) :=
  match l with
  | Tnil => Some nil
  | Tcons t l' => 
    match (tree_eval t m), (list_tree_eval l' m) with
    | Some v, Some lv => Some (v::lv)
    | _, _ => None
    end
  end.

Definition deps:= Dict.t tree.

Definition deps_get (d:deps) x := 
   match Dict.get d x with 
   | None => Tname x
   | Some t => t
   end.

Lemma set_spec_eq d x t:
  deps_get (Dict.set d x t) x = t.
Proof.
  unfold deps_get; rewrite Dict.set_spec_eq; simpl; auto.
Qed.

Lemma set_spec_diff d x y t:
  x <> y -> deps_get (Dict.set d x t) y = deps_get d y.
Proof.
 unfold deps_get; intros; rewrite Dict.set_spec_diff; simpl; auto.
Qed.

Lemma empty_spec x: deps_get Dict.empty x = Tname x.
Proof.
 unfold deps_get; rewrite Dict.empty_spec; simpl; auto.
Qed.

Hint Rewrite set_spec_eq empty_spec: dict_rw. 

Fixpoint exp_tree (e: exp) (d old: deps): tree :=
  match e with
  | PReg x => deps_get d x
  | Op o le => Top o (list_exp_tree le d old)
  | Old e => exp_tree e old old
  end
with list_exp_tree (le: list_exp) (d old: deps): list_tree :=
  match le with
  | Enil => Tnil
  | Econs e le' => Tcons (exp_tree e d old) (list_exp_tree le' d old)
  | LOld le => list_exp_tree le old old
  end.

Definition failsafe (t: tree): bool :=
  match t with
  | Tname x => true
  | Top o Tnil => is_constant o
  | _ => false
  end.

Local Hint Resolve is_constant_correct.

Lemma failsafe_correct (t: tree) m: failsafe t = true -> tree_eval t m <> None.
Proof.
  destruct t; simpl; try congruence.
  destruct l; simpl; try congruence.
  eauto.
Qed.

Fixpoint inst_deps (i: inst) (d old: deps): deps :=
  match i with
  | nil => d
  | (x, e)::i' =>
     let t0:=deps_get d x in
     let t1:=exp_tree e d old in
     let v':=if failsafe t0 then t1 else (Terase t1 t0) in
     inst_deps i' (Dict.set d x v') old
  end.

Fixpoint bblock_deps_rec (p: bblock) (d: deps): deps :=
  match p with
  | nil => d
  | i::p' =>
     let d':=inst_deps i d d in
     bblock_deps_rec p' d'
  end.

Definition bblock_deps: bblock -> deps
 := fun p => bblock_deps_rec p Dict.empty.

(** Main Result: the [bblock_deps_equiv] theorem states that bblocks with the same dependencies are observationaly equals *)


Lemma tree_eval_exp e od m0 old:
  (forall x, tree_eval (deps_get od x) m0 = Some (old x)) ->
  forall d m1, (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
   (tree_eval (exp_tree e d od) m0) = exp_eval ge e m1 old.
Proof.
  intro H.
  induction e using exp_mut with (P0:=fun l => forall d m1, (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) -> list_tree_eval (list_exp_tree l d od) m0 = list_exp_eval ge l m1 old); simpl; auto.
  - intros; erewrite IHe; eauto.
  - intros; erewrite IHe, IHe0; eauto. 
Qed.

Lemma tree_eval_inst_abort i m0 x old: forall d,
    tree_eval (deps_get d x) m0 = None ->
    tree_eval (deps_get (inst_deps i d old) x) m0 = None.
Proof.
  induction i as [|[y e] i IHi]; simpl; auto.
  intros d H; erewrite IHi; eauto. clear IHi.
  destruct (R.eq_dec x y).
  * subst; autorewrite with dict_rw.
    generalize (failsafe_correct (deps_get d y) m0).
    destruct (failsafe (deps_get d y)); simpl; intuition try congruence.
    rewrite H; simpl. auto.
  * rewrite! set_spec_diff; auto.
Qed.

Lemma tree_eval_abort p m0 x: forall d,
    tree_eval (deps_get d x) m0 = None ->
    tree_eval (deps_get (bblock_deps_rec p d) x) m0 = None.
Proof.
  induction p; simpl; auto.
  intros d H; erewrite IHp; eauto. clear IHp.
  eapply tree_eval_inst_abort; eauto.
Qed.

Lemma tree_eval_inst_Some_correct1 i m0 old od: 
  (forall x, tree_eval (deps_get od x) m0 = Some (old x)) ->
  forall (m1 m2: mem) d, 
  inst_run ge i m1 old = Some m2 -> 
  (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
  (forall x, tree_eval (deps_get (inst_deps i d od) x) m0 = Some (m2 x)).
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    remember (exp_eval ge e m1 old) as ov.
    destruct ov.
    + refine (IHi _ _ _ _ _ _); eauto.
      clear x0; intros x0.
      unfold assign; destruct (R.eq_dec x x0).
      * subst; autorewrite with dict_rw.
        destruct (failsafe (deps_get d x0)); simpl; try rewrite H0;
        erewrite tree_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + inversion H. 
Qed.

Local Hint Resolve tree_eval_inst_Some_correct1 tree_eval_abort.

Lemma tree_eval_Some_correct1 p m0: forall (m1 m2: mem) d, 
 run ge p m1 = Some m2 -> 
  (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
    (forall x, tree_eval (deps_get (bblock_deps_rec p d) x) m0 = Some (m2 x)).
Proof.
  induction p as [ | i p]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    remember (inst_run ge i m1 m1) as om.
    destruct om.
    + refine (IHp _ _ _ _ _ _); eauto.
    + inversion H. 
Qed.

Lemma bblock_deps_Some_correct1 p m0 m1:
  run ge p m0 = Some m1
   -> forall x, tree_eval (deps_get (bblock_deps p) x) m0 = Some (m1 x).
Proof.
  intros; eapply tree_eval_Some_correct1;
  intros; autorewrite with dict_rw; simpl; eauto.
Qed.

Lemma tree_eval_inst_None_correct i m0 old od: 
  (forall x, tree_eval (deps_get od x) m0 = Some (old x)) ->
  forall m1 d,  (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
  inst_run ge i m1 old = None <-> exists x, tree_eval (deps_get (inst_deps i d od) x) m0 = None.
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 d.
  - constructor 1; [discriminate | intros [x H']; rewrite H in H'; discriminate].
  - intros H0.
    remember (exp_eval ge e m1 old) as ov.
    destruct ov.
    + refine (IHi _ _ _); eauto.
      intros x0; unfold assign; destruct (R.eq_dec x x0).
      * subst; autorewrite with dict_rw. 
        destruct (failsafe (deps_get d x0)); simpl; try rewrite H0;
        erewrite tree_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + intuition.
      constructor 1 with (x:=x); simpl.
      apply tree_eval_inst_abort.
      autorewrite with dict_rw.
      destruct (failsafe (deps_get d x)); simpl; try rewrite H0;
      erewrite tree_eval_exp; eauto.
Qed.


Lemma tree_eval_None_correct p m0: forall m1 d,
  (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
  run ge p m1 = None <-> exists x, tree_eval (deps_get (bblock_deps_rec p d) x) m0 = None.
Proof.
  induction p as [|i p IHp]; simpl; intros m1 d.
  - constructor 1; [discriminate | intros [x H']; rewrite H in H'; discriminate].
  - intros H0.
    remember (inst_run ge i m1 m1) as om.
    destruct om.
    + refine (IHp _ _ _); eauto.
    + intuition.
      assert (X: inst_run ge i m1 m1 = None); auto.
      rewrite tree_eval_inst_None_correct in X; auto.
      destruct X as [x H1].
      constructor 1 with (x:=x); simpl; auto.
Qed.

Lemma bblock_deps_None_correct p m:
  run ge p m = None <-> exists x, tree_eval (deps_get (bblock_deps p) x) m = None.
Proof.
  intros; eapply tree_eval_None_correct.
  intros; autorewrite with dict_rw; simpl; eauto.
Qed.

Lemma tree_eval_inst_Some_correct2 i m0 old od: 
  (forall x, tree_eval (deps_get od x) m0 = Some (old x)) ->
  forall (m1 m2: mem) d, 
  (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
    (forall x, tree_eval (deps_get (inst_deps i d od) x) m0 = Some (m2 x)) ->
    res_eq (Some m2) (inst_run ge i m1 old).
Proof.
  intro X.
  induction i as [|[x e] i IHi]; simpl; intros m1 m2 d H0.
  - intros H; eapply ex_intro; intuition eauto.
    generalize (H0 x); rewrite H.
    congruence.
  - intros H.
    remember (exp_eval ge e m1 old) as ov.
    destruct ov.
    + refine (IHi _ _ _ _ _); eauto.
      intros x0; unfold assign; destruct (R.eq_dec x x0).
      * subst; autorewrite with dict_rw.
        destruct (failsafe (deps_get d x0)); simpl; try rewrite H0;
        erewrite tree_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + generalize (H x).
      rewrite tree_eval_inst_abort; try discriminate.
      autorewrite with dict_rw. 
      destruct (failsafe (deps_get d x)); simpl; try rewrite H0;
      erewrite tree_eval_exp; eauto.
Qed.

Lemma tree_eval_Some_correct2 p m0: forall (m1 m2: mem) d, 
  (forall x, tree_eval (deps_get d x) m0 = Some (m1 x)) ->
    (forall x, tree_eval (deps_get (bblock_deps_rec p d) x) m0 = Some (m2 x)) ->
    res_eq (Some m2) (run ge p m1).
Proof.
  induction p as [|i p]; simpl; intros m1 m2 d H0.
  - intros H; eapply ex_intro; intuition eauto.
    generalize (H0 x); rewrite H.
    congruence.
  - intros H.
    remember (inst_run ge i m1 m1) as om.
    destruct om.
    + refine (IHp _ _ _ _ _); eauto.
    + assert (X: inst_run ge i m1 m1 = None); auto.
      rewrite tree_eval_inst_None_correct in X; auto.
      destruct X as [x H1].
      generalize (H x).
      rewrite tree_eval_abort; congruence.
Qed.

Lemma bblock_deps_Some_correct2 p m0 m1:
  (forall x, tree_eval (deps_get (bblock_deps p) x) m0 = Some (m1 x))
  -> res_eq (Some m1) (run ge p m0).
Proof.
  intros; eapply tree_eval_Some_correct2; eauto.
  intros; autorewrite with dict_rw; simpl; eauto.
Qed.


Theorem bblock_deps_equiv p1 p2:
  (forall x, deps_get (bblock_deps p1) x = deps_get (bblock_deps p2) x)
   -> bblock_equiv ge p1 p2.
Proof.
  intros H m2.
  remember (run ge p1 m2) as om1.
  destruct om1; simpl.
  + apply bblock_deps_Some_correct2.
    intros; rewrite <- H.
    apply bblock_deps_Some_correct1; auto.
  + rewrite bblock_deps_None_correct.
    assert (X: run ge p1 m2 = None); auto.
    rewrite bblock_deps_None_correct in X.
    destruct X as [x Hx].
    rewrite H in Hx.
    eauto.
Qed.

End DEPTREE.

End DepTree.

Require Import PArith.
Require Import FMapPositive.

Module PosDict <: PseudoRegDictionary with Module R:=Pos.

Module R:=Pos.

Definition t:=PositiveMap.t.

Definition get {A} (d:t A) (x:R.t): option A 
 := PositiveMap.find x d.

Definition set {A} (d:t A) (x:R.t) (v:A): t A
 := PositiveMap.add x v d.

Local Hint Unfold PositiveMap.E.eq.

Lemma set_spec_eq A d x (v: A):
  get (set d x v) x = Some v.
Proof.
  unfold get, set; apply PositiveMap.add_1; auto.
Qed.

Lemma set_spec_diff A d x y (v: A):
  x <> y -> get (set d x v) y = get d y.
Proof.
  unfold get, set; intros; apply PositiveMap.gso; auto.
Qed.

Definition empty {A}: t A := PositiveMap.empty A.

Lemma empty_spec A x:
  get (empty (A:=A)) x = None.
Proof.
  unfold get, empty; apply PositiveMap.gempty; auto.
Qed.

End PosDict.