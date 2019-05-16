(** Dependency Trees of Abstract Basic Blocks

with a purely-functional-but-exponential test.

*)


Require Setoid. (* in order to rewrite <-> *)
Require Export AbstractBasicBlocksDef.
Require Import List.

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

Section DEPTREE.

(** Dependency Trees of these "bblocks" 

NB: each tree represents the successive computations in one given resource

*)

Inductive tree :=
  | Tname (x:R.t)
  | Top (o: op) (l: list_tree)
with list_tree :=
  | Tnil: list_tree
  | Tcons (t:tree) (l:list_tree):  list_tree
  .


Fixpoint tree_eval (ge: genv) (t: tree) (m: mem): option value :=
  match t with
  | Tname x => Some (m x)
  | Top o l =>
     match list_tree_eval ge l m with
     | Some v => op_eval ge o v
     | _ => None
     end
  end
with list_tree_eval ge (l: list_tree) (m: mem) {struct l}: option (list value) :=
  match l with
  | Tnil => Some nil
  | Tcons t l' => 
    match (tree_eval ge t m), (list_tree_eval ge l' m) with
    | Some v, Some lv => Some (v::lv)
    | _, _ => None
    end
  end.

Definition deps_get (d:Dict.t tree) x := 
   match Dict.get d x with 
   | None => Tname x
   | Some t => t
   end.

Fixpoint exp_tree (e: exp) d old: tree :=
  match e with
  | PReg x => deps_get d x
  | Op o le => Top o (list_exp_tree le d old)
  | Old e => exp_tree e old old
  end
with list_exp_tree (le: list_exp) d old: list_tree :=
  match le with
  | Enil => Tnil
  | Econs e le' => Tcons (exp_tree e d old) (list_exp_tree le' d old)
  | LOld le => list_exp_tree le old old
  end.

Record deps:= {pre: genv -> mem -> Prop; post: Dict.t tree}.

Coercion post: deps >-> Dict.t.

Definition deps_eval ge (d: deps) x (m:mem) :=
  tree_eval ge (deps_get d x) m.

Definition deps_set (d:deps) x (t:tree) := 
  {| pre:=(fun ge m => (deps_eval ge d x m) <> None /\ (d.(pre) ge m));
     post:=Dict.set d x t |}.

Definition deps_empty := {| pre:=fun _ _ => True; post:=Dict.empty |}.

Variable ge: genv.

Lemma set_spec_eq d x t m:
 deps_eval ge (deps_set d x t) x m = tree_eval ge t m.
Proof.
  unfold deps_eval, deps_set, deps_get; simpl; rewrite Dict.set_spec_eq; simpl; auto. 
Qed.

Lemma set_spec_diff d x y t m:
  x <> y -> deps_eval ge (deps_set d x t) y m = deps_eval ge d y m.
Proof.
  intros; unfold deps_eval, deps_set, deps_get; simpl; rewrite Dict.set_spec_diff; simpl; auto. 
Qed.

Lemma deps_eval_empty x m: deps_eval ge deps_empty x m = Some (m x).
Proof.
  unfold deps_eval, deps_get; rewrite Dict.empty_spec; simpl; auto.
Qed.

Hint Rewrite set_spec_eq deps_eval_empty: dict_rw. 

Fixpoint inst_deps (i: inst) (d old: deps): deps :=
  match i with
  | nil => d
  | (x, e)::i' =>
     let t:=exp_tree e d old in
     inst_deps i' (deps_set d x t) old
  end.

Fixpoint bblock_deps_rec (p: bblock) (d: deps): deps :=
  match p with
  | nil => d
  | i::p' =>
     let d':=inst_deps i d d in
     bblock_deps_rec p' d'
  end.

Local Hint Resolve deps_eval_empty.

Definition bblock_deps: bblock -> deps
 := fun p => bblock_deps_rec p deps_empty.

Lemma inst_deps_pre_monotonic i old: forall d m,
  (pre (inst_deps i d old) ge m) -> (pre d ge m).
Proof.
  induction i as [|[y e] i IHi]; simpl; auto.
  intros d a H; generalize (IHi _ _ H); clear H IHi.
  unfold deps_set; simpl; intuition.
Qed.

Lemma bblock_deps_pre_monotonic p: forall d m,
  (pre (bblock_deps_rec p d) ge m) -> (pre d ge m).
Proof.
  induction p as [|i p' IHp']; simpl; eauto.
  intros d a H; eapply inst_deps_pre_monotonic; eauto.
Qed.

Local Hint Resolve inst_deps_pre_monotonic bblock_deps_pre_monotonic.

Lemma tree_eval_exp e od m0 old:
  (forall x, deps_eval ge od x m0 = Some (old x)) ->
  forall d m1,
   (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
    tree_eval ge (exp_tree e d od) m0 = exp_eval ge e m1 old.
Proof.
  unfold deps_eval in * |- *; intro H.
  induction e using exp_mut with
    (P0:=fun l => forall (d:deps) m1, (forall x, tree_eval ge (deps_get d x) m0 = Some (m1 x)) -> list_tree_eval ge (list_exp_tree l d od) m0 = list_exp_eval ge l m1 old);
  simpl; auto.
  - intros; erewrite IHe; eauto.
  - intros. erewrite IHe, IHe0; eauto. 
Qed.

Lemma inst_deps_abort i m0 x old: forall d,
    pre (inst_deps i d old) ge m0 ->
    deps_eval ge d x m0 = None ->
    deps_eval ge (inst_deps i d old) x m0 = None.
Proof.
  induction i as [|[y e] i IHi]; simpl; auto.
  intros d VALID H; erewrite IHi; eauto. clear IHi.
  destruct (R.eq_dec x y).
  * subst; autorewrite with dict_rw.
    generalize (inst_deps_pre_monotonic _ _ _ _ VALID); clear VALID.
    unfold deps_set; simpl; intuition congruence.
  * rewrite set_spec_diff; auto.
Qed.

Lemma block_deps_rec_abort p m0 x: forall d,
    pre (bblock_deps_rec p d) ge m0 ->
    deps_eval ge d x m0 = None ->
    deps_eval ge (bblock_deps_rec p d) x m0 = None.
Proof.
  induction p; simpl; auto.
  intros d VALID H; erewrite IHp; eauto. clear IHp.
  eapply inst_deps_abort; eauto.
Qed.

Lemma inst_deps_Some_correct1 i m0 old od:
  (forall x, deps_eval ge od x m0 = Some (old x)) ->
  forall (m1 m2: mem) (d: deps), 
  inst_run ge i m1 old = Some m2 -> 
  (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
   forall x, deps_eval ge (inst_deps i d od) x m0 = Some (m2 x).
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    destruct (exp_eval ge e m1 old) eqn:Heqov; try congruence.
    refine (IHi _ _ _ _ _ _); eauto.
    clear x0; intros x0.
    unfold assign; destruct (R.eq_dec x x0).
    * subst; autorewrite with dict_rw.
      erewrite tree_eval_exp; eauto.
    * rewrite set_spec_diff; auto.
Qed.

Lemma bblocks_deps_rec_Some_correct1 p m0: forall (m1 m2: mem) d, 
 run ge p m1 = Some m2 -> 
  (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
  forall x, deps_eval ge (bblock_deps_rec p d) x m0 = Some (m2 x).
Proof.
  Local Hint Resolve inst_deps_Some_correct1.
  induction p as [ | i p]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    destruct (inst_run ge i m1 m1) eqn: Heqov.
    + refine (IHp _ _ _ _ _ _); eauto.
    + inversion H. 
Qed.

Lemma bblock_deps_Some_correct1 p m0 m1:
   run ge p m0 = Some m1
   -> forall x, deps_eval ge (bblock_deps p) x m0 = Some (m1 x).
Proof.
  intros; eapply bblocks_deps_rec_Some_correct1; eauto.
Qed.

Lemma inst_deps_None_correct i m0 old od:
   (forall x, deps_eval ge od x m0 = Some (old x)) ->
  forall m1 d, pre (inst_deps i d od) ge m0 ->
   (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
  inst_run ge i m1 old = None -> exists x, deps_eval ge (inst_deps i d od) x m0 = None.
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 d.
  - discriminate.
  - intros VALID H0.
    destruct (exp_eval ge e m1 old) eqn: Heqov.
    + refine (IHi _ _ _ _); eauto.
      intros x0; unfold assign; destruct (R.eq_dec x x0).
      * subst; autorewrite with dict_rw. 
        erewrite tree_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + intuition.
      constructor 1 with (x:=x); simpl.
      apply inst_deps_abort; auto.
      autorewrite with dict_rw.
      erewrite tree_eval_exp; eauto.
Qed.

Lemma inst_deps_Some_correct2 i m0 old od:
  (forall x, deps_eval ge od x m0 = Some (old x)) ->
  forall (m1 m2: mem) d, 
  pre (inst_deps i d od) ge m0 ->
  (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
  (forall x, deps_eval ge (inst_deps i d od) x m0 = Some (m2 x)) ->
  res_eq (Some m2) (inst_run ge i m1 old).
Proof.
  intro X.
  induction i as [|[x e] i IHi]; simpl; intros m1 m2 d VALID H0.
  - intros H; eapply ex_intro; intuition eauto.
    generalize (H0 x); rewrite H.
    congruence.
  - intros H.
    destruct (exp_eval ge e m1 old) eqn: Heqov.
    + refine (IHi _ _ _ _ _ _); eauto.
      intros x0; unfold assign; destruct (R.eq_dec x x0).
      * subst. autorewrite with dict_rw.
        erewrite tree_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + generalize (H x).
      rewrite inst_deps_abort; discriminate || auto.
      autorewrite with dict_rw. 
      erewrite tree_eval_exp; eauto.
Qed.

Lemma bblocks_deps_rec_Some_correct2 p m0: forall (m1 m2: mem) d, 
  pre (bblock_deps_rec p d) ge m0 ->
  (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
  (forall x, deps_eval ge (bblock_deps_rec p d) x m0 = Some (m2 x)) ->
    res_eq (Some m2) (run ge p m1).
Proof.
  induction p as [|i p]; simpl; intros m1 m2 d VALID H0.
  - intros H; eapply ex_intro; intuition eauto.
    generalize (H0 x); rewrite H.
    congruence.
  - intros H.
     destruct (inst_run ge i m1 m1) eqn: Heqom.
    + refine (IHp _ _ _ _ _ _); eauto.
    + assert (X: exists x, tree_eval ge (deps_get (inst_deps i d d) x) m0 = None).
      { eapply inst_deps_None_correct; eauto. }
      destruct X as [x H1].
      generalize (H x).
      erewrite block_deps_rec_abort; eauto.
      congruence.
Qed.


Lemma bblock_deps_Some_correct2 p m0 m1:
  pre (bblock_deps p) ge m0 ->
  (forall x, deps_eval ge (bblock_deps p) x m0 = Some (m1 x))
  -> res_eq (Some m1) (run ge p m0).
Proof.
  intros; eapply bblocks_deps_rec_Some_correct2; eauto.
Qed.

Lemma inst_valid i m0 old od:
  (forall x, deps_eval ge od x m0 = Some (old x)) ->
  forall (m1 m2: mem) (d: deps), 
  pre d ge m0 ->
  inst_run ge i m1 old = Some m2 ->
  (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
   pre (inst_deps i d od) ge m0.
Proof.
  induction i as [|[x e] i IHi]; simpl; auto.
  intros Hold m1 m2 d VALID0 H Hm1.
  destruct (exp_eval ge e m1 old) eqn: Heq; simpl; try congruence.
  eapply IHi; eauto.
  + unfold deps_set in * |- *; simpl. 
    rewrite Hm1; intuition congruence.
  + intros x0. unfold assign; destruct (R.eq_dec x x0).
    * subst; autorewrite with dict_rw.
      erewrite tree_eval_exp; eauto.
    * rewrite set_spec_diff; auto.
Qed.


Lemma block_deps_rec_valid p m0: forall (m1 m2: mem) (d:deps), 
  pre d ge m0 ->
  run ge p m1 = Some m2 -> 
  (forall x, deps_eval ge d x m0 = Some (m1 x)) ->
  pre (bblock_deps_rec p d) ge m0.
Proof.
  Local Hint Resolve inst_valid.
  induction p as [ | i p]; simpl; intros m1 d H; auto.
  intros H0 H1.
  destruct (inst_run ge i m1 m1) eqn: Heqov; eauto.
  congruence.
Qed.

Lemma bblock_deps_valid p m0 m1:
  run ge p m0 = Some m1 ->
  pre (bblock_deps p) ge m0.
Proof.
  intros; eapply block_deps_rec_valid; eauto.
  unfold deps_empty; simpl. auto.
Qed.

Definition valid ge d m := pre d ge m /\ forall x, deps_eval ge d x m <> None.

Theorem bblock_deps_simu p1 p2:
  (forall m, valid ge (bblock_deps p1) m -> valid ge (bblock_deps p2) m) ->
  (forall m0 x m1, valid ge (bblock_deps p1) m0 -> deps_eval ge (bblock_deps p1) x m0 = Some m1 ->
                   deps_eval ge (bblock_deps p2) x m0 = Some m1) ->
   bblock_simu ge p1 p2.
Proof.
  Local Hint Resolve bblock_deps_valid bblock_deps_Some_correct1.
  unfold valid; intros INCL EQUIV m DONTFAIL.
  destruct (run ge p1 m) as [m1|] eqn: RUN1; simpl; try congruence.
  assert (X: forall x, deps_eval ge (bblock_deps p1) x m = Some (m1 x)); eauto.
  eapply bblock_deps_Some_correct2; eauto.
  + destruct (INCL m); intuition eauto.
    congruence.
  + intro x; apply EQUIV; intuition eauto.
    congruence.
Qed.

Lemma valid_set_decompose_1 d t x m:
  valid ge (deps_set d x t) m -> valid ge d m.
Proof.
  unfold valid; intros ((PRE1 & PRE2) & VALID); split.
  + intuition.
  + intros x0 H. case (R.eq_dec x x0).
    * intuition congruence.
    * intros DIFF; eapply VALID. erewrite set_spec_diff; eauto.
Qed.

Lemma valid_set_decompose_2 d t x m:
  valid ge (deps_set d x t) m -> tree_eval ge t m <> None.
Proof.
  unfold valid; intros ((PRE1 & PRE2) & VALID) H.
  generalize (VALID x); autorewrite with dict_rw.
  tauto.
Qed.

Lemma valid_set_proof d x t m:
  valid ge d m -> tree_eval ge t m <> None -> valid ge (deps_set d x t) m.
Proof.
  unfold valid; intros (PRE & VALID) PREt. split.
  + split; auto.
  + intros x0; case (R.eq_dec x x0).
    - intros; subst; autorewrite with dict_rw. auto.
    - intros. rewrite set_spec_diff; auto. 
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