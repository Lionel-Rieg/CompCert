(** A theory for checking/proving simulation by symbolic execution.

*)


Require Setoid. (* in order to rewrite <-> *)
Require Export AbstractBasicBlocksDef.
Require Import List.
Require Import ImpPrelude.
Import HConsingDefs.

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


Module SimuTheory (L: SeqLanguage) (Dict: PseudoRegDictionary with Module R:=L.LP.R).

Export L.
Export LP.
Export Terms.

(* the symbolic memory:
  - pre: pre-condition expressing that the computation has not yet abort on a None.
  - post: the post-condition for each pseudo-register 
*)
Record smem:= {pre: genv -> mem -> Prop; post: Dict.t term}.

Coercion post: smem >-> Dict.t.

(** initial symbolic memory *)
Definition smem_empty := {| pre:=fun _ _ => True; post:=Dict.empty |}.

Definition smem_get (d:Dict.t term) x := 
   match Dict.get d x with 
   | None => Input x unknown_hid
   | Some t => t
   end.

Fixpoint exp_term (e: exp) (d old: Dict.t term): term :=
  match e with
  | PReg x => smem_get d x
  | Op o le => App o (list_exp_term le d old) unknown_hid
  | Old e => exp_term e old old
  end
with list_exp_term (le: list_exp) (d old: Dict.t term) : list_term :=
  match le with
  | Enil => LTnil unknown_hid
  | Econs e le' => LTcons (exp_term e d old) (list_exp_term le' d old) unknown_hid
  | LOld le => list_exp_term le old old
  end.

(** evaluation of the post-condition *)
Definition smem_eval ge (d: Dict.t term) x (m:mem) :=
  term_eval ge (smem_get d x) m.

(** assignment of the symbolic memory *)
Definition smem_set (d:smem) x (t:term) := 
  {| pre:=(fun ge m => (smem_eval ge d x m) <> None /\ (d.(pre) ge m));
     post:=Dict.set d x t |}.

Section SIMU_THEORY.

Variable ge: genv.

Lemma set_spec_eq d x t m:
 smem_eval ge (smem_set d x t) x m = term_eval ge t m.
Proof.
  unfold smem_eval, smem_set, smem_get; simpl; rewrite Dict.set_spec_eq; simpl; auto. 
Qed.

Lemma set_spec_diff d x y t m:
  x <> y -> smem_eval ge (smem_set d x t) y m = smem_eval ge d y m.
Proof.
  intros; unfold smem_eval, smem_set, smem_get; simpl; rewrite Dict.set_spec_diff; simpl; auto. 
Qed.

Lemma smem_eval_empty x m: smem_eval ge smem_empty x m = Some (m x).
Proof.
  unfold smem_eval, smem_get; rewrite Dict.empty_spec; simpl; auto.
Qed.

Hint Rewrite set_spec_eq smem_eval_empty: dict_rw. 

Fixpoint inst_smem (i: inst) (d old: smem): smem :=
  match i with
  | nil => d
  | (x, e)::i' =>
     let t:=exp_term e d old in
     inst_smem i' (smem_set d x t) old
  end.

Fixpoint bblock_smem_rec (p: bblock) (d: smem): smem :=
  match p with
  | nil => d
  | i::p' =>
     let d':=inst_smem i d d in
     bblock_smem_rec p' d'
  end.

Local Hint Resolve smem_eval_empty.

Definition bblock_smem: bblock -> smem
 := fun p => bblock_smem_rec p smem_empty.

Lemma inst_smem_pre_monotonic i old: forall d m,
  (pre (inst_smem i d old) ge m) -> (pre d ge m).
Proof.
  induction i as [|[y e] i IHi]; simpl; auto.
  intros d a H; generalize (IHi _ _ H); clear H IHi.
  unfold smem_set; simpl; intuition.
Qed.

Lemma bblock_smem_pre_monotonic p: forall d m,
  (pre (bblock_smem_rec p d) ge m) -> (pre d ge m).
Proof.
  induction p as [|i p' IHp']; simpl; eauto.
  intros d a H; eapply inst_smem_pre_monotonic; eauto.
Qed.

Local Hint Resolve inst_smem_pre_monotonic bblock_smem_pre_monotonic.

Lemma term_eval_exp e (od:smem) m0 old:
  (forall x, smem_eval ge od x m0 = Some (old x)) ->
  forall d m1,
   (forall x, smem_eval ge (d:smem) x m0 = Some (m1 x)) ->
    term_eval ge (exp_term e d od) m0 = exp_eval ge e m1 old.
Proof.
  unfold smem_eval in * |- *; intro H.
  induction e using exp_mut with
    (P0:=fun l => forall (d:smem) m1, (forall x, term_eval ge (smem_get d x) m0 = Some (m1 x)) -> list_term_eval ge (list_exp_term l d od) m0 = list_exp_eval ge l m1 old);
  simpl; auto.
  - intros; erewrite IHe; eauto.
  - intros. erewrite IHe, IHe0; eauto. 
Qed.

Lemma inst_smem_abort i m0 x old: forall d,
    pre (inst_smem i d old) ge m0 ->
    smem_eval ge d x m0 = None ->
    smem_eval ge (inst_smem i d old) x m0 = None.
Proof.
  induction i as [|[y e] i IHi]; simpl; auto.
  intros d VALID H; erewrite IHi; eauto. clear IHi.
  destruct (R.eq_dec x y).
  * subst; autorewrite with dict_rw.
    generalize (inst_smem_pre_monotonic _ _ _ _ VALID); clear VALID.
    unfold smem_set; simpl; intuition congruence.
  * rewrite set_spec_diff; auto.
Qed.

Lemma block_smem_rec_abort p m0 x: forall d,
    pre (bblock_smem_rec p d) ge m0 ->
    smem_eval ge d x m0 = None ->
    smem_eval ge (bblock_smem_rec p d) x m0 = None.
Proof.
  induction p; simpl; auto.
  intros d VALID H; erewrite IHp; eauto. clear IHp.
  eapply inst_smem_abort; eauto.
Qed.

Lemma inst_smem_Some_correct1 i m0 old (od:smem): 
  (forall x, smem_eval ge od x m0 = Some (old x)) ->
  forall (m1 m2: mem) (d: smem), 
  inst_run ge i m1 old = Some m2 -> 
  (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
   forall x, smem_eval ge (inst_smem i d od) x m0 = Some (m2 x).
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    destruct (exp_eval ge e m1 old) eqn:Heqov; try congruence.
    refine (IHi _ _ _ _ _ _); eauto.
    clear x0; intros x0.
    unfold assign; destruct (R.eq_dec x x0).
    * subst; autorewrite with dict_rw.
      erewrite term_eval_exp; eauto.
    * rewrite set_spec_diff; auto.
Qed.

Lemma bblocks_smem_rec_Some_correct1 p m0: forall (m1 m2: mem) (d: smem), 
 run ge p m1 = Some m2 -> 
  (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
  forall x, smem_eval ge (bblock_smem_rec p d) x m0 = Some (m2 x).
Proof.
  Local Hint Resolve inst_smem_Some_correct1.
  induction p as [ | i p]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    destruct (inst_run ge i m1 m1) eqn: Heqov.
    + refine (IHp _ _ _ _ _ _); eauto.
    + inversion H. 
Qed.

Lemma bblock_smem_Some_correct1 p m0 m1:
   run ge p m0 = Some m1
   -> forall x, smem_eval ge (bblock_smem p) x m0 = Some (m1 x).
Proof.
  intros; eapply bblocks_smem_rec_Some_correct1; eauto.
Qed.

Lemma inst_smem_None_correct i m0 old (od: smem):
   (forall x, smem_eval ge od x m0 = Some (old x)) ->
  forall m1 d, pre (inst_smem i d od) ge m0 ->
   (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
  inst_run ge i m1 old = None -> exists x, smem_eval ge (inst_smem i d od) x m0 = None.
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 d.
  - discriminate.
  - intros VALID H0.
    destruct (exp_eval ge e m1 old) eqn: Heqov.
    + refine (IHi _ _ _ _); eauto.
      intros x0; unfold assign; destruct (R.eq_dec x x0).
      * subst; autorewrite with dict_rw. 
        erewrite term_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + intuition.
      constructor 1 with (x:=x); simpl.
      apply inst_smem_abort; auto.
      autorewrite with dict_rw.
      erewrite term_eval_exp; eauto.
Qed.

Lemma inst_smem_Some_correct2 i m0 old (od: smem):
  (forall x, smem_eval ge od x m0 = Some (old x)) ->
  forall (m1 m2: mem) d, 
  pre (inst_smem i d od) ge m0 ->
  (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
  (forall x, smem_eval ge (inst_smem i d od) x m0 = Some (m2 x)) ->
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
        erewrite term_eval_exp; eauto.
      * rewrite set_spec_diff; auto.
    + generalize (H x).
      rewrite inst_smem_abort; discriminate || auto.
      autorewrite with dict_rw. 
      erewrite term_eval_exp; eauto.
Qed.

Lemma bblocks_smem_rec_Some_correct2 p m0: forall (m1 m2: mem) d, 
  pre (bblock_smem_rec p d) ge m0 ->
  (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
  (forall x, smem_eval ge (bblock_smem_rec p d) x m0 = Some (m2 x)) ->
    res_eq (Some m2) (run ge p m1).
Proof.
  induction p as [|i p]; simpl; intros m1 m2 d VALID H0.
  - intros H; eapply ex_intro; intuition eauto.
    generalize (H0 x); rewrite H.
    congruence.
  - intros H.
     destruct (inst_run ge i m1 m1) eqn: Heqom.
    + refine (IHp _ _ _ _ _ _); eauto.
    + assert (X: exists x, term_eval ge (smem_get (inst_smem i d d) x) m0 = None).
      { eapply inst_smem_None_correct; eauto. }
      destruct X as [x H1].
      generalize (H x).
      erewrite block_smem_rec_abort; eauto.
      congruence.
Qed.


Lemma bblock_smem_Some_correct2 p m0 m1:
  pre (bblock_smem p) ge m0 ->
  (forall x, smem_eval ge (bblock_smem p) x m0 = Some (m1 x))
  -> res_eq (Some m1) (run ge p m0).
Proof.
  intros; eapply bblocks_smem_rec_Some_correct2; eauto.
Qed.

Lemma inst_valid i m0 old (od:smem):
  (forall x, smem_eval ge od x m0 = Some (old x)) ->
  forall (m1 m2: mem) (d: smem), 
  pre d ge m0 ->
  inst_run ge i m1 old = Some m2 ->
  (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
   pre (inst_smem i d od) ge m0.
Proof.
  induction i as [|[x e] i IHi]; simpl; auto.
  intros Hold m1 m2 d VALID0 H Hm1.
  destruct (exp_eval ge e m1 old) eqn: Heq; simpl; try congruence.
  eapply IHi; eauto.
  + unfold smem_set in * |- *; simpl. 
    rewrite Hm1; intuition congruence.
  + intros x0. unfold assign; destruct (R.eq_dec x x0).
    * subst; autorewrite with dict_rw.
      erewrite term_eval_exp; eauto.
    * rewrite set_spec_diff; auto.
Qed.


Lemma block_smem_rec_valid p m0: forall (m1 m2: mem) (d:smem), 
  pre d ge m0 ->
  run ge p m1 = Some m2 -> 
  (forall x, smem_eval ge d x m0 = Some (m1 x)) ->
  pre (bblock_smem_rec p d) ge m0.
Proof.
  Local Hint Resolve inst_valid.
  induction p as [ | i p]; simpl; intros m1 d H; auto.
  intros H0 H1.
  destruct (inst_run ge i m1 m1) eqn: Heqov; eauto.
  congruence.
Qed.

Lemma bblock_smem_valid p m0 m1:
  run ge p m0 = Some m1 ->
  pre (bblock_smem p) ge m0.
Proof.
  intros; eapply block_smem_rec_valid; eauto.
  unfold smem_empty; simpl. auto.
Qed.

Definition svalid ge d m := pre d ge m /\ forall x, smem_eval ge d x m <> None.

Theorem bblock_smem_simu p1 p2:
  (forall m, svalid ge (bblock_smem p1) m -> svalid ge (bblock_smem p2) m) ->
  (forall m0 x m1, svalid ge (bblock_smem p1) m0 -> smem_eval ge (bblock_smem p1) x m0 = Some m1 ->
                   smem_eval ge (bblock_smem p2) x m0 = Some m1) ->
   bblock_simu ge p1 p2.
Proof.
  Local Hint Resolve bblock_smem_valid bblock_smem_Some_correct1.
  unfold svalid; intros INCL EQUIV m DONTFAIL.
  destruct (run ge p1 m) as [m1|] eqn: RUN1; simpl; try congruence.
  assert (X: forall x, smem_eval ge (bblock_smem p1) x m = Some (m1 x)); eauto.
  eapply bblock_smem_Some_correct2; eauto.
  + destruct (INCL m); intuition eauto.
    congruence.
  + intro x; apply EQUIV; intuition eauto.
    congruence.
Qed.

Lemma svalid_set_decompose_1 d t x m:
  svalid ge (smem_set d x t) m -> svalid ge d m.
Proof.
  unfold svalid; intros ((PRE1 & PRE2) & VALID); split.
  + intuition.
  + intros x0 H. case (R.eq_dec x x0).
    * intuition congruence.
    * intros DIFF; eapply VALID. erewrite set_spec_diff; eauto.
Qed.

Lemma svalid_set_decompose_2 d t x m:
  svalid ge (smem_set d x t) m -> term_eval ge t m <> None.
Proof.
  unfold svalid; intros ((PRE1 & PRE2) & VALID) H.
  generalize (VALID x); autorewrite with dict_rw.
  tauto.
Qed.

Lemma svalid_set_proof d x t m:
  svalid ge d m -> term_eval ge t m <> None -> svalid ge (smem_set d x t) m.
Proof.
  unfold svalid; intros (PRE & VALID) PREt. split.
  + split; auto.
  + intros x0; case (R.eq_dec x x0).
    - intros; subst; autorewrite with dict_rw. auto.
    - intros. rewrite set_spec_diff; auto. 
Qed.

End SIMU_THEORY.

End SimuTheory.

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