(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*                                                             *)
(*  Copyright VERIMAG. All rights reserved.                    *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** A theory for checking/proving simulation by symbolic execution.

*)


Require Coq.Logic.FunctionalExtensionality. (* not really necessary -- see lemma at the end *)
Require Setoid. (* in order to rewrite <-> *)
Require Export AbstractBasicBlocksDef.
Require Import List.
Require Import ImpPrelude.
Import HConsingDefs.


Module SimuTheory (L: SeqLanguage).

Export L.
Export LP.

Inductive term :=
  | Input (x:R.t)
  | App (o: op) (l: list_term)
with list_term :=
  | LTnil
  | LTcons (t:term) (l:list_term)
  .

Fixpoint term_eval (ge: genv) (t: term) (m: mem): option value :=
  match t with
  | Input x => Some (m x)
  | App o l =>
     match list_term_eval ge l m with
     | Some v => op_eval ge o v
     | _ => None
     end
  end
with list_term_eval ge (l: list_term) (m: mem) {struct l}: option (list value) :=
  match l with
  | LTnil => Some nil
  | LTcons t l' => 
    match term_eval ge t m, list_term_eval ge l' m with
    | Some v, Some lv => Some (v::lv)
    | _, _ => None
    end
  end.

(* the symbolic memory:
  - pre: pre-condition expressing that the computation has not yet abort on a None.
  - post: the post-condition for each pseudo-register 
*)
Record smem:= {pre: genv -> mem -> Prop; post:> R.t -> term}.

(** initial symbolic memory *)
Definition smem_empty := {| pre:=fun _ _ => True; post:=(fun x => Input x) |}.

Fixpoint exp_term (e: exp) (d old: smem) : term :=
  match e with
  | PReg x => d x
  | Op o le => App o (list_exp_term le d old)
  | Old e => exp_term e old old
  end
with list_exp_term (le: list_exp) (d old: smem) : list_term :=
  match le with
  | Enil => LTnil
  | Econs e le' => LTcons (exp_term e d old) (list_exp_term le' d old)
  | LOld le => list_exp_term le old old
  end.


(** assignment of the symbolic memory *)
Definition smem_set (d:smem) x (t:term) := 
  {| pre:=(fun ge m => (term_eval ge (d x) m) <> None /\ (d.(pre) ge m));
     post:=fun y => if R.eq_dec x y then t else d y |}.

Section SIMU_THEORY.

Variable ge: genv.

Lemma set_spec_eq d x t m:
 term_eval ge (smem_set d x t x) m = term_eval ge t m.
Proof.
  unfold smem_set; simpl; case (R.eq_dec x x); try congruence.
Qed.

Lemma set_spec_diff d x y t m:
  x <> y -> term_eval ge (smem_set d x t y) m = term_eval ge (d y) m.
Proof.
  unfold smem_set; simpl; case (R.eq_dec x y); try congruence.
Qed.

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

Local Hint Resolve inst_smem_pre_monotonic bblock_smem_pre_monotonic: core.

Lemma term_eval_exp e (od:smem) m0 old:
  (forall x, term_eval ge (od x) m0 = Some (old x)) ->
  forall (d:smem) m1,
   (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
    term_eval ge (exp_term e d od) m0 = exp_eval ge e m1 old.
Proof.
  intro H.
  induction e using exp_mut with
    (P0:=fun l => forall (d:smem) m1, (forall x, term_eval ge (d x) m0 = Some (m1 x)) -> list_term_eval ge (list_exp_term l d od) m0 = list_exp_eval ge l m1 old);
  simpl; auto.
  - intros; erewrite IHe; eauto.
  - intros. erewrite IHe, IHe0; eauto. 
Qed.

Lemma inst_smem_abort i m0 x old: forall (d:smem),
    pre (inst_smem i d old) ge m0 ->
    term_eval ge (d x) m0 = None ->
    term_eval ge (inst_smem i d old x) m0 = None.
Proof.
  induction i as [|[y e] i IHi]; simpl; auto.
  intros d VALID H; erewrite IHi; eauto. clear IHi.
  unfold smem_set; simpl; destruct (R.eq_dec y x); auto.
  subst;
  generalize (inst_smem_pre_monotonic _ _ _ _ VALID); clear VALID.
  unfold smem_set; simpl. intuition congruence.
Qed.

Lemma block_smem_rec_abort p m0 x: forall d,
    pre (bblock_smem_rec p d) ge m0 ->
    term_eval ge (d x) m0 = None ->
    term_eval ge (bblock_smem_rec p d x) m0 = None.
Proof.
  induction p; simpl; auto.
  intros d VALID H; erewrite IHp; eauto. clear IHp.
  eapply inst_smem_abort; eauto.
Qed.

Lemma inst_smem_Some_correct1 i m0 old (od:smem): 
  (forall x, term_eval ge (od x) m0 = Some (old x)) ->
  forall (m1 m2: mem) (d: smem), 
  inst_run ge i m1 old = Some m2 -> 
  (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
   forall x, term_eval ge (inst_smem i d od x) m0 = Some (m2 x).
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    destruct (exp_eval ge e m1 old) eqn:Heqov; try congruence.
    refine (IHi _ _ _ _ _ _); eauto.
    clear x0; intros x0.
    unfold assign, smem_set; simpl. destruct (R.eq_dec x x0); auto.
    subst; erewrite term_eval_exp; eauto.
Qed.

Lemma bblocks_smem_rec_Some_correct1 p m0: forall (m1 m2: mem) (d: smem), 
 run ge p m1 = Some m2 -> 
  (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
  forall x, term_eval ge (bblock_smem_rec p d x) m0 = Some (m2 x).
Proof.
  Local Hint Resolve inst_smem_Some_correct1: core.
  induction p as [ | i p]; simpl; intros m1 m2 d H.
  - inversion_clear H; eauto.
  - intros H0 x0.
    destruct (inst_run ge i m1 m1) eqn: Heqov.
    + refine (IHp _ _ _ _ _ _); eauto.
    + inversion H. 
Qed.

Lemma bblock_smem_Some_correct1 p m0 m1:
   run ge p m0 = Some m1
   -> forall x, term_eval ge (bblock_smem p x) m0 = Some (m1 x).
Proof.
  intros; eapply bblocks_smem_rec_Some_correct1; eauto.
Qed.

Lemma inst_smem_None_correct i m0 old (od: smem):
   (forall x, term_eval ge (od x) m0 = Some (old x)) ->
  forall m1 d, pre (inst_smem i d od) ge m0 ->
   (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
  inst_run ge i m1 old = None -> exists x, term_eval ge (inst_smem i d od x) m0 = None.
Proof.
  intro X; induction i as [|[x e] i IHi]; simpl; intros m1 d.
  - discriminate.
  - intros VALID H0.
    destruct (exp_eval ge e m1 old) eqn: Heqov.
    + refine (IHi _ _ _ _); eauto.
      intros x0; unfold assign, smem_set; simpl. destruct (R.eq_dec x x0); auto.
      subst; erewrite term_eval_exp; eauto.
    + intuition.
      constructor 1 with (x:=x); simpl.
      apply inst_smem_abort; auto.
      rewrite set_spec_eq. 
      erewrite term_eval_exp; eauto.
Qed.

Lemma inst_smem_Some_correct2 i m0 old (od: smem):
  (forall x, term_eval ge (od x) m0 = Some (old x)) ->
  forall (m1 m2: mem) d, 
  pre (inst_smem i d od) ge m0 ->
  (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
  (forall x, term_eval ge (inst_smem i d od x) m0 = Some (m2 x)) ->
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
      intros x0; unfold assign, smem_set; simpl; destruct (R.eq_dec x x0); auto.
      subst; erewrite term_eval_exp; eauto.
    + generalize (H x).
      rewrite inst_smem_abort; discriminate || auto.
      rewrite set_spec_eq. 
      erewrite term_eval_exp; eauto.
Qed.

Lemma bblocks_smem_rec_Some_correct2 p m0: forall (m1 m2: mem) d, 
  pre (bblock_smem_rec p d) ge m0 ->
  (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
  (forall x, term_eval ge (bblock_smem_rec p d x) m0 = Some (m2 x)) ->
    res_eq (Some m2) (run ge p m1).
Proof.
  induction p as [|i p]; simpl; intros m1 m2 d VALID H0.
  - intros H; eapply ex_intro; intuition eauto.
    generalize (H0 x); rewrite H.
    congruence.
  - intros H.
     destruct (inst_run ge i m1 m1) eqn: Heqom.
    + refine (IHp _ _ _ _ _ _); eauto.
    + assert (X: exists x, term_eval ge (inst_smem i d d x) m0 = None).
      { eapply inst_smem_None_correct; eauto. }
      destruct X as [x H1].
      generalize (H x).
      erewrite block_smem_rec_abort; eauto.
      congruence.
Qed.

Lemma bblock_smem_Some_correct2 p m0 m1:
  pre (bblock_smem p) ge m0 ->
  (forall x, term_eval ge (bblock_smem p x) m0 = Some (m1 x))
  -> res_eq (Some m1) (run ge p m0).
Proof.
  intros; eapply bblocks_smem_rec_Some_correct2; eauto.
Qed.

Lemma inst_valid i m0 old (od:smem):
  (forall x, term_eval ge (od x) m0 = Some (old x)) ->
  forall (m1 m2: mem) (d: smem), 
  pre d ge m0 ->
  inst_run ge i m1 old = Some m2 ->
  (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
   pre (inst_smem i d od) ge m0.
Proof.
  induction i as [|[x e] i IHi]; simpl; auto.
  intros Hold m1 m2 d VALID0 H Hm1.
  destruct (exp_eval ge e m1 old) eqn: Heq; simpl; try congruence.
  eapply IHi; eauto.
  + unfold smem_set in * |- *; simpl. 
    rewrite Hm1; intuition congruence.
  + intros x0. unfold assign, smem_set; simpl; destruct (R.eq_dec x x0); auto.
    subst; erewrite term_eval_exp; eauto.
Qed.


Lemma block_smem_rec_valid p m0: forall (m1 m2: mem) (d:smem), 
  pre d ge m0 ->
  run ge p m1 = Some m2 -> 
  (forall x, term_eval ge (d x) m0 = Some (m1 x)) ->
  pre (bblock_smem_rec p d) ge m0.
Proof.
  Local Hint Resolve inst_valid: core.
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

Definition smem_valid ge d m := pre d ge m /\ forall x, term_eval ge (d x) m <> None.

Definition smem_simu (d1 d2: smem): Prop :=
     (forall m, smem_valid ge d1 m -> smem_valid ge d2 m)
  /\ (forall m0 x, smem_valid ge d1 m0 -> 
                   term_eval ge (d1 x) m0 = term_eval ge (d2 x) m0).


Theorem bblock_smem_simu p1 p2:
   smem_simu (bblock_smem p1) (bblock_smem p2) ->
   bblock_simu ge p1 p2.
Proof.
  Local Hint Resolve bblock_smem_valid bblock_smem_Some_correct1: core.
  intros (INCL & EQUIV) m DONTFAIL; unfold smem_valid in * |-.
  destruct (run ge p1 m) as [m1|] eqn: RUN1; simpl; try congruence.
  assert (X: forall x, term_eval ge (bblock_smem p1 x) m = Some (m1 x)); eauto.
  eapply bblock_smem_Some_correct2; eauto.
  + destruct (INCL m); intuition eauto.
    congruence.
  + intro x; erewrite <- EQUIV; intuition eauto.
    congruence.
Qed.

Lemma smem_valid_set_decompose_1 d t x m:
  smem_valid ge (smem_set d x t) m -> smem_valid ge d m.
Proof.
  unfold smem_valid; intros ((PRE1 & PRE2) & VALID); split.
  + intuition.
  + intros x0 H. case (R.eq_dec x x0).
    * intuition congruence.
    * intros DIFF; eapply VALID. erewrite set_spec_diff; eauto.
Qed.

Lemma smem_valid_set_decompose_2 d t x m:
  smem_valid ge (smem_set d x t) m -> term_eval ge t m <> None.
Proof.
  unfold smem_valid; intros ((PRE1 & PRE2) & VALID) H.
  generalize (VALID x); rewrite set_spec_eq.
  tauto.
Qed.

Lemma smem_valid_set_proof d x t m:
  smem_valid ge d m -> term_eval ge t m <> None -> smem_valid ge (smem_set d x t) m.
Proof.
  unfold smem_valid; intros (PRE & VALID) PREt. split.
  + split; auto.
  + intros x0; unfold smem_set; simpl; case (R.eq_dec x x0); intros; subst; auto.
Qed.


End SIMU_THEORY.

(** REMARKS: more abstract formulation of the proof... 
    but relying on functional_extensionality.
*)
Definition smem_correct ge (d: smem) (m: mem) (om: option mem): Prop:=
   forall m', om=Some m' <-> (d.(pre) ge m /\ forall x, term_eval ge (d x) m = Some (m' x)).

Lemma bblock_smem_correct ge p m: smem_correct ge (bblock_smem p) m (run ge p m).
Proof.
  unfold smem_correct; simpl; intros m'; split.
  + intros; split.
    * eapply bblock_smem_valid; eauto.
    * eapply bblock_smem_Some_correct1; eauto.
  + intros (H1 & H2).
    destruct (bblock_smem_Some_correct2 ge p m m') as (m2 & X & Y); eauto.
    rewrite X. f_equal.
    apply FunctionalExtensionality.functional_extensionality; auto.
Qed.

End SimuTheory.
