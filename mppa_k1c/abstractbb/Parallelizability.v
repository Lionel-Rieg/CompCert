(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** Parallel Semantics of Abstract Basic Blocks and parallelizability test.
*)

Require Setoid. (* in order to rewrite <-> *)
Require Export AbstractBasicBlocksDef.

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

Require Import Sorting.Permutation.
Require Import Bool.
Local Open Scope lazy_bool_scope.


Module ParallelSemantics (L: SeqLanguage).

Export L.
Local Open Scope list.

Section PARALLEL.
Variable ge: genv.

(* parallel run of a inst *)
Fixpoint inst_prun (i: inst) (m tmp old: mem): option mem :=
  match i with
  | nil => Some m
  | (x, e)::i' =>
     match exp_eval ge e tmp old with
     | Some v' => inst_prun i' (assign m x v') (assign tmp x v') old
     | None => None
     end
  end.

(* [inst_prun] is generalization of [inst_run] *)
Lemma inst_run_prun i: forall m old,
  inst_run ge i m old = inst_prun i m m old.
Proof.
  induction i as [|[y e] i']; simpl; auto.
  intros m old; destruct (exp_eval ge e m old); simpl; auto.
Qed.


(* parallel run of a bblock -- with in-order writes *)
Fixpoint prun_iw (p: bblock) m old: option mem :=
  match p with
  | nil => Some m
  | i::p' =>
    match inst_prun i m old old with
    | Some m1 => prun_iw p' m1 old
    | None => None
    end
  end.

(* non-deterministic parallel run, due to arbitrary writes order *)
Definition prun (p: bblock) m (om: option mem) := exists p', res_eq om (prun_iw p' m m) /\ Permutation p p'.


(* a few lemma on equality *)

Lemma inst_prun_equiv i old: forall m1 m2 tmp,
  (forall x, m1 x = m2 x) ->
  res_eq (inst_prun i m1 tmp old) (inst_prun i m2 tmp old).
Proof.
  induction i as [|[x e] i']; simpl; eauto.
  intros m1 m2 tmp H; destruct (exp_eval ge e tmp old); simpl; auto.
  eapply IHi'; unfold assign. intros; destruct (R.eq_dec x x0); auto.
Qed.

Lemma prun_iw_equiv p: forall m1 m2 old, 
  (forall x, m1 x = m2 x) ->
  res_eq (prun_iw p m1 old) (prun_iw p m2 old).
Proof.
  induction p as [|i p']; simpl; eauto.
  - intros m1 m2 old H.
    generalize (inst_prun_equiv i old m1 m2 old H);
    destruct (inst_prun i m1 old old); simpl.
    + intros (m3 & H3 & H4); rewrite H3; simpl; eauto.
    + intros H1; rewrite H1; simpl; auto.
Qed.


Lemma prun_iw_app p1: forall m1 old p2,
   prun_iw (p1++p2) m1 old = 
     match prun_iw p1 m1 old with 
     | Some m2 => prun_iw p2 m2 old 
     | None => None
     end.
Proof.
   induction p1; simpl; try congruence.
   intros; destruct (inst_prun _ _ _); simpl; auto.
Qed.

Lemma prun_iw_app_None p1: forall m1 old p2,
   prun_iw p1 m1 old = None ->
   prun_iw (p1++p2) m1 old = None.
Proof.
   intros m1 old p2 H; rewrite prun_iw_app. rewrite H; auto.
Qed.

Lemma prun_iw_app_Some p1: forall m1 old m2 p2,
   prun_iw p1 m1 old = Some m2 ->
   prun_iw (p1++p2) m1 old = prun_iw p2 m2 old.
Proof.
   intros m1 old m2 p2 H; rewrite prun_iw_app. rewrite H; auto.
Qed.

End PARALLEL.
End ParallelSemantics.



Fixpoint notIn {A} (x: A) (l:list A): Prop :=
  match l with
  | nil => True
  | a::l' => x <> a /\ notIn x l'
  end.

Lemma notIn_iff A (x:A) l: (~List.In x l) <-> notIn x l.
Proof.
  induction l; simpl; intuition.
Qed.

Lemma notIn_app A (x:A) l1: forall l2, notIn x (l1++l2) <-> (notIn x l1 /\ notIn x l2).
Proof.
  induction l1; simpl.
  - intuition.
  - intros; rewrite IHl1. intuition.
Qed.


Lemma In_Permutation A (l1 l2: list A): Permutation l1 l2 -> forall x, In x l1 -> In x l2.
Proof.
  induction 1; simpl; intuition.
Qed.

Lemma Permutation_incl A (l1 l2: list A): Permutation l1 l2 -> incl l1 l2.
Proof.
  unfold incl; intros; eapply In_Permutation; eauto.
Qed.

Lemma notIn_incl A (l1 l2: list A) x: incl l1 l2 -> notIn x l2 -> notIn x l1.
Proof.
  unfold incl; rewrite <- ! notIn_iff; intuition.
Qed.


Definition disjoint {A: Type} (l l':list A) : Prop := forall x, In x l -> notIn x l'.

Lemma disjoint_sym_imp A (l1 l2: list A): disjoint l1 l2 -> disjoint l2 l1.
Proof.
  unfold disjoint. intros H x H1. generalize (H x). rewrite <- !notIn_iff. intuition.
Qed.

Lemma disjoint_sym A (l1 l2: list A): disjoint l1 l2 <-> disjoint l2 l1.
Proof.
  constructor 1; apply disjoint_sym_imp; auto.
Qed.


Lemma disjoint_cons_l A (x:A) (l1 l2: list A): disjoint (x::l1) l2 <-> (notIn x l2) /\ (disjoint l1 l2).
Proof.
  unfold disjoint. simpl; intuition subst; auto. 
Qed.

Lemma disjoint_cons_r A (x:A) (l1 l2: list A): disjoint l1 (x::l2) <-> (notIn x l1) /\ (disjoint l1 l2).
Proof.
  rewrite disjoint_sym, disjoint_cons_l, disjoint_sym; intuition.
Qed.

Lemma disjoint_app_r A (l l1 l2: list A): disjoint l (l1++l2) <-> (disjoint l l1 /\ disjoint l l2).
Proof.
  unfold disjoint. intuition. 
  - generalize (H x H0). rewrite notIn_app; intuition.
  - generalize (H x H0). rewrite notIn_app; intuition.
  - rewrite notIn_app; intuition.
Qed.

Lemma disjoint_app_l A (l l1 l2: list A): disjoint (l1++l2) l <-> (disjoint l1 l /\ disjoint l2 l).
Proof.
  rewrite disjoint_sym,  disjoint_app_r; intuition; rewrite disjoint_sym; auto.
Qed.

Lemma disjoint_incl_r A (l1 l2: list A): incl l1 l2 -> forall l, disjoint l l2 -> disjoint l l1.
Proof.
  unfold disjoint. intros; eapply notIn_incl; eauto.
Qed.

Lemma disjoint_incl_l A (l1 l2: list A): incl l1 l2 -> forall l, disjoint l2 l -> disjoint l1 l.
Proof.
  intros; rewrite disjoint_sym. eapply disjoint_incl_r; eauto. rewrite disjoint_sym; auto.
Qed.


Module ParallelizablityChecking (L: SeqLanguage).

Include ParallelSemantics L.

Section PARALLELI.
Variable ge: genv.

(** * Preliminary notions on frames *)

Lemma notIn_dec (x: R.t) l : { notIn x l } + { In x l }.
Proof.
  destruct (In_dec R.eq_dec x l). constructor 2; auto.
  constructor 1; rewrite <- notIn_iff. auto.
Qed.

Fixpoint frame_assign m1 (f: list R.t) m2 := 
  match f with
  | nil => m1
  | x::f' => frame_assign (assign m1 x (m2 x)) f' m2  
  end.

Lemma frame_assign_def f: forall m1 m2 x,
   frame_assign m1 f m2 x = if notIn_dec x f then m1 x else m2 x.
Proof.
  induction f as [|y f] ; simpl; auto.
  - intros; destruct (notIn_dec x []); simpl in *; tauto.
  - intros; rewrite IHf; destruct (notIn_dec x (y::f)); simpl in *.
    + destruct (notIn_dec x f); simpl in *; intuition.
      rewrite assign_diff; auto.
      rewrite <- notIn_iff in *; intuition.
    + destruct (notIn_dec x f); simpl in *; intuition subst.
      rewrite assign_eq; auto.
      rewrite <- notIn_iff in *; intuition.
Qed.

Lemma frame_assign_In m1 f m2 x:
   In x f -> frame_assign m1 f m2 x = m2 x.
Proof.
  intros; rewrite frame_assign_def; destruct (notIn_dec x f); auto.
  rewrite <- notIn_iff in *; intuition.
Qed.

Lemma frame_assign_notIn m1 f m2 x:
   notIn x f -> frame_assign m1 f m2 x = m1 x.
Proof.
  intros; rewrite frame_assign_def; destruct (notIn_dec x f); auto.
  rewrite <- notIn_iff in *; intuition.
Qed.

Definition frame_eq (frame: R.t -> Prop) (om1 om2: option mem): Prop :=
  match om1 with
  | Some m1 => exists m2, om2 = Some m2 /\ forall x, (frame x) -> m1 x = m2 x 
  | None => om2 = None
  end.

Lemma frame_eq_list_split f1 (f2: R.t -> Prop) om1 om2:
 frame_eq (fun x => In x f1) om1 om2 ->
 (forall m1 m2 x, om1 = Some m1 -> om2 = Some m2 -> f2 x -> notIn x f1 -> m1 x = m2 x) ->
 frame_eq f2 om1 om2.
Proof.
  unfold frame_eq; destruct om1 as [ m1 | ]; simpl; auto.
  intros (m2 & H0 & H1); subst.
  intros H.
  eexists; intuition eauto.
  destruct (notIn_dec x f1); auto.
Qed. 

(*
Lemma frame_eq_res_eq f om1 om2:
 frame_eq (fun x => In x f) om1 om2 ->
 (forall m1 m2 x, om1 = Some m1 -> om2 = Some m2 -> notIn x f -> m1 x = m2 x) ->
 res_eq om1 om2.
Proof.
  intros H H0; lapply (frame_eq_list_split f (fun _ => True) om1 om2 H); eauto.
  clear H H0; unfold frame_eq, res_eq. destruct om1; simpl; firstorder.
Qed.
*)

(** * Writing frames *)

Fixpoint inst_wframe(i:inst): list R.t := 
  match i with
  | nil => nil
  | a::i' => (fst a)::(inst_wframe i') 
  end.

Lemma inst_wframe_correct i m' old: forall m tmp, 
  inst_prun ge i m tmp old = Some m' -> 
  forall x, notIn x (inst_wframe i) -> m' x  = m x.
Proof.
  induction i as [|[y e] i']; simpl.
  - intros m tmp H x H0; inversion_clear H; auto.
  - intros m tmp H x (H1 & H2); destruct (exp_eval ge e tmp old); simpl; try congruence.
    cutrewrite (m x = assign m y v x); eauto.
    rewrite assign_diff; auto.
Qed.

Lemma inst_prun_fequiv i old: forall m1 m2 tmp, 
  frame_eq (fun x => In x (inst_wframe i)) (inst_prun ge i m1 tmp old) (inst_prun ge i m2 tmp old).
Proof.
  induction i as [|[y e] i']; simpl.
  - intros m1 m2 tmp; eexists; intuition eauto.
  - intros m1 m2 tmp. destruct (exp_eval ge e tmp old); simpl; auto.
    eapply frame_eq_list_split; eauto. clear IHi'.
    intros m1' m2' x H1 H2.
    lapply (inst_wframe_correct i' m1' old (assign m1 y v) (assign tmp y v)); eauto.
    lapply (inst_wframe_correct i' m2' old (assign m2 y v) (assign tmp y v)); eauto.
    intros Xm2 Xm1 H H0. destruct H. 
    + subst. rewrite Xm1, Xm2; auto. rewrite !assign_eq. auto.
    + rewrite <- notIn_iff in H0; tauto.
Qed.

Lemma inst_prun_None i m1 m2 tmp old: 
  inst_prun ge i m1 tmp old = None -> 
  inst_prun ge i m2 tmp old = None.
Proof.
  intros H; generalize (inst_prun_fequiv i old m1 m2 tmp).
  rewrite H; simpl; auto.
Qed.

Lemma inst_prun_Some i m1 m2 tmp old m1': 
  inst_prun ge i m1 tmp old = Some m1' -> 
  res_eq (Some (frame_assign m2 (inst_wframe i) m1')) (inst_prun ge i m2 tmp old).
Proof.
  intros H; generalize (inst_prun_fequiv i old m1 m2 tmp).
  rewrite H; simpl.
  intros (m2' & H1 & H2).
  eexists; intuition eauto.
  rewrite frame_assign_def.
  lapply (inst_wframe_correct i m2' old m2 tmp); eauto.
  destruct (notIn_dec x (inst_wframe i)); auto.
  intros X; rewrite X; auto.
Qed.

Fixpoint bblock_wframe(p:bblock): list R.t := 
  match p with
  | nil => nil
  | i::p' => (inst_wframe i)++(bblock_wframe p') 
  end.

Local Hint Resolve Permutation_app_head Permutation_app_tail Permutation_app_comm: core.

Lemma bblock_wframe_Permutation p p': 
 Permutation p p' -> Permutation (bblock_wframe p)  (bblock_wframe p').
Proof.
  induction 1 as [|i p p'|i1 i2 p|p1 p2 p3]; simpl; auto.
  - rewrite! app_assoc; auto.
  - eapply Permutation_trans; eauto.
Qed.

(*
Lemma bblock_wframe_correct p m' old: forall m, 
  prun_iw p m old = Some m' -> 
  forall x, notIn x (bblock_wframe p) -> m' x = m x.
Proof.
  induction p as [|i p']; simpl.
  - intros m H; inversion_clear H; auto.
  - intros m H x; rewrite notIn_app; intros (H1 & H2). 
    remember (inst_prun i m old old) as om.
    destruct om as [m1|]; simpl.
    + eapply eq_trans.
      eapply IHp'; eauto.
      eapply inst_wframe_correct; eauto.
    + inversion H.
Qed.

Lemma prun_iw_fequiv p old: forall m1 m2, 
  frame_eq (fun x => In x (bblock_wframe p)) (prun_iw p m1 old) (prun_iw p m2 old).
Proof.
  induction p as [|i p']; simpl.
  - intros m1 m2; eexists; intuition eauto.
  - intros m1 m2; generalize (inst_prun_fequiv i old m1 m2 old).
    remember (inst_prun i m1 old old) as om.
    destruct om as [m1'|]; simpl.
    + intros (m2' & H1 & H2). rewrite H1; simpl.
    eapply frame_eq_list_split; eauto. clear IHp'.
    intros m1'' m2'' x H3 H4. rewrite in_app_iff.
    intros X X2. assert (X1: In x (inst_wframe i)). { destruct X; auto. rewrite <- notIn_iff in X2; tauto. }
    clear X.
    lapply (bblock_wframe_correct p' m1'' old m1'); eauto.
    lapply (bblock_wframe_correct p' m2'' old m2'); eauto.
    intros Xm2' Xm1'. 
    rewrite Xm1', Xm2'; auto.
    + intro H; rewrite H; simpl; auto.
Qed.

Lemma prun_iw_equiv p m1 m2 old: 
  (forall x, notIn x (bblock_wframe p) -> m1 x = m2 x) ->
  res_eq (prun_iw p m1 old) (prun_iw p m2 old).
Proof.
  intros; eapply frame_eq_res_eq.
  eapply prun_iw_fequiv.
  intros m1' m2' x H1 H2 H0.Require
  lapply (bblock_wframe_correct p m1' old m1); eauto.
  lapply (bblock_wframe_correct p m2' old m2); eauto.
  intros X2 X1; rewrite X1, X2; auto.
Qed.
*)

(** * Checking that parallel semantics is deterministic *)

Fixpoint is_det (p: bblock): Prop :=
  match p with
  | nil => True
  | i::p' =>
       disjoint (inst_wframe i) (bblock_wframe p') (* no WRITE-AFTER-WRITE *)
    /\ is_det p'
  end.

Lemma is_det_Permutation p p': 
 Permutation p p' -> is_det p -> is_det p'.
Proof.
  induction 1; simpl; auto.
  - intros; intuition. eapply disjoint_incl_r. 2: eauto.
    eapply Permutation_incl. eapply Permutation_sym. 
    eapply bblock_wframe_Permutation; auto.
  - rewrite! disjoint_app_r in * |- *. intuition.
    rewrite disjoint_sym; auto. 
Qed.

Theorem is_det_correct p p':
  Permutation p p' -> 
  is_det p -> 
  forall m old, res_eq (prun_iw ge p m old) (prun_iw ge p' m old).
Proof.
  induction 1 as [ | i p p' | i1 i2 p | p1 p2 p3 ]; simpl; eauto.
  - intros [H0 H1] m old.
    remember (inst_prun ge i m old old) as om0.
    destruct om0 as [ m0 | ]; simpl; auto.
  - rewrite disjoint_app_r.
    intros ([Z1 Z2] & Z3 & Z4) m old.
    remember (inst_prun ge i2 m old old) as om2.
    destruct om2 as [ m2 | ]; simpl; auto.
    + remember (inst_prun ge i1 m old old) as om1.
      destruct om1 as [ m1 | ]; simpl; auto.
      * lapply (inst_prun_Some i2 m m1 old old m2); simpl; auto.
        lapply (inst_prun_Some i1 m m2 old old m1); simpl; auto.
        intros (m1' & Hm1' & Xm1') (m2' & Hm2' & Xm2').
        rewrite Hm1', Hm2'; simpl.
        eapply prun_iw_equiv.
        intros x; rewrite <- Xm1', <- Xm2'. clear Xm2' Xm1' Hm1' Hm2' m1' m2'.
        rewrite frame_assign_def.
        rewrite disjoint_sym in Z1; unfold disjoint in Z1.
        destruct (notIn_dec x (inst_wframe i1)) as [ X1 | X1 ].
        { rewrite frame_assign_def; destruct (notIn_dec x (inst_wframe i2)) as [ X2 | X2 ]; auto.
          erewrite (inst_wframe_correct i2 m2 old m old); eauto.
          erewrite (inst_wframe_correct i1 m1 old m old); eauto.
        }
        rewrite frame_assign_notIn; auto.
     * erewrite inst_prun_None; eauto. simpl; auto.
   + remember (inst_prun ge i1 m old old) as om1.
     destruct om1 as [ m1 | ]; simpl; auto.
     erewrite inst_prun_None; eauto.
  - intros; eapply res_eq_trans.
    eapply IHPermutation1; eauto.
    eapply IHPermutation2; eauto.
    eapply is_det_Permutation; eauto.
Qed.

(** * Standard Frames *)

Fixpoint exp_frame (e: exp): list R.t :=
  match e with
  | PReg x => x::nil
  | Op o le => list_exp_frame le
  | Old e => exp_frame e
  end
with list_exp_frame (le: list_exp): list R.t :=
  match le with
  | Enil => nil
  | Econs e le' => exp_frame e ++ list_exp_frame le'
  | LOld le => list_exp_frame le
  end.

Lemma exp_frame_correct e old1 old2: 
  (forall x, In x (exp_frame e) -> old1 x = old2 x) ->
  forall m1 m2, (forall x, In x (exp_frame e) -> m1 x = m2 x) ->
   (exp_eval ge e m1 old1)=(exp_eval ge e m2 old2).
Proof.
  induction e using exp_mut with (P0:=fun l => (forall x, In x (list_exp_frame l) -> old1 x = old2 x) -> forall m1 m2, (forall x, In x (list_exp_frame l) -> m1 x = m2 x) ->
   (list_exp_eval ge l m1 old1)=(list_exp_eval ge l m2 old2)); simpl; auto.
  - intros H1 m1 m2 H2; rewrite H2; auto.
  - intros H1 m1 m2 H2; erewrite IHe; eauto.
  - intros H1 m1 m2 H2; erewrite IHe, IHe0; eauto; 
    intros; (eapply H1 || eapply H2); rewrite in_app_iff; auto.
Qed.

Fixpoint inst_frame (i: inst): list R.t :=
  match i with
  | nil => nil
  | a::i' => (fst a)::(exp_frame (snd a) ++ inst_frame i') 
  end.

Lemma inst_wframe_frame i x: In x (inst_wframe i) -> In x (inst_frame i).
Proof.
  induction i as [ | [y e] i']; simpl; intuition.
Qed.


Lemma inst_frame_correct i wframe old1 old2: forall m tmp1 tmp2,
  (disjoint (inst_frame i) wframe) ->
  (forall x, notIn x wframe -> old1 x = old2 x) ->
  (forall x, notIn x wframe -> tmp1 x = tmp2 x) ->
  inst_prun ge i m tmp1 old1 = inst_prun ge i m tmp2 old2.
Proof.
  induction i as [|[x e] i']; simpl; auto.
  intros m tmp1 tmp2; rewrite disjoint_cons_l, disjoint_app_l.
  intros (H1 & H2 & H3) H6 H7.
  cutrewrite (exp_eval ge e tmp1 old1 = exp_eval ge e tmp2 old2).
  - destruct (exp_eval ge e tmp2 old2); auto.
    eapply IHi'; eauto. 
    simpl; intros x0 H0; unfold assign. destruct (R.eq_dec x x0); simpl; auto. 
  - unfold disjoint in H2; apply exp_frame_correct.
    intros;apply H6; auto.
    intros;apply H7; auto.
Qed.

(** * Parallelizability *)

Fixpoint pararec (p: bblock) (wframe: list R.t): Prop :=
  match p with
  | nil => True
  | i::p' =>
       disjoint (inst_frame i) wframe (* no USE-AFTER-WRITE *)
    /\ pararec p' ((inst_wframe i) ++ wframe)
  end.

Lemma pararec_disjoint (p: bblock): forall wframe, pararec p wframe -> disjoint (bblock_wframe p) wframe.
Proof.
  induction p as [|i p']; simpl.
  - unfold disjoint; simpl; intuition.
  - intros wframe [H0 H1]; rewrite disjoint_app_l. 
    generalize (IHp' _ H1).
    rewrite disjoint_app_r. intuition. 
    eapply disjoint_incl_l. 2: eapply H0.
    unfold incl. eapply inst_wframe_frame; eauto.
Qed.

Lemma pararec_det p: forall wframe, pararec p wframe -> is_det p.
Proof.
  induction p as [|i p']; simpl; auto.
  intros wframe [H0 H1]. generalize (pararec_disjoint _ _ H1). rewrite disjoint_app_r.
  intuition. 
  - apply disjoint_sym; auto.
  - eapply IHp'. eauto.
Qed.

Lemma pararec_correct p old: forall wframe m,
  pararec p wframe -> 
  (forall x, notIn x wframe -> m x = old x) ->
  run ge p m = prun_iw ge p m old.
Proof.
  elim p; clear p; simpl; auto.
  intros i p' X wframe m [H H0] H1.
  erewrite inst_run_prun, inst_frame_correct; eauto.
  remember (inst_prun ge i m old old) as om0.
  destruct om0 as [m0 | ]; try congruence.
  eapply X; eauto.
  intro x; rewrite notIn_app. intros [H3 H4].
  rewrite <- H1; auto.
  eapply inst_wframe_correct; eauto.
Qed.

Definition parallelizable (p: bblock) := pararec p nil.

Theorem parallelizable_correct p m om':
  parallelizable p -> (prun ge p m om' <-> res_eq om' (run ge p m)).
Proof.
  intros H. constructor 1.
  - intros (p' & H0 & H1). eapply res_eq_trans; eauto.
    erewrite pararec_correct; eauto.
    eapply res_eq_sym.
    eapply is_det_correct; eauto.
    eapply pararec_det; eauto.
  - intros; unfold prun. 
    eexists. constructor 1. 2: apply Permutation_refl. 
    erewrite pararec_correct in H0; eauto.
Qed.

End PARALLELI.

End ParallelizablityChecking.


Module Type PseudoRegSet.

Declare Module R: PseudoRegisters.

(** We assume a datatype [t] refining (list R.t)

This data-refinement is given by an abstract "invariant" match_frame below, 
preserved by the following operations.

*)

Parameter t: Type.
Parameter match_frame: t -> (list R.t) -> Prop.

Parameter empty: t.
Parameter empty_match_frame: match_frame empty nil.

Parameter add: R.t -> t -> t.
Parameter add_match_frame: forall s x l, match_frame s l -> match_frame (add x s) (x::l).

Parameter union: t -> t -> t.
Parameter union_match_frame: forall s1 s2 l1 l2, match_frame s1 l1 -> match_frame s2 l2 -> match_frame (union s1 s2) (l1++l2).

Parameter is_disjoint: t -> t -> bool.
Parameter is_disjoint_match_frame: forall s1 s2 l1 l2, match_frame s1 l1 -> match_frame s2 l2 -> (is_disjoint s1 s2)=true -> disjoint l1 l2. 

End PseudoRegSet.


Lemma lazy_andb_bool_true (b1 b2: bool): b1 &&& b2 = true <-> b1 = true /\ b2 = true.
Proof.
  destruct b1, b2; intuition.
Qed.




Module ParallelChecks (L: SeqLanguage) (S:PseudoRegSet with Module R:=L.LP.R).

Include ParallelizablityChecking L.

Section PARALLEL2.
Variable ge: genv.

Local Hint Resolve S.empty_match_frame S.add_match_frame S.union_match_frame S.is_disjoint_match_frame: core.

(** Now, refinement of each operation toward parallelizable *)

Fixpoint inst_wsframe(i:inst): S.t :=
  match i with
  | nil => S.empty
  | a::i' => S.add (fst a) (inst_wsframe i') 
  end.

Lemma inst_wsframe_correct i: S.match_frame (inst_wsframe i) (inst_wframe i).
Proof.
  induction i; simpl; auto.
Qed.

Fixpoint exp_sframe (e: exp): S.t :=
  match e with
  | PReg x => S.add x S.empty
  | Op o le => list_exp_sframe le
  | Old e => exp_sframe e
  end
with list_exp_sframe (le: list_exp): S.t :=
  match le with
  | Enil => S.empty
  | Econs e le' => S.union (exp_sframe e) (list_exp_sframe le')
  | LOld le => list_exp_sframe le
  end.

Lemma exp_sframe_correct e: S.match_frame (exp_sframe e) (exp_frame e).
Proof.
  induction e using exp_mut with (P0:=fun l => S.match_frame (list_exp_sframe l) (list_exp_frame l)); simpl; auto.
Qed.

Fixpoint inst_sframe (i: inst): S.t :=
  match i with
  | nil => S.empty
  | a::i' => S.add (fst a) (S.union (exp_sframe (snd a)) (inst_sframe i'))
  end.

Local Hint Resolve exp_sframe_correct: core.

Lemma inst_sframe_correct i: S.match_frame (inst_sframe i) (inst_frame i).
Proof.
  induction i as [|[y e] i']; simpl; auto.
Qed.

Local Hint Resolve inst_wsframe_correct inst_sframe_correct: core.

Fixpoint is_pararec (p: bblock) (wsframe: S.t): bool :=
  match p with
  | nil => true
  | i::p' =>
       S.is_disjoint (inst_sframe i) wsframe (* no USE-AFTER-WRITE *)
    &&& is_pararec p' (S.union (inst_wsframe i) wsframe)
  end.

Lemma is_pararec_correct (p: bblock): forall s l, S.match_frame s l -> (is_pararec p s)=true -> (pararec p l).
Proof.
  induction p; simpl; auto.
  intros s l H1 H2; rewrite lazy_andb_bool_true in H2. destruct H2 as [H2 H3].
  constructor 1; eauto.
Qed.

Definition is_parallelizable (p: bblock) := is_pararec p S.empty.

Lemma is_para_correct_aux p: is_parallelizable p = true -> parallelizable p.
Proof.
  unfold is_parallelizable, parallelizable; intros; eapply is_pararec_correct; eauto.
Qed.

Theorem is_parallelizable_correct p:
  is_parallelizable p = true -> forall m om', (prun ge p m om' <-> res_eq om' (run ge p m)).
Proof.
  intros; apply parallelizable_correct.
  apply is_para_correct_aux. auto.
Qed.

End PARALLEL2.
End ParallelChecks.




Require Import PArith.
Require Import MSets.MSetPositive.

Module PosPseudoRegSet <: PseudoRegSet with Module R:=Pos.

Module R:=Pos.

(** We assume a datatype [t] refining (list R.t)

This data-refinement is given by an abstract "invariant" match_frame below, 
preserved by the following operations.

*)

Definition t:=PositiveSet.t.

Definition match_frame (s:t) (l:list R.t): Prop
 := forall x, PositiveSet.In x s <-> In x l.

Definition empty:=PositiveSet.empty.

Lemma empty_match_frame: match_frame empty nil.
Proof.
  unfold match_frame, empty, PositiveSet.In; simpl; intuition.
Qed.

Definition add: R.t -> t -> t := PositiveSet.add.

Lemma add_match_frame: forall s x l, match_frame s l -> match_frame (add x s) (x::l).
Proof.
  unfold match_frame, add; simpl. 
  intros s x l H y. rewrite PositiveSet.add_spec, H.
  intuition. 
Qed.

Definition union: t -> t -> t := PositiveSet.union.
Lemma union_match_frame: forall s1 s2 l1 l2, match_frame s1 l1 -> match_frame s2 l2 -> match_frame (union s1 s2) (l1++l2).
Proof.
  unfold match_frame, union. 
  intros s1 s2 l1 l2 H1 H2 x. rewrite PositiveSet.union_spec, H1, H2.
  intuition. 
Qed.

Fixpoint is_disjoint (s s': PositiveSet.t) : bool :=
  match s with
  | PositiveSet.Leaf => true
  | PositiveSet.Node l o r =>
    match s' with
    | PositiveSet.Leaf => true
    | PositiveSet.Node l' o' r' => 
      if (o &&& o') then false else (is_disjoint l l' &&& is_disjoint r r')
    end
  end.

Lemma is_disjoint_spec_true s: forall s', is_disjoint s s' = true -> forall x, PositiveSet.In x s -> PositiveSet.In x s' -> False.
Proof.
  unfold PositiveSet.In; induction s as [ |l IHl o r IHr]; simpl; try discriminate.
  destruct s' as [|l' o' r']; simpl; try discriminate.
  intros X.
  assert (H: ~(o = true /\ o'=true) /\ is_disjoint l l' = true /\ is_disjoint r r'=true).
  { destruct o, o', (is_disjoint l l'), (is_disjoint r r'); simpl in X; intuition. }
  clear X; destruct H as (H & H1 & H2).
  destruct x as [i|i|]; simpl; eauto.
Qed.

Lemma is_disjoint_match_frame: forall s1 s2 l1 l2, match_frame s1 l1 -> match_frame s2 l2 -> (is_disjoint s1 s2)=true -> disjoint l1 l2.
Proof.
  unfold match_frame, disjoint.
  intros s1 s2 l1 l2 H1 H2 H3 x.
  rewrite <- notIn_iff, <- H1, <- H2.
  intros H4 H5; eapply is_disjoint_spec_true; eauto.
Qed.

End PosPseudoRegSet.
