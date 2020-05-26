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

(** Implementation of a symbolic execution of sequential semantics of Abstract Basic Blocks

with imperative hash-consing, and rewriting.

*)

Require Export Impure.ImpHCons.
Export Notations.
Import HConsing.


Require Export SeqSimuTheory.

Require Import PArith.


Local Open Scope impure.

Import ListNotations.
Local Open Scope list_scope.


Module Type ImpParam.

Include LangParam.

Parameter op_eq: op -> op -> ?? bool.

Parameter op_eq_correct: forall o1 o2, 
 WHEN op_eq o1 o2 ~> b THEN
  b=true -> o1 = o2.

End ImpParam.


Module Type ISeqLanguage.

Declare Module LP: ImpParam.

Include MkSeqLanguage LP.

End ISeqLanguage.


Module Type ImpDict.

Declare Module R: PseudoRegisters.

Parameter t: Type -> Type.

Parameter get: forall {A}, t A -> R.t -> option A.

Parameter set: forall {A}, t A -> R.t -> A -> t A.

Parameter set_spec_eq: forall A d x (v: A),
  get (set d x v) x = Some v.

Parameter set_spec_diff: forall A d x y (v: A),
  x <> y -> get (set d x v) y = get d y.

Parameter rem: forall {A}, t A -> R.t -> t A.

Parameter rem_spec_eq: forall A (d: t A) x,
  get (rem d x) x = None.

Parameter rem_spec_diff: forall A (d: t A) x y,
  x <> y -> get (rem d x) y = get d y.

Parameter empty: forall {A}, t A.

Parameter empty_spec: forall A x,
  get (empty (A:=A)) x = None.

Parameter eq_test: forall {A}, t A -> t A -> ?? bool.

Parameter eq_test_correct: forall A (d1 d2: t A),
 WHEN eq_test d1 d2 ~> b THEN
  b=true -> forall x, get d1 x = get d2 x.

(* NB: we could also take an eq_test on R.t (but not really useful with "pure" dictionaries  *)


(* only for debugging *)
Parameter not_eq_witness: forall {A}, t A -> t A -> ?? option R.t.

End ImpDict.


Module Type ImpSimuInterface.

Declare Module CoreL: ISeqLanguage.
Import CoreL.
Import Terms.

Parameter bblock_simu_test: reduction -> bblock -> bblock -> ?? bool.

Parameter bblock_simu_test_correct: forall reduce (p1 p2 : bblock),
    WHEN bblock_simu_test reduce p1 p2 ~> b
    THEN b = true -> forall ge : genv, bblock_simu ge p1 p2.


Parameter verb_bblock_simu_test
     : reduction ->
       (R.t -> ?? pstring) ->
       (op -> ?? pstring) -> bblock -> bblock -> ?? bool.

Parameter verb_bblock_simu_test_correct: 
   forall reduce
          (string_of_name : R.t -> ?? pstring)
          (string_of_op : op -> ?? pstring) 
          (p1 p2 : bblock),
    WHEN verb_bblock_simu_test reduce string_of_name string_of_op p1 p2 ~> b
    THEN b = true -> forall ge : genv, bblock_simu ge p1 p2.

End ImpSimuInterface.



Module ImpSimu (L: ISeqLanguage) (Dict: ImpDict with Module R:=L.LP.R): ImpSimuInterface with Module CoreL := L.

Module CoreL:=L.

Module ST := SimuTheory L.

Import ST.
Import Terms.

Definition term_set_hid (t: term) (hid: hashcode): term :=
  match t with
  | Input x _ => Input x hid
  | App op l _ => App op l hid
  end.

Definition list_term_set_hid (l: list_term) (hid: hashcode): list_term :=
  match l with
  | LTnil _ => LTnil hid
  | LTcons t l' _ => LTcons t l' hid
  end.

Lemma term_eval_set_hid ge t hid m:
  term_eval ge (term_set_hid t hid) m = term_eval ge t m.
Proof.
  destruct t; simpl; auto.
Qed.

Lemma list_term_eval_set_hid ge l hid m:
  list_term_eval ge (list_term_set_hid l hid) m = list_term_eval ge l m.
Proof.
  destruct l; simpl; auto.
Qed.

(* Local nickname *)
Module D:=ImpPrelude.Dict.

Section SimuWithReduce.

Variable reduce: reduction.

Section CanonBuilding.

Variable hC_term: hashinfo term -> ?? term.
Hypothesis hC_term_correct: forall t, WHEN hC_term t ~> t' THEN forall ge m, term_eval ge (hdata t) m = term_eval ge t' m.

Variable hC_list_term: hashinfo list_term -> ?? list_term.
Hypothesis hC_list_term_correct: forall t, WHEN hC_list_term t ~> t' THEN forall ge m, list_term_eval ge (hdata t) m = list_term_eval ge t' m.

(* First, we wrap constructors for hashed values !*)

Local Open Scope positive.
Local Open Scope list_scope.

Definition hInput_hcodes (x:R.t) :=
   DO hc <~ hash 1;;
   DO hv <~ hash x;;
   RET [hc;hv].
Extraction Inline hInput_hcodes.

Definition hInput (x:R.t): ?? term :=
   DO hv <~ hInput_hcodes x;;
   hC_term {| hdata:=Input x unknown_hid; hcodes :=hv; |}.

Lemma hInput_correct x:
  WHEN hInput x ~> t THEN forall ge m, term_eval ge t m = Some (m x).
Proof.
  wlp_simplify.
Qed.
Global Opaque hInput.
Hint Resolve hInput_correct: wlp.

Definition hApp_hcodes (o:op) (l: list_term) :=
   DO hc <~ hash 2;;
   DO hv <~ hash o;;
   RET [hc;hv;list_term_get_hid l].
Extraction Inline hApp_hcodes.

Definition hApp (o:op) (l: list_term) : ?? term :=
   DO hv <~ hApp_hcodes o l;;
   hC_term {| hdata:=App o l unknown_hid; hcodes:=hv |}.

Lemma hApp_correct o l:
  WHEN hApp o l ~> t THEN forall ge m,
    term_eval ge t m = match list_term_eval ge l m with
                       | Some v => op_eval ge o v
                       | None => None
                       end.
Proof.
  wlp_simplify.
Qed.
Global Opaque hApp.
Hint Resolve hApp_correct: wlp.

Definition hLTnil (_: unit): ?? list_term :=
   hC_list_term {| hdata:=LTnil unknown_hid; hcodes := nil; |} .

Lemma hLTnil_correct x: 
  WHEN hLTnil x ~> l THEN forall ge m, list_term_eval ge l m = Some nil.
Proof.
  wlp_simplify.
Qed.
Global Opaque hLTnil.
Hint Resolve hLTnil_correct: wlp.


Definition hLTcons (t: term) (l: list_term): ?? list_term :=
   hC_list_term {| hdata:=LTcons t l unknown_hid; hcodes := [term_get_hid t; list_term_get_hid l]; |}.

Lemma hLTcons_correct t l:
  WHEN hLTcons t l ~> l' THEN forall ge m, 
     list_term_eval ge l' m = match term_eval ge t m, list_term_eval ge l m with
                              | Some v, Some lv => Some (v::lv)
                              | _, _ => None
                              end.
Proof.
  wlp_simplify.
Qed.
Global Opaque hLTcons.
Hint Resolve hLTcons_correct: wlp.

(* Second, we use these hashed constructors ! *)

Record hsmem:= {hpre: list term; hpost:> Dict.t term}.

(** evaluation of the post-condition *)
Definition hsmem_post_eval ge (hd: Dict.t term) x (m:mem) :=
   match Dict.get hd x with 
   | None => Some (m x)
   | Some ht => term_eval ge ht m
   end.

Definition hsmem_get (d:hsmem) x: ?? term :=
   match Dict.get d x with 
   | None => hInput x
   | Some t => RET t
   end.

Lemma hsmem_get_correct (d:hsmem) x:
  WHEN hsmem_get d x ~> t THEN forall ge m, term_eval ge t m = hsmem_post_eval ge d x m.
Proof.
  unfold hsmem_get, hsmem_post_eval; destruct (Dict.get d x); wlp_simplify.
Qed.
Global Opaque hsmem_get.
Hint Resolve hsmem_get_correct: wlp.

Local Opaque allvalid.

Definition smem_model ge (d: smem) (hd:hsmem): Prop :=
  (forall m, allvalid ge hd.(hpre) m <-> smem_valid ge d m) 
  /\ (forall m x, smem_valid ge d m -> hsmem_post_eval ge hd x m = (ST.term_eval ge (d x) m)).

Lemma smem_model_smem_valid_alt ge d hd: smem_model ge d hd -> 
 forall m x, smem_valid ge d m -> hsmem_post_eval ge hd x m <> None.
Proof.
  intros (H1 & H2) m x H. rewrite H2; auto.
  unfold smem_valid in H. intuition eauto.
Qed.

Lemma smem_model_allvalid_alt ge d hd: smem_model ge d hd -> 
 forall m x, allvalid ge hd.(hpre) m -> hsmem_post_eval ge hd x m <> None.
Proof.
  intros (H1 & H2) m x H. eapply smem_model_smem_valid_alt.
  - split; eauto.
  - rewrite <- H1; auto.
Qed.

Definition naive_set (hd:hsmem) x (t:term) := 
  {| hpre:= t::hd.(hpre); hpost:=Dict.set hd x t |}.

Lemma naive_set_correct hd x ht ge d t:
    smem_model ge d hd ->
    (forall m, smem_valid ge d m -> term_eval ge ht m = ST.term_eval ge t m) ->
    smem_model ge (smem_set d x t) (naive_set hd x ht).
Proof.
  unfold naive_set; intros (DM0 & DM1) EQT; split.
  - intros m.
    destruct (DM0 m) as (PRE & VALID0); clear DM0.
    assert (VALID1: allvalid ge hd.(hpre) m -> pre d ge m). { unfold smem_valid in PRE; tauto. }
    assert (VALID2: allvalid ge hd.(hpre) m -> forall x : Dict.R.t, ST.term_eval ge (d x) m <> None). { unfold smem_valid in PRE; tauto. }
    rewrite !allvalid_extensionality in * |- *; simpl.
    intuition (subst; eauto).
    + eapply smem_valid_set_proof; eauto.
      erewrite <- EQT; eauto.
    + exploit smem_valid_set_decompose_1; eauto.
      intros X1; exploit smem_valid_set_decompose_2; eauto.
      rewrite <- EQT; eauto.
    + exploit smem_valid_set_decompose_1; eauto.
  - clear DM0. unfold hsmem_post_eval, hsmem_post_eval in * |- *; simpl.
    Local Hint Resolve smem_valid_set_decompose_1: core.
    intros; case (R.eq_dec x x0).
    + intros; subst; rewrite !Dict.set_spec_eq; simpl; eauto.
    + intros; rewrite !Dict.set_spec_diff; simpl; eauto.
Qed.
Local Hint Resolve naive_set_correct: core.

Definition equiv_hsmem ge (hd1 hd2: hsmem) := 
      (forall m, allvalid ge hd1.(hpre) m <-> allvalid ge hd2.(hpre) m)
   /\ (forall m x, allvalid ge hd1.(hpre) m -> hsmem_post_eval ge hd1 x m = hsmem_post_eval ge hd2 x m).

Lemma equiv_smem_symmetry ge hd1 hd2:
  equiv_hsmem ge hd1 hd2 -> equiv_hsmem ge hd2 hd1.
Proof.
  intros (V1 & P1); split.
  - intros; symmetry; auto.
  - intros; symmetry; eapply P1. rewrite V1; auto.
Qed.

Lemma equiv_hsmem_models ge hd1 hd2 d: 
   smem_model ge d hd1 -> equiv_hsmem ge hd1 hd2 -> smem_model ge d hd2.
Proof.
  intros (VALID & EQUIV) (HEQUIV & PEQUIV); split.
  - intros m; rewrite <- VALID; auto. symmetry; auto.
  - intros m x H. rewrite <- EQUIV; auto. 
    rewrite PEQUIV; auto.
    rewrite VALID; auto.
Qed.

Variable log_assign: R.t -> term -> ?? unit.

Definition lift {A B} hid (x:A) (k: B -> ?? A) (y:B): ?? A :=
  DO b <~ phys_eq hid unknown_hid;;
  if b then k y else RET x.

Fixpoint hterm_lift (t: term): ?? term :=
  match t with
  | Input x hid => lift hid t hInput x
  | App o l hid => 
      lift hid t
       (fun l => DO lt <~ hlist_term_lift l;;
        hApp o lt) l
  end
with hlist_term_lift (l: list_term) {struct l}: ?? list_term :=
  match l with
  | LTnil hid => lift hid l hLTnil ()
  | LTcons t l' hid => 
     lift hid l
        (fun t => DO t <~ hterm_lift t;;
         DO lt <~ hlist_term_lift l';;
          hLTcons t lt) t
  end.

Lemma hterm_lift_correct t:
  WHEN hterm_lift t ~> ht THEN forall ge m, term_eval ge ht m = term_eval ge t m.
Proof.
  induction t using term_mut with (P0:=fun lt =>
     WHEN hlist_term_lift lt ~> hlt THEN forall ge m, list_term_eval ge hlt m = list_term_eval ge lt m); 
     wlp_simplify.
  - rewrite H0, H; auto.
  - rewrite H1, H0, H; auto.
Qed.
Local Hint Resolve hterm_lift_correct: wlp.
Global Opaque hterm_lift.

Variable log_new_hterm: term -> ?? unit.

Fixpoint hterm_append (l: list term) (lh: list term): ?? list term :=
  match l with
  | nil => RET lh
  | t::l' =>
     DO ht <~ hterm_lift t;;
     log_new_hterm ht;;
     hterm_append l' (ht::lh)
  end.

Lemma hterm_append_correct l: forall lh,
  WHEN hterm_append l lh ~> lh' THEN (forall ge m, allvalid ge lh' m <-> (allvalid ge l m /\ allvalid ge lh m)).
Proof.
  Local Hint Resolve eq_trans: localhint.
  induction l as [|t l']; simpl; wlp_xsimplify ltac:(eauto with wlp).
  - intros; rewrite! allvalid_extensionality; intuition eauto.
  - intros REC ge m; rewrite REC; clear IHl' REC. rewrite !allvalid_extensionality.
    simpl; intuition (subst; eauto with wlp localhint).
Qed.
(*Local Hint Resolve hterm_append_correct: wlp.*)
Global Opaque hterm_append.

Definition smart_set (hd:hsmem) x (ht:term) :=
     match ht with
     | Input y _ =>
       if R.eq_dec x y then
          RET (Dict.rem hd x)
       else (
          log_assign x ht;;
          RET (Dict.set hd x ht)
       )
     | _ => 
       log_assign x ht;;
       RET (Dict.set hd x ht)
     end.

Lemma smart_set_correct hd x ht:
  WHEN smart_set hd x ht ~> d THEN
    forall ge m y, hsmem_post_eval ge d y m = hsmem_post_eval ge (Dict.set hd x ht) y m.
Proof.
  destruct ht; wlp_simplify.
  unfold hsmem_post_eval; simpl. case (R.eq_dec x0 y).
  - intros; subst. rewrite Dict.set_spec_eq, Dict.rem_spec_eq. simpl; congruence.
  - intros; rewrite Dict.set_spec_diff, Dict.rem_spec_diff; auto.
Qed.
(*Local Hint Resolve smart_set_correct: wlp.*)
Global Opaque smart_set.

Definition hsmem_set (hd:hsmem) x (t:term) :=
  DO pt <~ reduce t;;
  DO lht <~ hterm_append pt.(mayfail) hd.(hpre);;
  DO ht <~ hterm_lift pt.(effect);;
  log_new_hterm ht;;
  DO nd <~ smart_set hd x ht;;
  RET {| hpre := lht; hpost := nd |}.

Lemma hsmem_set_correct hd x ht:
  WHEN hsmem_set hd x ht ~> nhd THEN
    forall ge d t, smem_model ge d hd ->
    (forall m, smem_valid ge d m -> term_eval ge ht m = ST.term_eval ge t m) ->
    smem_model ge (smem_set d x t) nhd.
Proof.
  intros; wlp_simplify.
  generalize (hterm_append_correct _ _ _ Hexta0); intro APPEND.
  generalize (hterm_lift_correct _ _ Hexta1); intro LIFT.
  generalize (smart_set_correct _ _ _ _ Hexta3); intro SMART.
  eapply equiv_hsmem_models; eauto; unfold equiv_hsmem; simpl. 
  destruct H as (VALID & EFFECT); split.
  - intros; rewrite APPEND, <- VALID.
    rewrite !allvalid_extensionality in * |- *; simpl; intuition (subst; eauto).
  - intros m x0 ALLVALID; rewrite SMART.
    destruct (term_eval ge ht m) eqn: Hht.
    * case (R.eq_dec x x0).
      + intros; subst. unfold hsmem_post_eval; simpl. rewrite !Dict.set_spec_eq.
        erewrite LIFT, EFFECT; eauto.
      + intros; unfold hsmem_post_eval; simpl. rewrite !Dict.set_spec_diff; auto.
    * rewrite allvalid_extensionality in ALLVALID; destruct (ALLVALID ht); simpl; auto.
Qed.
Local Hint Resolve hsmem_set_correct: wlp.
Global Opaque hsmem_set.

(* VARIANTE: we do not hash-cons the term from the expression
Lemma exp_hterm_correct ge e hod od:
  smem_model ge od hod ->
 forall hd d,
  smem_model ge d hd ->
  forall m, smem_valid ge d m -> smem_valid ge od m -> term_eval ge (exp_term e hd hod) m = term_eval ge (exp_term e d od) m.
Proof.
  intro H.
  induction e using exp_mut with (P0:=fun le =>  forall d hd,
     smem_model ge d hd -> forall m, smem_valid ge d m -> smem_valid ge od m -> list_term_eval ge (list_exp_term le hd hod) m = list_term_eval ge (list_exp_term le d od) m); 
     unfold smem_model in * |- * ; simpl; intuition eauto.
  - erewrite IHe; eauto.
  - erewrite IHe0, IHe; eauto.
Qed.
Local Hint Resolve exp_hterm_correct: wlp.
*)

Fixpoint exp_hterm (e: exp) (hd hod: hsmem): ?? term :=
  match e with
  | PReg x => hsmem_get hd x
  | Op o le =>
     DO lt <~ list_exp_hterm le hd hod;; 
     hApp o lt
  | Old e => exp_hterm e hod hod
  end
with list_exp_hterm (le: list_exp) (hd hod: hsmem): ?? list_term :=
  match le with
  | Enil => hLTnil tt
  | Econs e le' => 
     DO t <~ exp_hterm e hd hod;;
     DO lt <~ list_exp_hterm le' hd hod;;
     hLTcons t lt
  | LOld le => list_exp_hterm le hod hod
  end.

Lemma exp_hterm_correct_x ge e hod od:
   smem_model ge od hod ->
  forall hd d,
   smem_model ge d hd ->
  WHEN exp_hterm e hd hod ~> t THEN forall m, smem_valid ge d m -> smem_valid ge od m -> term_eval ge t m = ST.term_eval ge (exp_term e d od) m.
 Proof.
   intro H.
   induction e using exp_mut with (P0:=fun le =>  forall d hd,
     smem_model ge d hd ->
     WHEN list_exp_hterm le hd hod ~> lt THEN forall m, smem_valid ge d m -> smem_valid ge od m -> list_term_eval ge lt m = ST.list_term_eval ge (list_exp_term le d od) m); 
     unfold smem_model, hsmem_post_eval in * |- * ; simpl; wlp_simplify.
  - rewrite H1, <- H4; auto.
  - rewrite H4, <- H0; simpl; auto.
  - rewrite H5, <- H0, <- H4; simpl; auto.
Qed.
Global Opaque exp_hterm.

Lemma exp_hterm_correct e hd hod:
  WHEN exp_hterm e hd hod ~> t THEN forall ge od d m, smem_model ge od hod -> smem_model ge d hd -> smem_valid ge d m -> smem_valid ge od m -> term_eval ge t m = ST.term_eval ge (exp_term e d od) m.
Proof.
  unfold wlp; intros; eapply exp_hterm_correct_x; eauto.
Qed.
Hint Resolve exp_hterm_correct: wlp.

Fixpoint hinst_smem (i: inst) (hd hod: hsmem): ?? hsmem :=
  match i with
  | nil => RET hd
  | (x, e)::i' =>
     DO ht <~ exp_hterm e hd hod;;
     DO nd <~ hsmem_set hd x ht;;
     hinst_smem i' nd hod
  end.

Lemma hinst_smem_correct i: forall hd hod,
  WHEN hinst_smem i hd hod ~> hd' THEN
    forall ge od d, smem_model ge od hod -> smem_model ge d hd -> (forall m, smem_valid ge d m -> smem_valid ge od m) -> smem_model ge (inst_smem i d od) hd'.
Proof.
  Local Hint Resolve smem_valid_set_proof: core.
  induction i; simpl; wlp_simplify; eauto 15 with wlp.
Qed.
Global Opaque hinst_smem.
Local Hint Resolve hinst_smem_correct: wlp.

(* logging info: we log the number of inst-instructions passed ! *)
Variable log_new_inst: unit -> ?? unit. 

Fixpoint bblock_hsmem_rec (p: bblock) (d: hsmem): ?? hsmem :=
  match p with
  | nil => RET d
  | i::p' =>
     log_new_inst tt;;
     DO d' <~ hinst_smem i d d;;
     bblock_hsmem_rec p' d'
  end.

Lemma bblock_hsmem_rec_correct p: forall hd,
  WHEN bblock_hsmem_rec p hd ~> hd' THEN forall ge d, smem_model ge d hd -> smem_model ge (bblock_smem_rec p d) hd'.
Proof.
  induction p; simpl; wlp_simplify.
Qed.
Global Opaque bblock_hsmem_rec.
Local Hint Resolve bblock_hsmem_rec_correct: wlp.

Definition hsmem_empty: hsmem := {| hpre:= nil ; hpost := Dict.empty |}.

Lemma hsmem_empty_correct ge: smem_model ge smem_empty hsmem_empty.
Proof.
  unfold smem_model, smem_valid, hsmem_post_eval; simpl; intuition try congruence.
  rewrite !Dict.empty_spec; simpl; auto.
Qed.

Definition bblock_hsmem: bblock -> ?? hsmem
 := fun p => bblock_hsmem_rec p hsmem_empty.

Lemma bblock_hsmem_correct p:
  WHEN bblock_hsmem p ~> hd THEN forall ge, smem_model ge (bblock_smem p) hd.
Proof.
  Local Hint Resolve hsmem_empty_correct: core.
  wlp_simplify.
Qed.
Global Opaque bblock_hsmem.

End CanonBuilding.

(* Now, we build the hash-Cons value from a "hash_eq".

Informal specification: 
  [hash_eq] must be consistent with the "hashed" constructors defined above.

We expect that hashinfo values in the code of these "hashed" constructors verify:

  (hash_eq (hdata x) (hdata y) ~> true) <-> (hcodes x)=(hcodes y)    

*)

Definition term_hash_eq (ta tb: term): ?? bool := 
  match ta, tb with
  | Input xa _, Input xb _ =>
     if R.eq_dec xa xb  (* Inefficient in some cases ? *)
     then RET true
     else RET false
  | App oa lta _, App ob ltb _ => 
     DO b <~ op_eq oa ob ;;
     if b then phys_eq lta ltb
     else RET false
  | _,_ => RET false
  end.

Lemma term_hash_eq_correct: forall ta tb, WHEN term_hash_eq ta tb ~> b THEN b=true -> term_set_hid ta unknown_hid=term_set_hid tb unknown_hid.
Proof.
  Local Hint Resolve op_eq_correct: wlp.
  destruct ta, tb; wlp_simplify; (discriminate || (subst; auto)).
Qed.
Global Opaque term_hash_eq.
Hint Resolve term_hash_eq_correct: wlp.

Definition list_term_hash_eq (lta ltb: list_term): ?? bool := 
  match lta, ltb with
  | LTnil _, LTnil _ => RET true
  | LTcons ta lta _, LTcons tb ltb _ => 
      DO b <~ phys_eq ta tb ;;
     if b then phys_eq lta ltb
     else RET false
  | _,_ => RET false
  end.

Lemma list_term_hash_eq_correct: forall lta ltb, WHEN list_term_hash_eq lta ltb ~> b THEN b=true -> list_term_set_hid lta unknown_hid=list_term_set_hid ltb unknown_hid.
Proof.
  destruct lta, ltb; wlp_simplify; (discriminate || (subst; auto)).
Qed.
Global Opaque list_term_hash_eq.
Hint Resolve list_term_hash_eq_correct: wlp.

Lemma hsmem_post_eval_intro (d1 d2: hsmem):
  (forall x, Dict.get d1 x = Dict.get d2 x) -> (forall ge x m, hsmem_post_eval ge d1 x m = hsmem_post_eval ge d2 x m).
Proof.
  unfold hsmem_post_eval; intros H ge x m; rewrite H. destruct (Dict.get d2 x); auto.
Qed.

Local Hint Resolve bblock_hsmem_correct Dict.eq_test_correct: wlp.

Program Definition mk_hash_params (log: term -> ?? unit): Dict.hash_params term :=
 {|
    Dict.test_eq := phys_eq;
    Dict.hashing := fun (ht: term) => RET (term_get_hid ht);
    Dict.log := log |}.
Obligation 1.
  eauto with wlp.
Qed.

(*** A GENERIC EQ_TEST: IN ORDER TO SUPPORT SEVERAL DEBUGGING MODE !!! ***)
Definition no_log_assign (x:R.t) (t:term): ?? unit := RET tt.
Definition no_log_new_term (t:term): ?? unit := RET tt.

Section Prog_Eq_Gen.

Variable log_assign: R.t -> term -> ?? unit.
Variable log_new_term: hashConsing term -> hashConsing list_term -> ??(term -> ?? unit).
Variable log_inst1: unit -> ?? unit. (* log of p1 insts *)
Variable log_inst2: unit -> ?? unit. (* log of p2 insts *)

Variable hco_term: hashConsing term.
Hypothesis hco_term_correct: forall t, WHEN hco_term.(hC) t ~> t' THEN forall ge m, term_eval ge (hdata t) m = term_eval ge t' m.

Variable hco_list: hashConsing list_term.
Hypothesis hco_list_correct: forall t, WHEN hco_list.(hC) t ~> t' THEN forall ge m, list_term_eval ge (hdata t) m = list_term_eval ge t' m.

Variable print_error_end: hsmem -> hsmem -> ?? unit.
Variable print_error: pstring -> ?? unit.

Variable check_failpreserv: bool.
Variable dbg_failpreserv: term -> ?? unit. (* info of additional failure of the output bbloc p2 wrt the input bbloc p1 *) 

Program Definition g_bblock_simu_test (p1 p2: bblock): ?? bool :=
  DO failure_in_failpreserv <~ make_cref false;;
  DO r <~ (TRY
    DO d1 <~ bblock_hsmem hco_term.(hC) hco_list.(hC) log_assign no_log_new_term log_inst1 p1;;
    DO log_new_term <~ log_new_term hco_term hco_list;;
    DO d2 <~ bblock_hsmem hco_term.(hC) hco_list.(hC) no_log_assign log_new_term log_inst2 p2;;
    DO b <~ Dict.eq_test d1 d2 ;;
    if b then (
      if check_failpreserv then (
          let hp := mk_hash_params dbg_failpreserv in
          failure_in_failpreserv.(set)(true);;
          Sets.assert_list_incl hp d2.(hpre) d1.(hpre);;
          RET true
      ) else RET false
    ) else (
      print_error_end d1 d2 ;;
      RET false
    )
  CATCH_FAIL s, _ =>
    DO b <~ failure_in_failpreserv.(get)();;
    if b then RET false 
         else print_error s;; RET false
  ENSURE (fun b => b=true -> forall ge, bblock_simu ge p1 p2));;
  RET (`r).
Obligation 1.
  constructor 1; wlp_simplify; try congruence.
  destruct (H ge) as (EQPRE1&EQPOST1); destruct (H0 ge) as (EQPRE2&EQPOST2); clear H H0.
  apply bblock_smem_simu; auto. split.
  + intros m; rewrite <- EQPRE1, <- EQPRE2.
    rewrite ! allvalid_extensionality.
    unfold incl in * |- *; intuition eauto.
  + intros m0 x VALID; rewrite <- EQPOST1, <- EQPOST2; auto.
    erewrite hsmem_post_eval_intro; eauto.
    erewrite <- EQPRE2; auto.
    erewrite <- EQPRE1 in VALID.
    rewrite ! allvalid_extensionality in * |- *.
    unfold incl in * |- *; intuition eauto.
Qed.

Theorem g_bblock_simu_test_correct p1 p2:
  WHEN g_bblock_simu_test p1 p2 ~> b THEN b=true -> forall ge, bblock_simu ge p1 p2.
Proof.
  wlp_simplify.
  destruct exta0; simpl in * |- *; auto.
Qed.
Global Opaque g_bblock_simu_test.

End Prog_Eq_Gen.



Definition hpt: hashP term := {| hash_eq := term_hash_eq; get_hid:=term_get_hid; set_hid:=term_set_hid |}. 
Definition hplt: hashP list_term := {| hash_eq := list_term_hash_eq; get_hid:=list_term_get_hid; set_hid:=list_term_set_hid |}.

Definition recover_hcodes (t:term): ??(hashinfo term) :=
  match t with
  | Input x _ => 
    DO hv <~ hInput_hcodes x ;;
    RET {| hdata := t; hcodes := hv |}
  | App o l _ => 
    DO hv <~ hApp_hcodes o l ;;
    RET {| hdata := t; hcodes := hv |}
  end.


Definition msg_end_of_bblock: pstring :="--- unknown subterms in the graph".

Definition log_new_term
    (unknownHash_msg: term -> ?? pstring)
    (hct:hashConsing term) 
    (hcl:hashConsing list_term) 
    : ?? (term -> ?? unit) :=
  DO clock <~ hct.(next_hid)();;
  hct.(next_log) msg_end_of_bblock;;
  hcl.(next_log) msg_end_of_bblock;;
  RET (fun t =>
       DO ok <~ hash_older (term_get_hid t) clock;;
       if ok 
       then
          RET tt
       else 
          DO ht <~ recover_hcodes t;;
          hct.(remove) ht;;
          DO msg <~ unknownHash_msg t;;
          FAILWITH msg).

Definition skip (_:unit): ?? unit := RET tt.

Definition msg_prefix: pstring := "*** ERROR INFO from bblock_simu_test: ".
Definition msg_error_on_end: pstring := "mismatch in final assignments !".
Definition msg_unknow_term: pstring := "unknown term".
Definition msg_number: pstring := "on 2nd bblock -- on inst num ".
Definition msg_notfailpreserv: pstring := "a possible failure of 2nd bblock is absent in 1st bblock (INTERNAL ERROR: this error is expected to be detected before!!!)".

Definition print_error_end (_ _: hsmem): ?? unit
 := println (msg_prefix +; msg_error_on_end).

Definition print_error (log: logger unit) (s:pstring): ?? unit
 := DO n <~ log_info log ();;
    println (msg_prefix +; msg_number +; n +; " -- " +; s). 

Definition failpreserv_error (_: term): ?? unit
  := println (msg_prefix +; msg_notfailpreserv).

Lemma term_eval_set_hid_equiv ge t1 t2 hid1 hid2 m:
  term_set_hid t1 hid1 = term_set_hid t2 hid2 -> term_eval ge t1 m = term_eval ge t2 m.
Proof.
  intro H; erewrite <- term_eval_set_hid; rewrite H. apply term_eval_set_hid.
Qed.

Lemma list_term_eval_set_hid_equiv ge t1 t2 hid1 hid2 m:
  list_term_set_hid t1 hid1 = list_term_set_hid t2 hid2 -> list_term_eval ge t1 m = list_term_eval ge t2 m.
Proof.
  intro H; erewrite <- list_term_eval_set_hid; rewrite H. apply list_term_eval_set_hid.
Qed.

Local Hint Resolve term_eval_set_hid_equiv list_term_eval_set_hid_equiv: core.

Program Definition bblock_simu_test (p1 p2: bblock): ?? bool :=
  DO log <~ count_logger ();;
  DO hco_term <~ mk_annot (hCons hpt);;
  DO hco_list <~ mk_annot (hCons hplt);;
  g_bblock_simu_test
    no_log_assign
    (log_new_term (fun _ => RET msg_unknow_term))
    skip
    (log_insert log)
    hco_term _
    hco_list _
    print_error_end
    (print_error log)
    true (* check_failpreserv *)
    failpreserv_error
    p1 p2.
Obligation 1.
  generalize (hCons_correct _ _ _ H0); clear H0.
  wlp_simplify.
Qed.
Obligation 2.
  generalize (hCons_correct _ _ _ H); clear H.
  wlp_simplify.
Qed.

Local Hint Resolve g_bblock_simu_test_correct: core.

Theorem bblock_simu_test_correct p1 p2:
  WHEN bblock_simu_test p1 p2 ~> b THEN b=true -> forall ge, bblock_simu ge p1 p2.
Proof.
  wlp_simplify.
Qed.
Global Opaque bblock_simu_test.

(** This is only to print info on each bblock_simu_test run **)
Section Verbose_version.

Variable string_of_name: R.t -> ?? pstring.
Variable string_of_op: op -> ?? pstring.


Local Open Scope string_scope.

Definition string_term_hid (t: term): ?? pstring := 
  DO id <~ string_of_hashcode (term_get_hid t);;
  RET ("E" +; (CamlStr id)).

Definition string_list_hid (lt: list_term): ?? pstring := 
  DO id <~ string_of_hashcode (list_term_get_hid lt);;
  RET ("L" +; (CamlStr id)).

Definition print_raw_term (t: term): ?? unit :=
  match t with
  | Input x _ => 
    DO s <~ string_of_name x;;
    println( "init_access " +; s)
  | App o (LTnil _) _ => 
    DO so <~ string_of_op o;;
    println so
  | App o l _ =>
    DO so <~ string_of_op o;;
    DO sl <~ string_list_hid l;;
    println (so +; " " +; sl)
  end.

(*
Definition print_raw_list(lt: list_term): ?? unit :=
  match lt with
  | LTnil _=> println ""
  | LTcons t l _ =>
    DO st <~ string_term_hid t;;
    DO sl <~ string_list_hid l;;
    println(st +; " " +; sl)
  end.
*)

Section PrettryPrint.

Variable get_debug_info: term -> ?? option pstring. 

Fixpoint string_of_term (t: term): ?? pstring :=
  match t with
  | Input x _ => string_of_name x
  | App o (LTnil _) _ => string_of_op o
  | App o l _ => 
      DO so <~ string_of_op o;;
      DO sl <~ string_of_list_term l;;
      RET (so +; "[" +; sl +; "]")
  end
with string_of_list_term (l: list_term): ?? pstring :=
  match l with
  | LTnil _ => RET (Str "")
  | LTcons t (LTnil _) _  => 
    DO dbg <~ get_debug_info t;;
    match dbg with
    | Some x => RET x
    | None => string_of_term t
    end
  | LTcons t l' _ => 
     DO st <~ (DO dbg <~ get_debug_info t;;
               match dbg with
               | Some x => RET x
               | None => string_of_term t
               end);;
     DO sl <~ string_of_list_term l';;
     RET (st +; ";" +; sl)
  end.


End PrettryPrint.


Definition pretty_term gdi t :=
  DO r <~ string_of_term gdi t;;
  println(r).

Fixpoint print_head (head: list pstring): ?? unit :=
  match head with
  | i::head' => println (i);; print_head head'
  | _ => RET tt
  end.

Definition print_term gdi (head: list pstring) (t: term): ?? unit :=
  print_head head;;
  DO s <~ string_term_hid t;;
  print (s +; ": ");;
  print_raw_term t;;
  DO dbg <~ gdi t;;
  match dbg with
  | Some x => 
     print("//  " +; x +; " <- ");;
     pretty_term gdi t
  | None => RET tt
  end.

Definition print_list gdi (head: list pstring) (lt: list_term): ?? unit :=
  print_head head;;
  DO s <~ string_list_hid lt ;;
  print (s +; ": ");;
  (* print_raw_list lt;; *)
  DO ps <~ string_of_list_term gdi lt;;
  println("[" +; ps +; "]").


Definition print_tables gdi ext exl: ?? unit :=
  println "-- term table --" ;;
  iterall ext (fun head _ pt => print_term gdi head pt.(hdata));;
  println "-- list table --" ;;
  iterall exl (fun head _ pl => print_list gdi head pl.(hdata));;
  println "----------------".

Definition print_final_debug gdi (d1 d2: hsmem): ?? unit 
 := DO b <~ Dict.not_eq_witness d1 d2 ;;
    match b with
    | Some x =>
      DO s <~ string_of_name x;;
      println("mismatch on: " +; s);;
      match Dict.get d1 x with 
      | None => println("=> unassigned in 1st bblock")
      | Some t1 =>
         print("=> node expected from 1st bblock: ");;
         pretty_term gdi t1
      end;;
      match Dict.get d2 x with 
      | None => println("=> unassigned in 2nd bblock")
      | Some t2 =>
         print("=> node found from 2nd bblock: ");;
         pretty_term gdi t2
      end
    | None => FAILWITH "bug in Dict.not_eq_witness ?"
    end.

Definition witness:= option term.

Definition msg_term (cr: cref witness) t :=
  set cr (Some t);;
  RET msg_unknow_term.

Definition print_witness gdi cr (*msg*) :=
  DO wit <~ get cr ();;
  match wit with
  | Some t =>
     println("=> unknown term node: ");;
     pretty_term gdi t (*;;
     println("=> encoded on " +; msg +; " graph as: ");;
     print_raw_term t *)
  | None => println "Unexpected failure: no witness info (hint: hash-consing bug ?)"
  end.


Definition print_error_end1 gdi hct hcl (d1 d2:hsmem): ?? unit
 := println "- GRAPH of 1st bblock";;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    print_tables gdi ext exl;;
    print_error_end d1 d2;;
    print_final_debug gdi d1 d2.

Definition print_error1 gdi hct hcl cr log s : ?? unit
 := println "- GRAPH of 1st bblock";;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    print_tables gdi ext exl;;
    print_error log s;;
    print_witness gdi cr (*"1st"*).


Definition xmsg_number: pstring := "on 1st bblock -- on inst num ".

Definition print_error_end2 gdi hct hcl (d1 d2:hsmem): ?? unit
 := println (msg_prefix +; msg_error_on_end);;
    println "- GRAPH of 2nd bblock";;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    print_tables gdi ext exl.

Definition print_error2 gdi hct hcl cr (log: logger unit) (s:pstring): ?? unit
 := DO n <~ log_info log ();;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    println (msg_prefix +; xmsg_number +; n +; " -- " +; s);;
    print_witness gdi cr (*"2nd"*);;
    println "- GRAPH of 2nd bblock";;
    print_tables gdi ext exl.

(* USELESS
Definition simple_log_assign (d: D.t term pstring) (x: R.t) (t: term): ?? unit :=
  DO s <~ string_of_name x;;
  d.(D.set) (t,s).
*)

Definition log_assign (d: D.t term pstring) (log: logger unit) (x: R.t) (t: term): ?? unit :=
  DO i <~ log_info log ();;
  DO sx <~ string_of_name x;;
  d.(D.set) (t,(sx +; "@" +; i)).

Definition msg_new_inst : pstring := "--- inst ".

Definition hlog (log: logger unit) (hct: hashConsing term) (hcl: hashConsing list_term): unit -> ?? unit :=
   (fun _ =>
      log_insert log tt ;;
      DO s <~ log_info log tt;;
      let s:= msg_new_inst +; s in
      next_log hct s;;
      next_log hcl s
    ).

Program Definition verb_bblock_simu_test (p1 p2: bblock): ?? bool :=
  DO dict_info <~ make_dict (mk_hash_params (fun _ => RET tt));;
  DO log1 <~ count_logger ();;
  DO log2 <~ count_logger ();;
  DO cr <~ make_cref None;;
  DO hco_term <~ mk_annot (hCons hpt);;
  DO hco_list <~ mk_annot (hCons hplt);;
  DO result1 <~ g_bblock_simu_test
     (log_assign dict_info log1)
     (log_new_term (msg_term cr))
     (hlog log1 hco_term hco_list)
     (log_insert log2)
     hco_term _
     hco_list _
     (print_error_end1 dict_info.(D.get) hco_term hco_list)
     (print_error1 dict_info.(D.get) hco_term hco_list cr log2)
     true
     failpreserv_error
     p1 p2;;
  if result1 
  then RET true
  else
    DO dict_info <~ make_dict (mk_hash_params (fun _ => RET tt));;
    DO log1 <~ count_logger ();;
    DO log2 <~ count_logger ();;
    DO cr <~ make_cref None;;
    DO hco_term <~ mk_annot (hCons hpt);;
    DO hco_list <~ mk_annot (hCons hplt);;
    DO result2 <~ g_bblock_simu_test
       (log_assign dict_info log1)
       (*fun _ _ => RET no_log_new_term*)  (* REM: too weak !! *)
       (log_new_term (msg_term cr))        (* REM: too strong ?? *)
       (hlog log1 hco_term hco_list)
       (log_insert log2)
       hco_term _
       hco_list _
       (print_error_end2 dict_info.(D.get) hco_term hco_list)
       (print_error2 dict_info.(D.get) hco_term hco_list cr log2)
       false
       (fun _ => RET tt)
       p2 p1;;
    if result2 
    then (
      println (msg_prefix +; " OOops - symmetry violation in bblock_simu_test  => this is a bug of bblock_simu_test ??");;
      RET false
    ) else RET false
   .
Obligation 1.
  generalize (hCons_correct _ _ _ H0); clear H0.
  wlp_simplify.
Qed.
Obligation 2.
  generalize (hCons_correct _ _ _ H); clear H.
  wlp_simplify.
Qed.
Obligation 3.
  generalize (hCons_correct _ _ _ H0); clear H0.
  wlp_simplify.
Qed.
Obligation 4.
  generalize (hCons_correct _ _ _ H); clear H.
  wlp_simplify.
Qed.

Theorem verb_bblock_simu_test_correct p1 p2:
  WHEN verb_bblock_simu_test p1 p2 ~> b THEN b=true -> forall ge, bblock_simu ge p1 p2.
Proof.
  wlp_simplify.
Qed.
Global Opaque verb_bblock_simu_test.

End Verbose_version.

End SimuWithReduce.

(* TODO: why inlining fails here ? *)
Transparent hterm_lift.
Extraction Inline lift.

End ImpSimu.

Require Import FMapPositive.


Require Import PArith.
Require Import FMapPositive.

Module ImpPosDict <: ImpDict with Module R:=Pos.

Module R:=Pos.

Definition t:=PositiveMap.t.

Definition get {A} (d:t A) (x:R.t): option A 
 := PositiveMap.find x d.

Definition set {A} (d:t A) (x:R.t) (v:A): t A
 := PositiveMap.add x v d.

Local Hint Unfold PositiveMap.E.eq: core.

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

Definition rem {A} (d:t A) (x:R.t): t A
 := PositiveMap.remove x d.

Lemma rem_spec_eq A (d: t A) x:
  get (rem d x) x = None.
Proof.
  unfold get, rem; apply PositiveMap.grs; auto.
Qed.

Lemma rem_spec_diff A (d: t A) x y:
  x <> y -> get (rem d x) y = get d y.
Proof.
  unfold get, rem; intros; apply PositiveMap.gro; auto.
Qed.


Definition empty {A}: t A := PositiveMap.empty A.

Lemma empty_spec A x:
  get (empty (A:=A)) x = None.
Proof.
  unfold get, empty; apply PositiveMap.gempty; auto.
Qed.

Import PositiveMap.

Fixpoint eq_test {A} (d1 d2: t A): ?? bool :=
  match d1, d2 with
  | Leaf _, Leaf _ => RET true
  | Node l1 (Some x1) r1, Node l2 (Some x2) r2 =>
      DO b0 <~ phys_eq x1 x2 ;;
      if b0 then
        DO b1 <~ eq_test l1 l2 ;;
        if b1 then
          eq_test r1 r2
        else
           RET false
      else
         RET false
  | Node l1 None r1, Node l2 None r2 =>
      DO b1 <~ eq_test l1 l2 ;;
      if b1 then
        eq_test r1 r2
      else
        RET false
  | _, _ => RET false
  end.

Lemma eq_test_correct A d1: forall (d2: t A),
 WHEN eq_test d1 d2 ~> b THEN
  b=true -> forall x, get d1 x = get d2 x.
Proof.
  unfold get; induction d1 as [|l1 Hl1 [x1|] r1 Hr1]; destruct d2 as [|l2 [x2|] r2]; simpl; 
  wlp_simplify; (discriminate || (subst; destruct x; simpl; auto)).
Qed.
Global Opaque eq_test.

(* ONLY FOR DEBUGGING INFO: get some key of a non-empty d *)
Fixpoint pick {A} (d: t A): ?? R.t :=
  match d with
  | Leaf _ => FAILWITH "unexpected empty dictionary"
  | Node _ (Some _) _ => RET xH
  | Node (Leaf _) None r => 
    DO p <~ pick r;;
    RET (xI p)
  | Node l None _ =>
    DO p <~ pick l;;
    RET (xO p)
  end.

(* ONLY FOR DEBUGGING INFO: find one variable on which d1 and d2 differs *)
Fixpoint not_eq_witness {A} (d1 d2: t A): ?? option R.t :=
  match d1, d2 with
  | Leaf _, Leaf _ => RET None
  | Node l1 (Some x1) r1, Node l2 (Some x2) r2 =>
      DO b0 <~ phys_eq x1 x2 ;;
      if b0 then
        DO b1 <~ not_eq_witness l1 l2;;
        match b1 with
        | None => 
          DO b2 <~ not_eq_witness r1 r2;;
          match b2 with
          | None => RET None
          | Some p => RET (Some (xI p))
          end
        | Some p => RET (Some (xO p))
        end
      else
         RET (Some xH)
  | Node l1 None r1, Node l2 None r2 =>
        DO b1 <~ not_eq_witness l1 l2;;
        match b1 with
        | None => 
          DO b2 <~ not_eq_witness r1 r2;;
          match b2 with
          | None => RET None
          | Some p => RET (Some (xI p))
          end
        | Some p => RET (Some (xO p))
        end
  | l, Leaf _ => DO p <~ pick l;; RET (Some p)
  | Leaf _, r => DO p <~ pick r;; RET (Some p)
  | _, _ => RET (Some xH)
  end.

End ImpPosDict.

