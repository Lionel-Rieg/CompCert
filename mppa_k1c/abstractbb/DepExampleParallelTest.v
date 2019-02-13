Require Import DepExampleEqTest.
Require Import Parallelizability.

Module PChk := ParallelChecks L PosResourceSet.

Definition bblock_is_para (p: bblock) : bool :=
  PChk.is_parallelizable (comp_bblock p).

Local Hint Resolve the_mem_separation reg_map_separation.

(* Actually, almost the same proof script than [comp_bblock_correct_aux] !
   We could definitely factorize the proof through a lemma on compilation to macros.
*)
Lemma comp_bblock_correct_para_iw p: forall sin sout min mout,
  match_state sin min -> 
  match_state sout mout ->
  match_option_state (sem_bblock_par_iw p sin sout) (PChk.prun_iw (comp_bblock p) mout min).
Proof.
  induction p as [|i p IHp]; simpl; eauto.
  intros sin sout min mout Hin Hout; destruct i; simpl; erewrite !comp_op_correct; eauto; simpl.
  - (* MOVE *)
    apply IHp; auto.
    destruct Hin as [H1 H2]; destruct Hout as [H3 H4]; constructor 1; simpl; auto.
    + rewrite L.assign_diff; auto.
    + unfold assign; intros r; destruct (Pos.eq_dec dest r).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
  - (* ARITH *)
    apply IHp; auto.
    destruct Hin as [H1 H2]; destruct Hout as [H3 H4]; constructor 1; simpl; auto.
    + rewrite L.assign_diff; auto.
    + unfold assign; intros r; destruct (Pos.eq_dec dest r).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
  - (* LOAD *)
    destruct Hin as [H1 H2]; destruct Hout as [H3 H4].
    rewrite H1, H2; simpl.
    unfold get_addr.
    destruct (rm sin base + operand_eval offset (rm sin))%Z; simpl; auto.
    apply IHp. { constructor 1; auto. }
    constructor 1; simpl.
    + rewrite L.assign_diff; auto.
    + unfold assign; intros r; destruct (Pos.eq_dec dest r).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
  - (* STORE *)
    destruct Hin as [H1 H2]; destruct Hout as [H3 H4].
    rewrite H1, !H2; simpl.
    unfold get_addr.
    destruct (rm sin base + operand_eval offset (rm sin))%Z; simpl; auto.
    apply IHp. { constructor 1; auto. }
    constructor 1; simpl; auto.
    intros r; rewrite L.assign_diff; auto.
  - (* MEMSWAP *)
    destruct Hin as [H1 H2]; destruct Hout as [H3 H4].
    rewrite H1, !H2; simpl.
    unfold get_addr.
    destruct (rm sin base + operand_eval offset (rm sin))%Z; simpl; auto.
    apply IHp. { constructor 1; auto. }
    constructor 1; simpl; auto.
    + intros r0; rewrite L.assign_diff; auto.
      unfold assign; destruct (Pos.eq_dec r r0).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
Qed.

Local Hint Resolve match_trans_state.

Definition trans_option_state (os: option state): option L.mem :=
  match os with
  | Some s => Some (trans_state s)
  | None => None
  end.

Lemma match_trans_option_state os: match_option_state os (trans_option_state os).
Proof.
  destruct os; simpl; eauto.
Qed.

Local Hint Resolve match_trans_option_state comp_bblock_correct match_option_state_intro_X match_from_res_eq res_equiv_from_match.

Lemma is_mem_reg (x: P.R.t): x=the_mem \/ exists r, x=reg_map r.
Proof.
  case (Pos.eq_dec x the_mem); auto.
  unfold the_mem, reg_map; constructor 2.
  eexists (Pos.pred x). rewrite Pos.succ_pred; auto.
Qed.

Lemma res_eq_from_match (os: option state) (om1 om2: option L.mem): 
  (match_option_stateX om1 os) -> (match_option_state os om2) -> (L.res_eq om1 om2).
Proof.
  destruct om1 as [m1|]; simpl.
  - intros (s & H1 & H2 & H3); subst; simpl.
    intros (m2 & H4 & H5 & H6); subst; simpl.
    eapply ex_intro; intuition eauto.
    destruct (is_mem_reg x) as [H|(r & H)]; subst; congruence.
  - intro; subst; simpl; auto.
Qed.

(* We use axiom of functional extensionality ! *)
Require Coq.Logic.FunctionalExtensionality.

Lemma match_from_res_equiv os1 os2 om: 
  res_equiv os2 os1 -> match_option_state os1 om ->  match_option_state os2 om.
Proof.
  destruct os2 as [s2 | ]; simpl.
  - intros (s & H1 & H2 & H3). subst; simpl.
    intros (m & H4 & H5 & H6); subst; simpl.
    eapply ex_intro; intuition eauto.
    constructor 1.
    + rewrite H5; apply f_equal; eapply FunctionalExtensionality.functional_extensionality; auto.
    + congruence.
  - intros; subst; simpl; auto.
Qed.


Require Import Sorting.Permutation.

Local Hint Constructors Permutation.

Lemma comp_bblock_Permutation p p': Permutation p p' -> Permutation (comp_bblock p) (comp_bblock p').
Proof.
 induction 1; simpl; eauto.
Qed.

Lemma comp_bblock_Permutation_back p1 p1': Permutation p1 p1' -> 
  forall p, p1=comp_bblock p ->
  exists p', p1'=comp_bblock p' /\ Permutation p p'.
Proof.
 induction 1; simpl; eauto.
 - destruct p as [|i p]; simpl; intro X; inversion X; subst.
   destruct (IHPermutation p) as (p' & H1 & H2); subst; auto.
   eexists (i::p'). simpl; eauto.
 - destruct p as [|i1 p]; simpl; intro X; inversion X as [(H & H1)]; subst; clear X.
   destruct p as [|i2 p]; simpl; inversion_clear H1.
   eexists (i2::i1::p). simpl; eauto.
 - intros p H1; destruct (IHPermutation1 p) as (p' & H2 & H3); subst; auto.
   destruct (IHPermutation2 p') as (p'' & H4 & H5); subst; eauto.
Qed.

Local Hint Resolve comp_bblock_Permutation res_eq_from_match match_from_res_equiv comp_bblock_correct_para_iw.

Lemma bblock_par_iff_prun p s os': 
 sem_bblock_par p s os' <-> PChk.prun (comp_bblock p) (trans_state s) (trans_option_state os').
Proof.
  unfold sem_bblock_par, PChk.prun. constructor 1.
  - intros (p' & H1 & H2).
    eexists (comp_bblock p'); intuition eauto.
  - intros (p' & H1 & H2). 
    destruct (comp_bblock_Permutation_back _ _ H2 p) as (p0 & H3 & H4); subst; auto.
    eexists p0; constructor 1; eauto.
Qed.

Theorem bblock_is_para_correct p:
  bblock_is_para p = true -> forall s os', (sem_bblock_par p s os' <-> res_equiv os' (sem_bblock p s)).
Proof.
  intros H; generalize (PChk.is_parallelizable_correct _ H); clear H.
  intros H s os'.
  rewrite bblock_par_iff_prun, H.
  constructor; eauto.
Qed.