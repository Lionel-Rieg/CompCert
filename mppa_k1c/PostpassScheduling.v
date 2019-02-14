(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Errors AST Integers.
Require Import Asmblock Axioms Memory Globalenvs.

Local Open Scope error_monad_scope.

(** Oracle taking as input a basic block,
    returns a schedule expressed as a list of bundles *)
Axiom schedule: bblock -> list bblock.

Extract Constant schedule => "PostpassSchedulingOracle.schedule".

(** Specification of the "coming soon" Asmblockdeps.v *)
Inductive bblock_equiv (ge: Genv.t fundef unit) (f: function) (bb bb': bblock) :=
  | bblock_equiv_intro:
      (forall rs m,
      exec_bblock ge f bb rs m = exec_bblock ge f bb' rs m) ->
      bblock_equiv ge f bb bb'.

Axiom state': Type.
Inductive outcome' := Next' : state' -> outcome' | Stuck' : outcome'.

Axiom bblock': Type.
Axiom exec': genv -> function -> bblock' -> state' -> outcome'.
Axiom match_states: state -> state' -> Prop. 
Axiom trans_block: bblock -> bblock'.
Axiom trans_state: state -> state'.

Axiom trans_state_match: forall S, match_states S (trans_state S).

Inductive bblock_equiv' (ge: Genv.t fundef unit) (f: function) (bb bb': bblock') :=
  | bblock_equiv_intro':
      (forall s,
      exec' ge f bb s = exec' ge f bb' s) ->
      bblock_equiv' ge f bb bb'.

Definition exec := exec_bblock.

Axiom forward_simu:
  forall rs1 m1 rs2 m2 s1' b ge fn,
    exec ge fn b rs1 m1 = Next rs2 m2 ->
    match_states (State rs1 m1) s1' ->
    exists s2',
       exec' ge fn (trans_block b) s1' = Next' s2'
    /\ match_states (State rs2 m2) s2'.

Axiom forward_simu_stuck:
  forall rs1 m1 s1' b ge fn,
    exec ge fn b rs1 m1 = Stuck ->
    match_states (State rs1 m1) s1' ->
    exec' ge fn (trans_block b) s1' = Stuck'.

Axiom trans_block_reverse_stuck:
  forall ge fn b rs m s',
  exec' ge fn (trans_block b) s' = Stuck' ->
  match_states (State rs m) s' ->
  exec ge fn b rs m = Stuck.

Axiom state_equiv:
  forall S1 S2 S', match_states S1 S' /\ match_states S2 S' -> S1 = S2.


(* TODO - replace it by the actual bblock_equivb' *)
Definition bblock_equivb' (b1 b2: bblock') := true.

Axiom bblock_equiv'_eq:
  forall ge fn b1 b2,
  bblock_equivb' b1 b2 = true <-> bblock_equiv' ge fn b1 b2.

Lemma trans_equiv_stuck:
  forall b1 b2 ge fn rs m,
  bblock_equiv' ge fn (trans_block b1) (trans_block b2) ->
  (exec ge fn b1 rs m = Stuck <-> exec ge fn b2 rs m = Stuck).
Proof.
  intros. inv H.
  pose (trans_state_match (State rs m)).
  split.
  - intros. eapply forward_simu_stuck in H; eauto. rewrite H0 in H. eapply trans_block_reverse_stuck; eassumption.
  - intros. eapply forward_simu_stuck in H; eauto. rewrite <- H0 in H. eapply trans_block_reverse_stuck; eassumption.
Qed.



Lemma bblock_equiv'_comm:
  forall ge fn b1 b2,
  bblock_equiv' ge fn b1 b2 <-> bblock_equiv' ge fn b2 b1.
Proof.
  intros. repeat constructor. all: inv H; congruence.
Qed.

Theorem trans_exec:
  forall b1 b2 ge f, bblock_equiv' ge f (trans_block b1) (trans_block b2) -> bblock_equiv ge f b1 b2.
Proof.
  repeat constructor. intros rs1 m1.
  destruct (exec_bblock _ _ b1 _ _) as [rs2 m2|] eqn:EXEB; destruct (exec_bblock _ _ b2 _ _) as [rs3 m3|] eqn:EXEB2; auto.
  - pose (trans_state_match (State rs1 m1)).
    exploit forward_simu.
      eapply EXEB.
      eapply m.
    intros (s2' & EXEB' & MS).
    exploit forward_simu.
      eapply EXEB2.
      eapply m.
    intros (s3' & EXEB'2 & MS2). inv H.
    rewrite H0 in EXEB'. rewrite EXEB'2 in EXEB'. inv EXEB'.
    exploit (state_equiv (State rs2 m2) (State rs3 m3) s2'). eauto.
    congruence.
  - rewrite trans_equiv_stuck in EXEB2. 2: eapply bblock_equiv'_comm; eauto. unfold exec in EXEB2. rewrite EXEB2 in EXEB. discriminate.
  - rewrite trans_equiv_stuck in EXEB; eauto. unfold exec in EXEB. rewrite EXEB in EXEB2. discriminate.
Qed.



(* Lemmas necessary for defining concat_all *)
Lemma app_nonil {A: Type} (l l': list A) : l <> nil -> l ++ l' <> nil.
Proof.
  intros. destruct l; simpl.
  - contradiction.
  - discriminate.
Qed.

Lemma app_nonil2 {A: Type} : forall (l l': list A), l' <> nil -> l ++ l' <> nil.
Proof.
  destruct l.
  - intros. simpl; auto.
  - intros. rewrite <- app_comm_cons. discriminate.
Qed.



Definition check_size bb :=
  if zlt Ptrofs.max_unsigned (size bb)
    then Error (msg "PostpassSchedulingproof.check_size")
  else OK tt.

Program Definition concat2 (bb bb': bblock) : res bblock :=
  do ch <- check_size bb;
  do ch' <- check_size bb';
  match (exit bb) with
  | None => 
      match (header bb') with
      | nil => 
          match (exit bb') with 
          | Some (PExpand (Pbuiltin _ _ _)) => Error (msg "PostpassSchedulingproof.concat2: builtin not alone")
          | _ => OK {| header := header bb; body := body bb ++ body bb'; exit := exit bb' |}
          end
      | _ => Error (msg "PostpassSchedulingproof.concat2")
      end
  | _ => Error (msg "PostpassSchedulingproof.concat2")
  end.
Next Obligation.
  apply wf_bblock_refl. constructor.
  - destruct bb' as [hd' bdy' ex' WF']. destruct bb as [hd bdy ex WF]. simpl in *.
    apply wf_bblock_refl in WF'. apply wf_bblock_refl in WF.
    inversion_clear WF'. inversion_clear WF. clear H1 H3.
    inversion H2; inversion H0.
    + left. apply app_nonil. auto.
    + right. auto.
    + left. apply app_nonil2. auto.
    + right. auto.
  - unfold builtin_alone. intros. rewrite H0 in H.
    assert (Some (PExpand (Pbuiltin ef args res)) <> Some (PExpand (Pbuiltin ef args res))).
    apply (H ef args res). contradict H1. auto.
Defined.

Lemma concat2_zlt_size:
  forall a b bb,
  concat2 a b = OK bb ->
     size a <= Ptrofs.max_unsigned
  /\ size b <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H.
  split.
  - unfold check_size in EQ. destruct (zlt Ptrofs.max_unsigned (size a)); monadInv EQ. omega.
  - unfold check_size in EQ1. destruct (zlt Ptrofs.max_unsigned (size b)); monadInv EQ1. omega.
Qed.

Lemma concat2_noexit:
  forall a b bb,
  concat2 a b = OK bb ->
  exit a = None.
Proof.
  intros. destruct a as [hd bdy ex WF]; simpl in *.
  destruct ex as [e|]; simpl in *; auto.
  unfold concat2 in H. simpl in H. monadInv H.
Qed.

Lemma concat2_decomp:
  forall a b bb,
  concat2 a b = OK bb ->
     body bb = body a ++ body b
  /\ exit bb = exit b.
Proof.
  intros. exploit concat2_noexit; eauto. intros.
  destruct a as [hda bda exa WFa]; destruct b as [hdb bdb exb WFb]; destruct bb as [hd bd ex WF]; simpl in *.
  subst exa.
  unfold concat2 in H; simpl in H.
  destruct hdb.
  - destruct exb.
    + destruct c.
      * destruct i. monadInv H.
      * monadInv H. split; auto.
    + monadInv H. split; auto.
  - monadInv H.
Qed.

Lemma concat2_size:
  forall a b bb, concat2 a b = OK bb -> size bb = size a + size b.
Proof.
  intros. unfold concat2 in H.
  destruct a as [hda bda exa WFa]; destruct b as [hdb bdb exb WFb]; destruct bb as [hd bdy ex WF]; simpl in *.
  destruct exa; monadInv H. destruct hdb; try (monadInv EQ2). destruct exb; try (monadInv EQ2).
  - destruct c.
    + destruct i; try (monadInv EQ2).
    + monadInv EQ2. unfold size; simpl. rewrite app_length. rewrite Nat.add_0_r. rewrite <- Nat2Z.inj_add. rewrite Nat.add_assoc. reflexivity.
  - unfold size; simpl. rewrite app_length. repeat (rewrite Nat.add_0_r). rewrite <- Nat2Z.inj_add. reflexivity.
Qed.

Lemma concat2_header:
  forall bb bb' tbb,
  concat2 bb bb' = OK tbb -> header bb = header tbb.
Proof.
  intros. destruct bb as [hd bdy ex COR]; destruct bb' as [hd' bdy' ex' COR']; destruct tbb as [thd tbdy tex tCOR]; simpl in *.
  unfold concat2 in H. simpl in H. monadInv H.
  destruct ex; try discriminate. destruct hd'; try discriminate. destruct ex'.
  - destruct c.
    + destruct i; discriminate.
    + congruence.
  - congruence.
Qed.

Lemma concat2_no_header_in_middle:
  forall bb bb' tbb,
  concat2 bb bb' = OK tbb ->
  header bb' = nil.
Proof.
  intros. destruct bb as [hd bdy ex COR]; destruct bb' as [hd' bdy' ex' COR']; destruct tbb as [thd tbdy tex tCOR]; simpl in *.
  unfold concat2 in H. simpl in H. monadInv H.
  destruct ex; try discriminate. destruct hd'; try discriminate. reflexivity.
Qed.



Fixpoint concat_all (lbb: list bblock) : res bblock :=
  match lbb with
  | nil => Error (msg "PostpassSchedulingproof.concatenate: empty list")
  | bb::nil => OK bb
  | bb::lbb =>
      do bb' <- concat_all lbb;
      concat2 bb bb'
  end.

Lemma concat_all_size :
  forall lbb a bb bb',
  concat_all (a :: lbb) = OK bb ->
  concat_all lbb = OK bb' ->
  size bb = size a + size bb'.
Proof.
  intros. unfold concat_all in H. fold concat_all in H.
  destruct lbb; try discriminate.
  monadInv H. rewrite H0 in EQ. inv EQ.
  apply concat2_size. assumption.
Qed.

Lemma concat_all_header:
  forall lbb bb tbb,
  concat_all (bb::lbb) = OK tbb -> header bb = header tbb.
Proof.
  destruct lbb.
  - intros. simpl in H. congruence.
  - intros. simpl in H. destruct lbb.
    + inv H. eapply concat2_header; eassumption.
    + monadInv H. eapply concat2_header; eassumption.
Qed.

Lemma concat_all_no_header_in_middle:
  forall lbb tbb,
  concat_all lbb = OK tbb ->
  Forall (fun b => header b = nil) (tail lbb).
Proof.
  induction lbb; intros; try constructor.
  simpl. simpl in H. destruct lbb.
  - constructor.
  - monadInv H. simpl tl in IHlbb. constructor.
    + apply concat2_no_header_in_middle in EQ0. apply concat_all_header in EQ. congruence.
    + apply IHlbb in EQ. assumption.
Qed.



Definition verify_schedule (bb bb' : bblock) : res unit :=
  match (bblock_equivb' (trans_block bb) (trans_block bb')) with
  | true => OK tt
  | false => Error (msg "PostpassScheduling.verify_schedule")
  end.

Definition verify_size bb lbb := if (Z.eqb (size bb) (size_blocks lbb)) then OK tt else Error (msg "PostpassScheduling:verify_size: wrong size").

Lemma verify_size_size:
  forall bb lbb, verify_size bb lbb = OK tt -> size bb = size_blocks lbb.
Proof.
  intros. unfold verify_size in H. destruct (size bb =? size_blocks lbb) eqn:SIZE; try discriminate.
  apply Z.eqb_eq. assumption.
Qed.



Program Definition no_header (bb : bblock) := {| header := nil; body := body bb; exit := exit bb |}.
Next Obligation.
  destruct bb; simpl. assumption.
Defined.

Lemma no_header_size:
  forall bb, size (no_header bb) = size bb.
Proof.
  intros. destruct bb as [hd bdy ex COR]. unfold no_header. simpl. reflexivity.
Qed.

Axiom trans_block_noheader_inv: forall bb, trans_block (no_header bb) = trans_block bb.

Lemma verify_schedule_no_header:
  forall bb bb',
  verify_schedule (no_header bb) bb' = verify_schedule bb bb'.
Proof.
  intros. unfold verify_schedule. rewrite trans_block_noheader_inv. reflexivity.
Qed.



Program Definition stick_header (h : list label) (bb : bblock) := {| header := h; body := body bb; exit := exit bb |}.
Next Obligation.
  destruct bb; simpl. assumption.
Defined.

Axiom trans_block_header_inv: forall bb hd, trans_block (stick_header hd bb) = trans_block bb.

Lemma stick_header_size:
  forall h bb, size (stick_header h bb) = size bb.
Proof.
  intros. destruct bb. unfold stick_header. simpl. reflexivity.
Qed.

Lemma stick_header_no_header:
  forall bb, stick_header (header bb) (no_header bb) = bb.
Proof.
  intros. destruct bb as [hd bdy ex COR]. simpl. unfold no_header; unfold stick_header; simpl. reflexivity.
Qed.

Lemma stick_header_verify_schedule:
  forall hd bb' hbb' bb,
  stick_header hd bb' = hbb' ->
  verify_schedule bb bb' = verify_schedule bb hbb'.
Proof.
  intros. unfold verify_schedule. rewrite <- H. rewrite trans_block_header_inv. reflexivity.
Qed.

Lemma check_size_stick_header:
  forall bb hd,
  check_size bb = check_size (stick_header hd bb).
Proof.
  intros. unfold check_size. rewrite stick_header_size. reflexivity.
Qed.

Lemma stick_header_concat2:
  forall bb bb' hd tbb,
  concat2 bb bb' = OK tbb ->
  concat2 (stick_header hd bb) bb' = OK (stick_header hd tbb).
Proof.
  intros. monadInv H. erewrite check_size_stick_header in EQ.
  unfold concat2. rewrite EQ. rewrite EQ1. simpl.
  destruct bb as [hdr bdy ex COR]; destruct bb' as [hdr' bdy' ex' COR']; simpl in *.
  destruct ex; try discriminate. destruct hdr'; try discriminate. destruct ex'.
  - destruct c.
    + destruct i. discriminate.
    + inv EQ2. unfold stick_header; simpl. reflexivity.
  - inv EQ2. unfold stick_header; simpl. reflexivity.
Qed.

Lemma stick_header_concat_all:
  forall bb c tbb hd,
  concat_all (bb :: c) = OK tbb ->
  concat_all (stick_header hd bb :: c) = OK (stick_header hd tbb).
Proof.
  intros. simpl in *. destruct c; try congruence.
  monadInv H. rewrite EQ. simpl.
  apply stick_header_concat2. assumption.
Qed.



Definition stick_header_code (h : list label) (lbb : list bblock) :=
  match (head lbb) with
  | None => Error (msg "PostpassScheduling.stick_header: empty schedule")
  | Some fst => OK ((stick_header h fst) :: tail lbb)
  end.

Lemma stick_header_code_no_header:
  forall bb c,
  stick_header_code (header bb) (no_header bb :: c) = OK (bb :: c).
Proof.
  intros. unfold stick_header_code. simpl. rewrite stick_header_no_header. reflexivity.
Qed.

Lemma hd_tl_size:
  forall lbb bb, hd_error lbb = Some bb -> size_blocks lbb = size bb + size_blocks (tl lbb).
Proof.
  destruct lbb.
  - intros. simpl in H. discriminate.
  - intros. simpl in H. inv H. simpl. reflexivity.
Qed.

Lemma stick_header_code_size:
  forall h lbb lbb', stick_header_code h lbb = OK lbb' -> size_blocks lbb = size_blocks lbb'.
Proof.
  intros. unfold stick_header_code in H. destruct (hd_error lbb) eqn:HD; try discriminate.
  inv H. simpl. rewrite stick_header_size. erewrite hd_tl_size; eauto.
Qed.

Lemma stick_header_code_no_header_in_middle:
  forall c h lbb,
  stick_header_code h c = OK lbb ->
  Forall (fun b => header b = nil) (tl c) ->
  Forall (fun b => header b = nil) (tl lbb).
Proof.
  destruct c; intros.
  - unfold stick_header_code in H. simpl in H. discriminate.
  - unfold stick_header_code in H. simpl in H. inv H. simpl in H0.
    simpl. assumption.
Qed.

Lemma stick_header_code_concat_all:
  forall hd lbb hlbb tbb,
  stick_header_code hd lbb = OK hlbb ->
  concat_all lbb = OK tbb ->
  exists htbb,
     concat_all hlbb = OK htbb
  /\ stick_header hd tbb = htbb.
Proof.
  intros. exists (stick_header hd tbb). split; auto.
  destruct lbb.
  - unfold stick_header_code in H. simpl in H. discriminate.
  - unfold stick_header_code in H. simpl in H. inv H.
    apply stick_header_concat_all. assumption.
Qed.



Definition do_schedule (bb: bblock) : list bblock :=
  if (Z.eqb (size bb) 1) then bb::nil else schedule bb.

Definition verified_schedule (bb : bblock) : res (list bblock) :=
  let bb' := no_header bb in
  let lbb := do_schedule bb' in
  do tbb <- concat_all lbb;
  do sizecheck <- verify_size bb lbb;
  do schedcheck <- verify_schedule bb' tbb;
  stick_header_code (header bb) lbb.

Lemma verified_schedule_size:
  forall bb lbb, verified_schedule bb = OK lbb -> size bb = size_blocks lbb.
Proof.
  intros. monadInv H. erewrite <- stick_header_code_size; eauto.
  apply verify_size_size.
  destruct x0; try discriminate. assumption.
Qed.

Lemma verified_schedule_single_inst:
  forall bb, size bb = 1 -> verified_schedule bb = OK (bb::nil).
Proof.
  intros. unfold verified_schedule.
  unfold do_schedule. rewrite no_header_size. rewrite H. simpl.
  unfold verify_size. simpl. rewrite no_header_size. rewrite Z.add_0_r. cutrewrite (size bb =? size bb = true). simpl.
  apply stick_header_code_no_header.
  rewrite H. reflexivity.
Qed.

Lemma verified_schedule_no_header_in_middle:
  forall lbb bb,
  verified_schedule bb = OK lbb ->
     Forall (fun b => header b = nil) (tail lbb).
Proof.
  intros. monadInv H. eapply stick_header_code_no_header_in_middle; eauto.
  eapply concat_all_no_header_in_middle. eassumption.
Qed.

Lemma verified_schedule_header:
  forall bb tbb lbb,
  verified_schedule bb = OK (tbb :: lbb) ->
     header bb = header tbb
  /\ Forall (fun b => header b = nil) lbb.
Proof.
  intros. split.
  - monadInv H. unfold stick_header_code in EQ3. destruct (hd_error _); try discriminate. inv EQ3.
    simpl. reflexivity.
  - apply verified_schedule_no_header_in_middle in H. assumption.
Qed.

Theorem verified_schedule_correct:
  forall ge f bb lbb,
  verified_schedule bb = OK lbb ->
  exists tbb, 
     concat_all lbb = OK tbb
  /\ bblock_equiv ge f bb tbb.
Proof.
  intros. monadInv H.
  exploit stick_header_code_concat_all; eauto.
  intros (tbb & CONC & STH).
  exists tbb. split; auto.
  rewrite verify_schedule_no_header in EQ0. erewrite stick_header_verify_schedule in EQ0; eauto.
  apply trans_exec. apply bblock_equiv'_eq. unfold verify_schedule in EQ0.
  destruct (bblock_equivb' _ _); auto; try discriminate.
Qed.



Fixpoint transf_blocks (lbb : list bblock) : res (list bblock) :=
  match lbb with
  | nil => OK nil
  | (cons bb lbb) =>
      do tlbb <- transf_blocks lbb;
      do tbb <- verified_schedule bb;
      OK (tbb ++ tlbb)
  end.

Definition transl_function (f: function) : res function :=
  do lb <- transf_blocks (fn_blocks f); 
  OK (mkfunction (fn_sig f) lb).

Definition transf_function (f: function) : res function :=
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (size_blocks tf.(fn_blocks))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.