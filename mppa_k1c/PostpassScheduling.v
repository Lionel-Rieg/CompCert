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
Require Import Asmblock Axioms.

Local Open Scope error_monad_scope.

(** Oracle taking as input a basic block,
    returns a schedule expressed as a list of bundles *)
Axiom schedule: bblock -> list bblock.

Extract Constant schedule => "PostpassSchedulingOracle.schedule".

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

Definition verify_schedule (bb bb' : bblock) : res unit := OK tt.

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

Program Definition stick_header (h : list label) (bb : bblock) := {| header := h; body := body bb; exit := exit bb |}.
Next Obligation.
  destruct bb; simpl. assumption.
Defined.

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