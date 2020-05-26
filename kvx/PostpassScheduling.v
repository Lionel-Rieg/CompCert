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

Require Import Coqlib Errors AST Integers.
Require Import Asmblock Axioms Memory Globalenvs.
Require Import Asmblockdeps Asmblockgenproof0 Asmblockprops.
Require Peephole.

Local Open Scope error_monad_scope.

(** Oracle taking as input a basic block,
    returns a schedule expressed as a list of bundles *)
Axiom schedule: bblock -> (list (list basic)) * option control.

Extract Constant schedule => "PostpassSchedulingOracle.schedule".

Definition state' := L.mem.
Definition outcome' := option state'.

Definition bblock' := L.bblock.

Definition exec' := L.run.

Definition exec := exec_bblock.

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
      * destruct i; monadInv H; split; auto.
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
    + destruct i; monadInv EQ2;
      unfold size; simpl; rewrite app_length; rewrite Nat.add_0_r; rewrite <- Nat2Z.inj_add; rewrite Nat.add_assoc; reflexivity.
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
    + destruct i; try discriminate; congruence.
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

Inductive is_concat : bblock -> list bblock -> Prop :=
  | mk_is_concat: forall tbb lbb, concat_all lbb = OK tbb -> is_concat tbb lbb.

Definition verify_schedule (bb bb' : bblock) : res unit :=
  match bblock_simub bb bb' with
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

Lemma verify_schedule_no_header:
  forall bb bb',
  verify_schedule (no_header bb) bb' = verify_schedule bb bb'.
Proof.
  intros. unfold verify_schedule. unfold bblock_simub. unfold pure_bblock_simu_test, bblock_simu_test. rewrite trans_block_noheader_inv.
  reflexivity.
Qed.


Lemma stick_header_verify_schedule:
  forall hd bb' hbb' bb,
  stick_header hd bb' = hbb' ->
  verify_schedule bb bb' = verify_schedule bb hbb'.
Proof.
  intros. unfold verify_schedule. unfold bblock_simub, pure_bblock_simu_test, bblock_simu_test.
  rewrite <- H. rewrite trans_block_header_inv. reflexivity.
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
    + destruct i; try discriminate; inv EQ2; unfold stick_header; simpl; reflexivity.
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

Program Definition make_bblock_from_basics lb :=
  match lb with
  | nil => Error (msg "PostpassScheduling.make_bblock_from_basics")
  | b :: lb => OK {| header := nil; body := b::lb; exit := None |}
  end.

Fixpoint schedule_to_bblocks_nocontrol llb :=
  match llb with
  | nil => OK nil
  | lb :: llb => do bb <- make_bblock_from_basics lb;
                 do lbb <- schedule_to_bblocks_nocontrol llb;
                 OK (bb :: lbb)
  end.

Program Definition make_bblock_from_basics_and_control lb c := 
  match c with
  | PExpand (Pbuiltin _ _ _) => Error (msg "PostpassScheduling.make_bblock_from_basics_and_control")
  | PCtlFlow cf => OK {| header := nil; body := lb; exit := Some (PCtlFlow cf) |}
  end.
Next Obligation.
  apply wf_bblock_refl. constructor.
  - right. discriminate.
  - discriminate.
Qed.

Fixpoint schedule_to_bblocks_wcontrol llb c :=
  match llb with
  | nil => OK ((bblock_single_inst (PControl c)) :: nil)
  | lb :: nil => do bb <- make_bblock_from_basics_and_control lb c; OK (bb :: nil)
  | lb :: llb => do bb <- make_bblock_from_basics lb;
                 do lbb <- schedule_to_bblocks_wcontrol llb c;
                 OK (bb :: lbb)
  end.

Definition schedule_to_bblocks (llb: list (list basic)) (oc: option control) : res (list bblock) :=
  match oc with
  | None => schedule_to_bblocks_nocontrol llb
  | Some c => schedule_to_bblocks_wcontrol llb c
  end.

Definition do_schedule (bb: bblock) : res (list bblock) :=
  if (Z.eqb (size bb) 1) then OK (bb::nil) 
  else match (schedule bb) with (llb, oc) => schedule_to_bblocks llb oc end.

Definition verify_par_bblock (bb: bblock) : res unit :=
  if (bblock_para_check bb) then OK tt else Error (msg "PostpassScheduling.verify_par_bblock").

Fixpoint verify_par (lbb: list bblock) :=
  match lbb with
  | nil => OK tt
  | bb :: lbb => do res <- verify_par_bblock bb; verify_par lbb
  end.

Definition verified_schedule_nob (bb : bblock) : res (list bblock) :=
  let bb'  := no_header bb in
  let bb'' := Peephole.optimize_bblock bb' in
  do lbb <- do_schedule bb'';
  do tbb <- concat_all lbb;
  do sizecheck <- verify_size bb lbb;
  do schedcheck <- verify_schedule bb' tbb;
  do res <- stick_header_code (header bb) lbb;
  do parcheck <- verify_par res;
  OK res.

Lemma verified_schedule_nob_size:
  forall bb lbb, verified_schedule_nob bb = OK lbb -> size bb = size_blocks lbb.
Proof.
  intros. monadInv H. erewrite <- stick_header_code_size; eauto.
  apply verify_size_size.
  destruct x1; try discriminate. assumption.
Qed.

Lemma verified_schedule_nob_no_header_in_middle:
  forall lbb bb,
  verified_schedule_nob bb = OK lbb ->
     Forall (fun b => header b = nil) (tail lbb).
Proof.
  intros. monadInv H. eapply stick_header_code_no_header_in_middle; eauto.
  eapply concat_all_no_header_in_middle. eassumption.
Qed.

Lemma verified_schedule_nob_header:
  forall bb tbb lbb,
  verified_schedule_nob bb = OK (tbb :: lbb) ->
     header bb = header tbb
  /\ Forall (fun b => header b = nil) lbb.
Proof.
  intros. split.
  - monadInv H. unfold stick_header_code in EQ3. destruct (hd_error _); try discriminate. inv EQ3.
    simpl. reflexivity.
  - apply verified_schedule_nob_no_header_in_middle in H. assumption.
Qed.


Definition verified_schedule (bb : bblock) : res (list bblock) :=
  match exit bb with
  | Some (PExpand (Pbuiltin ef args res)) => OK (bb::nil) (* Special case for ensuring the lemma verified_schedule_builtin_idem *)
  | _ => verified_schedule_nob bb
  end.

Lemma verified_schedule_size:
  forall bb lbb, verified_schedule bb = OK lbb -> size bb = size_blocks lbb.
Proof.
  intros. unfold verified_schedule in H. destruct (exit bb). destruct c. destruct i.
  all: try (apply verified_schedule_nob_size; auto; fail).
  inv H. simpl. omega.
Qed.

Lemma verified_schedule_no_header_in_middle:
  forall lbb bb,
  verified_schedule bb = OK lbb ->
     Forall (fun b => header b = nil) (tail lbb).
Proof.
  intros. unfold verified_schedule in H. destruct (exit bb). destruct c. destruct i.
  all: try (eapply verified_schedule_nob_no_header_in_middle; eauto; fail).
  inv H. simpl. auto.
Qed.

Lemma verified_schedule_header:
  forall bb tbb lbb,
  verified_schedule bb = OK (tbb :: lbb) ->
     header bb = header tbb
  /\ Forall (fun b => header b = nil) lbb.
Proof.
  intros. unfold verified_schedule in H. destruct (exit bb). destruct c. destruct i.
  all: try (eapply verified_schedule_nob_header; eauto; fail).
  inv H. split; simpl; auto.
Qed.


Lemma verified_schedule_nob_correct:
  forall ge f bb lbb,
  verified_schedule_nob bb = OK lbb ->
  exists tbb,
     is_concat tbb lbb
  /\ bblock_simu ge f bb tbb.
Proof.
  intros. monadInv H.
  exploit stick_header_code_concat_all; eauto.
  intros (tbb & CONC & STH).
  exists tbb. split; auto. constructor; auto.
  rewrite verify_schedule_no_header in EQ2. erewrite stick_header_verify_schedule in EQ2; eauto.
  eapply bblock_simub_correct; eauto. unfold verify_schedule in EQ2.
  destruct (bblock_simub _ _); auto; try discriminate.
Qed.

Theorem verified_schedule_correct:
  forall ge f bb lbb,
  verified_schedule bb = OK lbb ->
  exists tbb,
     is_concat tbb lbb
  /\ bblock_simu ge f bb tbb.
Proof.
  intros. unfold verified_schedule in H. destruct (exit bb). destruct c. destruct i.
  all: try (eapply verified_schedule_nob_correct; eauto; fail).
  inv H. eexists. split; simpl; auto. constructor; auto. simpl; auto. constructor; auto.
Qed.

Lemma verified_schedule_builtin_idem:
  forall bb ef args res lbb,
  exit bb = Some (PExpand (Pbuiltin ef args res)) ->
  verified_schedule bb = OK lbb ->
  lbb = bb :: nil.
Proof.
  intros. unfold verified_schedule in H0. rewrite H in H0. inv H0. reflexivity.
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
