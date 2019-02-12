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

Fixpoint concat_all (lbb: list bblock) : res bblock :=
  match lbb with
  | nil => Error (msg "PostpassSchedulingproof.concatenate: empty list")
  | bb::nil => OK bb
  | bb::lbb =>
      do bb' <- concat_all lbb;
      concat2 bb bb'
  end.

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