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
Require Import Asmblock.

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

Program Definition verified_schedule (bb : bblock) : res (list bblock) :=
  let bb' := {| header := nil; body := body bb; exit := exit bb |} in
  let lbb := schedule bb' in
  do tbb <- concat_all lbb;
  do check <- verify_schedule bb' tbb;
  match (head lbb) with
  | None => Error (msg "PostpassScheduling.verified_schedule: empty schedule")
  | Some fst => OK ({| header := header bb; body := body fst; exit := exit fst |} :: tail lbb)
  end.
Next Obligation.
  destruct bb; simpl. assumption.
Qed. Next Obligation.
  destruct fst; simpl. assumption.
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