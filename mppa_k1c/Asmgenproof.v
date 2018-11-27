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

(** Correctness proof for RISC-V generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm Asmgen Machblockgen Asmblockgen.
Require Import Machblockgenproof Asmblockgenproof.

Local Open Scope linking_scope.

Definition block_passes :=
      mkpass Machblockgenproof.match_prog
  ::: mkpass Asmblockgenproof.match_prog
  ::: mkpass Asm.match_prog
  ::: pass_nil _.

Definition match_prog := pass_match (compose_passes block_passes).

Lemma transf_program_match:
  forall p tp, Asmgen.transf_program p = OK tp -> match_prog p tp.
Proof.
  intros p tp H.
  unfold Asmgen.transf_program in H. apply bind_inversion in H. destruct H.
  inversion_clear H. inversion H1. remember (Machblockgen.transf_program p) as mbp.
  unfold match_prog; simpl.
  exists mbp; split. apply Machblockgenproof.transf_program_match; auto.
  exists x; split. apply Asmblockgenproof.transf_program_match; auto.
  exists tp; split. apply Asm.transf_program_match; auto. auto.
Qed.

(** Return Address Offset *)

Definition return_address_offset (f: Mach.function) (c: Mach.code) (ofs: ptrofs) : Prop :=
  Asmblockgenproof.return_address_offset (Machblockgen.transf_function f) (Machblockgen.trans_code c) ofs.


(* TODO: put this proof in Machblocgen ? (it is specific to Machblocgen) *) 
Lemma trans_code_monotonic c i b l:
   trans_code c = b::l ->
   exists l', exists b', trans_code (i::c) = l' ++ (b'::l).
Proof.
  destruct c as [|i' c]. { rewrite trans_code_equation; intros; congruence. }
  destruct (get_code_nature (i :: i':: c)) eqn:GCNIC.
  - apply get_code_nature_empty in GCNIC. discriminate.
  - (* i=label *) 
    destruct i; try discriminate.
    rewrite! trans_code_equation;
    remember (to_bblock (Mlabel l0 :: i' :: c)) as b0.
    destruct b0 as [b0 c0].
    exploit to_bblock_label; eauto.
    intros (H1 & H2). rewrite H2; simpl; clear H2.
    intros H2; inversion H2; subst.
    exists nil; simpl; eauto.
  - (*i=basic *) 
    rewrite! trans_code_equation; destruct (to_basic_inst i) eqn:TBI; [| destruct i; discriminate].
    destruct (cn_eqdec (get_code_nature (i':: c)) IsLabel).
    + (* i'=label *) remember (to_bblock (i :: i' :: c)) as b1.
      destruct b1 as [b1 c1].
      assert (X: c1 = i'::c).
      {  generalize Heqb1; clear Heqb1. 
         unfold to_bblock.
         erewrite to_bblock_header_noLabel; try congruence.
         destruct i'; try discriminate.
         destruct i; try discriminate; simpl;
         intro X; inversion X; auto.
      }
      subst c1.
      rewrite !trans_code_equation. intro H1; rewrite H1.
      exists (b1 :: nil). simpl; eauto.
    + (* i'<>label *) remember (to_bblock (i :: i' :: c)) as b1.
      destruct b1 as [b1 c1].
      remember (to_bblock (i' :: c)) as b2.
      destruct b2 as [b2 c2].
      intro H1; assert (X: c1=c2).
      {  generalize Heqb1, Heqb2; clear Heqb1 Heqb2. 
         unfold to_bblock.
         erewrite to_bblock_header_noLabel; try congruence.
         destruct i'; simpl in * |- ; try congruence;
         destruct i; try discriminate; simpl;
          try (destruct (to_bblock_body c) as [xx yy], (to_bblock_exit yy);
              intros X1 X2; inversion X1; inversion X2; auto).
      }
      subst; inversion H1.
      exists nil; simpl; eauto.
 - (* i=cfi *)
   remember (to_cfi i) as cfi.
   intros H. destruct cfi.
   + erewrite trans_code_cfi; eauto.
     rewrite H.
     refine (ex_intro _ (_::nil) _). simpl; eauto.
   + destruct i; simpl in * |-; try congruence.
Qed.

Lemma Mach_Machblock_tail sg ros c c1 c2: c1=(Mcall sg ros :: c) -> is_tail c1 c2 -> 
  exists b, (* Machblock.exit b = Some (Machblock.MBcall sg ros) /\ *) 
     is_tail (b :: trans_code c) (trans_code c2).
Proof.
  intro H; induction 1. 
  - intros; subst.
    rewrite (trans_code_equation (Mcall sg ros :: c)).
    simpl.
    eapply ex_intro; eauto with coqlib.
  - intros; exploit IHis_tail; eauto. clear IHis_tail.
    intros (b & Hb).
    + inversion Hb; clear Hb.
      * exploit (trans_code_monotonic c2 i); eauto.
        intros (l' & b' & Hl'); rewrite Hl'.
        simpl; eauto with coqlib.
      * exploit (trans_code_monotonic c2 i); eauto.
        intros (l' & b' & Hl'); rewrite Hl'.
        simpl; eapply ex_intro.
        eapply is_tail_trans; eauto with coqlib.
Qed.

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros.
  exploit Mach_Machblock_tail; eauto.
  destruct 1.
  eapply Asmblockgenproof.return_address_exists; eauto.
Qed.


Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  unfold match_prog in TRANSF. simpl in TRANSF.
  inv TRANSF. inv H. inv H1. inv H. inv H2. inv H.
  eapply compose_forward_simulations. 
  exploit Machblockgenproof.transf_program_correct; eauto.
  unfold Machblockgenproof.inv_trans_rao. 
  intros X; apply X.
  eapply compose_forward_simulations. apply Asmblockgenproof.transf_program_correct; eauto.
  apply Asm.transf_program_correct. eauto.
Qed.

End PRESERVATION.

Instance TransfAsm: TransfLink match_prog := pass_match_link (compose_passes block_passes).

(*******************************************)
(* Stub actually needed by driver/Compiler *)

Module Asmgenproof0.

Definition return_address_offset := return_address_offset.

End Asmgenproof0.