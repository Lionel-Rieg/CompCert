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

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.
Require Import Mach.
Require Import Linking.
Require Import Machblock.

Inductive Machblock_inst: Type :=
| MB_label (lbl: label) 
| MB_basic (bi: basic_inst)
| MB_cfi   (cfi: control_flow_inst).

Definition trans_inst (i:Mach.instruction) : Machblock_inst :=
  match i with
  | Mcall sig ros         => MB_cfi (MBcall sig ros)
  | Mtailcall sig ros     => MB_cfi (MBtailcall sig ros)
  | Mbuiltin ef args res  => MB_cfi (MBbuiltin ef args res)
  | Mgoto lbl             => MB_cfi (MBgoto lbl)
  | Mcond cond args lbl   => MB_cfi (MBcond cond args lbl)
  | Mjumptable arg tbl    => MB_cfi (MBjumptable arg tbl)
  | Mreturn               => MB_cfi (MBreturn)
  | Mgetstack ofs ty dst          => MB_basic (MBgetstack ofs ty dst)
  | Msetstack src ofs ty          => MB_basic (MBsetstack src ofs ty)
  | Mgetparam ofs ty dst          => MB_basic (MBgetparam ofs ty dst)
  | Mop       op args res         => MB_basic (MBop       op args res)
  | Mload trap chunk addr args dst=> MB_basic (MBload trap chunk addr args dst)
  | Mstore    chunk addr args src => MB_basic (MBstore    chunk addr args src)
  | Mlabel l => MB_label l
  end.

Definition empty_bblock:={| header := nil; body := nil; exit := None |}.
Extraction Inline empty_bblock.

Definition add_label l bb:={| header := l::(header bb); body := (body bb); exit := (exit bb) |}. 
Extraction Inline add_label.

Definition add_basic bi bb :={| header := nil; body := bi::(body bb); exit := (exit bb) |}.
Extraction Inline add_basic.

Definition cfi_bblock cfi:={| header := nil; body := nil; exit := Some cfi |}.
Extraction Inline cfi_bblock.

Definition add_to_new_bblock (i:Machblock_inst) : bblock :=
  match i with
  | MB_label l => add_label l empty_bblock
  | MB_basic i => add_basic i empty_bblock
  | MB_cfi i => cfi_bblock i
  end.

(** Adding an instruction to the beginning of a bblock list
  * Either adding the instruction to the head of the list,
  * or create a new bblock with the instruction *)
Definition add_to_code (i:Machblock_inst) (bl:code) : code :=
  match bl with
  | bh::bl0 => match i with
              | MB_label l => add_label l bh::bl0
              | MB_cfi i0 => cfi_bblock i0::bl
              | MB_basic i0 => match header bh with
                               |_::_ => add_basic i0 empty_bblock::bl
                               | nil => add_basic i0 bh::bl0
                               end
              end
  | _ => add_to_new_bblock i::nil
  end.
  
Fixpoint trans_code_rev (c: Mach.code) (bl:code) : code := 
  match c with
  | nil => bl
  | i::c0 =>
    trans_code_rev c0 (add_to_code (trans_inst i) bl)
  end.

Function trans_code (c: Mach.code) : code :=
  trans_code_rev (List.rev_append c nil) nil.

Definition transf_function (f: Mach.function) : function :=
  {| fn_sig:=Mach.fn_sig f;
     fn_code:=trans_code (Mach.fn_code f);
     fn_stacksize := Mach.fn_stacksize f;
     fn_link_ofs := Mach.fn_link_ofs f;
     fn_retaddr_ofs := Mach.fn_retaddr_ofs f
 |}.

Definition transf_fundef (f: Mach.fundef) : fundef :=
  transf_fundef transf_function f.

Definition transf_program (src: Mach.program) : program :=
  transform_program transf_fundef src.


(** Abstracting trans_code *)

Inductive is_end_block: Machblock_inst -> code -> Prop :=
  | End_empty mbi: is_end_block mbi nil
  | End_basic bi bh bl: header bh <> nil -> is_end_block (MB_basic bi) (bh::bl)
  | End_cfi cfi bl: bl <> nil -> is_end_block (MB_cfi cfi) bl. 

Local Hint Resolve End_empty End_basic End_cfi: core.

Inductive is_trans_code: Mach.code -> code -> Prop :=
  | Tr_nil: is_trans_code nil nil
  | Tr_end_block i c bl:
      is_trans_code c bl ->
      is_end_block (trans_inst i) bl ->
      is_trans_code (i::c) (add_to_new_bblock (trans_inst i)::bl)
  | Tr_add_label i l bh c bl:
      is_trans_code c (bh::bl) ->
      i = Mlabel l ->
      is_trans_code (i::c) (add_label l bh::bl)
  | Tr_add_basic i bi bh c bl:
      is_trans_code c (bh::bl) ->
      trans_inst i = MB_basic bi ->
      header bh = nil ->
      is_trans_code (i::c) (add_basic bi bh::bl).

Local Hint Resolve Tr_nil Tr_end_block: core.

Lemma add_to_code_is_trans_code i c bl:
  is_trans_code c bl ->
  is_trans_code (i::c) (add_to_code (trans_inst i) bl).
Proof.
  destruct bl as [|bh0 bl]; simpl.
  - intro H. inversion H. subst. eauto.
  - remember (trans_inst i) as ti.
    destruct ti as [l|bi|cfi].
    + intros; eapply Tr_add_label; eauto. destruct i; simpl in * |- *; congruence.
    + intros. remember (header bh0) as hbh0. destruct hbh0 as [|b].
      * eapply Tr_add_basic; eauto.
      * cutrewrite (add_basic bi empty_bblock = add_to_new_bblock (MB_basic bi)); auto.
        rewrite Heqti; eapply Tr_end_block; eauto.
        rewrite <- Heqti. eapply End_basic. congruence.
    + intros.
      cutrewrite (cfi_bblock cfi = add_to_new_bblock (MB_cfi cfi)); auto.
      rewrite Heqti. eapply Tr_end_block; eauto.
      rewrite <- Heqti. eapply End_cfi. congruence.
Qed.

Local Hint Resolve add_to_code_is_trans_code: core.

Lemma trans_code_is_trans_code_rev c1: forall c2 mbi, 
  is_trans_code c2 mbi ->
  is_trans_code (rev_append c1 c2) (trans_code_rev c1 mbi).
Proof.
  induction c1 as [| i c1]; simpl; auto.
Qed.

Lemma trans_code_is_trans_code c: is_trans_code c (trans_code c).
Proof.
  unfold trans_code.
  rewrite <- rev_alt.
  rewrite <- (rev_involutive c) at 1.
  rewrite rev_alt at 1.
  apply trans_code_is_trans_code_rev; auto.
Qed.

Lemma add_to_code_is_trans_code_inv i c bl:
  is_trans_code (i::c) bl -> exists bl0, is_trans_code c bl0 /\ bl = add_to_code (trans_inst i) bl0.
Proof.
  intro H; inversion H as [|H0 H1 bl0| | H0 bi bh H1 bl0]; clear H; subst; (repeat econstructor); eauto.
  + (* case Tr_end_block *) inversion H3; subst; simpl; auto.
     * destruct (header bh); congruence.
     * destruct bl0; simpl; congruence.
  + (* case Tr_add_basic *) rewrite H3. simpl. destruct (header bh); congruence.
Qed. 

Lemma trans_code_is_trans_code_rev_inv c1: forall c2 mbi, 
  is_trans_code (rev_append c1 c2) mbi ->
  exists mbi0, is_trans_code c2 mbi0 /\ mbi=trans_code_rev c1 mbi0.
Proof.
  induction c1 as [| i c1]; simpl; eauto.
  intros; exploit IHc1; eauto.
  intros (mbi0 & H1 & H2); subst.
  exploit add_to_code_is_trans_code_inv; eauto.
  intros. destruct H0 as [mbi1 [H2 H3]].
  exists mbi1. split; congruence.
Qed.

Local Hint Resolve trans_code_is_trans_code: core.

Theorem is_trans_code_inv c bl: is_trans_code c bl <-> bl=(trans_code c).
Proof.
  constructor; intros; subst; auto.
  unfold trans_code.
  exploit (trans_code_is_trans_code_rev_inv (rev_append c nil) nil bl); eauto.
  * rewrite <- rev_alt.
    rewrite <- rev_alt.
    rewrite (rev_involutive c).
    apply H.
  * intros.
    destruct H0 as [mbi [H0 H1]].
    inversion H0. subst. reflexivity.
Qed.
