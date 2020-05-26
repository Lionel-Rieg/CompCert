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

(** Common definition and proofs on Asmblock required by various modules *)

Require Import Coqlib.
Require Import Integers.
Require Import Memory.
Require Import Globalenvs.
Require Import Values.
Require Import Asmblock.
Require Import Axioms.

Definition bblock_simu (ge: Genv.t fundef unit) (f: function) (bb bb': bblock) :=
  forall rs m,
    exec_bblock ge f bb rs m <> Stuck ->
    exec_bblock ge f bb rs m = exec_bblock ge f bb' rs m.
    
Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma preg_of_data:
  forall r, data_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.
Hint Resolve preg_of_data: asmgen.

Lemma data_diff:
  forall r r',
  data_preg r = true -> data_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve data_diff: asmgen.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
Qed.

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence.
Qed.

Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.


Lemma nextblock_pc:
  forall b rs, (nextblock b rs)#PC = Val.offset_ptr rs#PC (Ptrofs.repr (size b)).
Proof.
  intros. apply Pregmap.gss.
Qed.

Lemma nextblock_inv:
  forall b r rs, r <> PC -> (nextblock b rs)#r = rs#r.
Proof.
  intros. unfold nextblock. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextblock_inv1:
  forall b r rs, data_preg r = true -> (nextblock b rs)#r = rs#r.
Proof.
  intros. apply nextblock_inv. red; intro; subst; discriminate.
Qed.

Ltac Simplif :=
  ((rewrite nextblock_inv by eauto with asmgen)
  || (rewrite nextblock_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextblock_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)
  ); auto with asmgen.

Ltac Simpl := repeat Simplif.

(* For Asmblockgenproof0 *)

Theorem exec_basic_instr_pc:
  forall ge b rs1 m1 rs2 m2,
  exec_basic_instr ge b rs1 m1 = Next rs2 m2 ->
  rs2 PC = rs1 PC.
Proof.
  intros. destruct b; try destruct i; try destruct i.
  all: try (inv H; Simpl).
  1-10: unfold parexec_load_offset in H1; destruct (eval_offset ofs); try discriminate; destruct (Mem.loadv _ _ _); unfold parexec_incorrect_load in *; destruct trap; try discriminate; unfold concrete_default_notrap_load_value in *; inv H1; Simpl; fail.

  1-20: unfold parexec_load_reg, parexec_load_regxs in H1; destruct (Mem.loadv _ _ _); unfold parexec_incorrect_load in *; destruct trap; try discriminate; unfold concrete_default_notrap_load_value in *; inv H1; Simpl; fail.

  { (* PLoadQRRO *)
    unfold  parexec_load_q_offset in H1.
    destruct (gpreg_q_expand _) as [r0 r1] in H1.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    inv H1. Simpl. }
  { (* PLoadORRO *)
    unfold  parexec_load_o_offset in H1.
    destruct (gpreg_o_expand _) as [[[r0 r1] r2] r3] in H1.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    inv H1. Simpl. }
  1-8: unfold parexec_store_offset in H1; destruct (eval_offset ofs); try discriminate; destruct (Mem.storev _ _ _); [inv H1; auto | discriminate]; fail.
  1-8: unfold parexec_store_reg in H1; destruct (Mem.storev _ _ _); [inv H1; Simpl | discriminate]; auto; fail.
  1-8: unfold parexec_store_regxs in H1; destruct (Mem.storev _ _ _); [inv H1; Simpl | discriminate]; auto; fail.
  
  { (* PStoreQRRO *)
    unfold  parexec_store_q_offset in H1.
    destruct (gpreg_q_expand _) as [r0 r1] in H1.
    unfold eval_offset in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    inv H1. Simpl. reflexivity. }
  { (* PStoreORRO *)
    unfold  parexec_store_o_offset in H1.
    destruct (gpreg_o_expand _) as [[[r0 r1] r2] r3] in H1.
    unfold eval_offset in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    inv H1. Simpl. reflexivity. }
  - destruct (Mem.alloc _ _ _). destruct (Mem.store _ _ _ _ _). inv H1. Simpl. discriminate.
  - destruct (Mem.loadv _ _ _); try discriminate. destruct (rs1 _); try discriminate.
    destruct (Mem.free _ _ _ _). inv H1. Simpl. discriminate.
  - destruct rs; try discriminate. inv H1. Simpl.
  - destruct rd; try discriminate. inv H1; Simpl.
  - reflexivity.
Qed.

(* For PostpassSchedulingproof *)

Lemma regset_double_set:
  forall r1 r2 (rs: regset) v1 v2,
  r1 <> r2 ->
  (rs # r1 <- v1 # r2 <- v2) = (rs # r2 <- v2 # r1 <- v1).
Proof.
  intros. apply functional_extensionality. intros r. destruct (preg_eq r r1).
  - subst. rewrite Pregmap.gso; auto. repeat (rewrite Pregmap.gss). auto.
  - destruct (preg_eq r r2).
    + subst. rewrite Pregmap.gss. rewrite Pregmap.gso; auto. rewrite Pregmap.gss. auto.
    + repeat (rewrite Pregmap.gso; auto).
Qed.

Lemma next_eq:
  forall (rs rs': regset) m m',
  rs = rs' -> m = m' -> Next rs m = Next rs' m'.
Proof.
  intros; apply f_equal2; auto.
Qed.

Lemma exec_load_offset_pc_var:
  forall trap t rs m rd ra ofs rs' m' v,
  exec_load_offset trap t rs m rd ra ofs = Next rs' m' ->
  exec_load_offset trap t rs # PC <- v m rd ra ofs = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_load_offset in *. unfold parexec_load_offset in *. rewrite Pregmap.gso; try discriminate. destruct (eval_offset ofs); try discriminate.
  destruct (Mem.loadv _ _ _).
  - inv H. apply next_eq; auto. apply functional_extensionality. intros. rewrite regset_double_set; auto. discriminate.
  - unfold parexec_incorrect_load in *.
    destruct trap; try discriminate.
    inv H. apply next_eq; auto. apply functional_extensionality. intros. rewrite regset_double_set; auto. discriminate.
Qed.

Lemma exec_load_reg_pc_var:
  forall trap t rs m rd ra ro rs' m' v,
    exec_load_reg trap t rs m rd ra ro = Next rs' m' ->
    exec_load_reg trap t rs # PC <- v m rd ra ro = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_load_reg in *. unfold parexec_load_reg in *. rewrite Pregmap.gso; try discriminate.
  destruct (Mem.loadv _ _ _).
  - inv H. apply next_eq; auto. apply functional_extensionality. intros. rewrite regset_double_set; auto. discriminate.
  - unfold parexec_incorrect_load in *.
    destruct trap; try discriminate.
    inv H. apply next_eq; auto. apply functional_extensionality. intros. rewrite regset_double_set; auto. discriminate.
Qed.

Lemma exec_load_regxs_pc_var:
  forall trap t rs m rd ra ro rs' m' v,
  exec_load_regxs trap t rs m rd ra ro = Next rs' m' ->
  exec_load_regxs trap t rs # PC <- v m rd ra ro = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_load_regxs in *. unfold parexec_load_regxs in *. rewrite Pregmap.gso; try discriminate.
  destruct (Mem.loadv _ _ _).
  - inv H. apply next_eq; auto. apply functional_extensionality. intros. rewrite regset_double_set; auto. discriminate.
  - unfold parexec_incorrect_load in *.
    destruct trap; try discriminate.
    inv H. apply next_eq; auto. apply functional_extensionality. intros. rewrite regset_double_set; auto. discriminate.
Qed.

Lemma exec_load_offset_q_pc_var:
  forall rs m rd ra ofs rs' m' v,
  exec_load_q_offset rs m rd ra ofs = Next rs' m' ->
  exec_load_q_offset rs # PC <- v m rd ra ofs = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_load_q_offset in *. unfold parexec_load_q_offset in *.
  destruct (gpreg_q_expand rd) as [rd0 rd1].
  (* destruct (ireg_eq rd0 ra); try discriminate. *)
  rewrite Pregmap.gso; try discriminate.
  destruct (Mem.loadv _ _ _); try discriminate.
  inv H.
  destruct (Mem.loadv _ _ _); try discriminate.
  inv H1. f_equal.
  rewrite (regset_double_set PC rd0) by discriminate.
  rewrite (regset_double_set PC rd1) by discriminate.
  reflexivity.
Qed.

Lemma exec_load_offset_o_pc_var:
  forall rs m rd ra ofs rs' m' v,
  exec_load_o_offset rs m rd ra ofs = Next rs' m' ->
  exec_load_o_offset rs # PC <- v m rd ra ofs = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_load_o_offset in *. unfold parexec_load_o_offset in *.
  destruct (gpreg_o_expand rd) as [[[rd0 rd1] rd2] rd3].
(*
  destruct (ireg_eq rd0 ra); try discriminate.
  destruct (ireg_eq rd1 ra); try discriminate.
  destruct (ireg_eq rd2 ra); try discriminate.
*)
  rewrite Pregmap.gso; try discriminate.
  simpl in *.
  destruct (Mem.loadv _ _ _); try discriminate.
  destruct (Mem.loadv _ _ _); try discriminate.
  destruct (Mem.loadv _ _ _); try discriminate.
  destruct (Mem.loadv _ _ _); try discriminate.
  rewrite (regset_double_set PC rd0) by discriminate.
  rewrite (regset_double_set PC rd1) by discriminate.
  rewrite (regset_double_set PC rd2) by discriminate.
  rewrite (regset_double_set PC rd3) by discriminate.
  inv H.
  trivial.
Qed.

Lemma exec_store_offset_pc_var:
  forall t rs m rd ra ofs rs' m' v,
  exec_store_offset t rs m rd ra ofs = Next rs' m' ->
  exec_store_offset t rs # PC <- v m rd ra ofs = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_store_offset in *. unfold parexec_store_offset in *. rewrite Pregmap.gso; try discriminate.
  destruct (eval_offset ofs); try discriminate.
  destruct (Mem.storev _ _ _).
  - inv H. apply next_eq; auto.
  - discriminate.
Qed.

Lemma exec_store_q_offset_pc_var:
  forall rs m rd ra ofs rs' m' v,
  exec_store_q_offset rs m rd ra ofs = Next rs' m' ->
  exec_store_q_offset rs # PC <- v m rd ra ofs = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_store_q_offset in *. unfold parexec_store_q_offset in *. rewrite Pregmap.gso; try discriminate.
  simpl in *.
  destruct (gpreg_q_expand _) as [s0 s1].
  destruct (Mem.storev _ _ _); try discriminate.
  destruct (Mem.storev _ _ _); try discriminate.
  inv H. apply next_eq; auto.
Qed.

Lemma exec_store_o_offset_pc_var:
  forall rs m rd ra ofs rs' m' v,
  exec_store_o_offset rs m rd ra ofs = Next rs' m' ->
  exec_store_o_offset rs # PC <- v m rd ra ofs = Next rs' # PC <- v m'.
Proof.
  intros.
  unfold exec_store_o_offset in *. unfold parexec_store_o_offset in *.
  destruct (gpreg_o_expand _) as [[[s0 s1] s2] s3].
  destruct (Mem.storev _ _ _); try discriminate.
  destruct (Mem.storev _ _ _); try discriminate.
  destruct (Mem.storev _ _ _); try discriminate.
  destruct (Mem.storev _ _ _); try discriminate.
  inv H.
  trivial.
Qed.
  
Lemma exec_store_reg_pc_var:
  forall t rs m rd ra ro rs' m' v,
  exec_store_reg t rs m rd ra ro = Next rs' m' ->
  exec_store_reg t rs # PC <- v m rd ra ro = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_store_reg in *. unfold parexec_store_reg in *. rewrite Pregmap.gso; try discriminate.
  destruct (Mem.storev _ _ _).
  - inv H. apply next_eq; auto.
  - discriminate.
Qed.

Lemma exec_store_regxs_pc_var:
  forall t rs m rd ra ro rs' m' v,
  exec_store_regxs t rs m rd ra ro = Next rs' m' ->
  exec_store_regxs t rs # PC <- v m rd ra ro = Next rs' # PC <- v m'.
Proof.
  intros. unfold exec_store_regxs in *. unfold parexec_store_regxs in *. rewrite Pregmap.gso; try discriminate.
  destruct (Mem.storev _ _ _).
  - inv H. apply next_eq; auto.
  - discriminate.
Qed.

Theorem exec_basic_instr_pc_var:
  forall ge i rs m rs' m' v,
  exec_basic_instr ge i rs m = Next rs' m' ->
  exec_basic_instr ge i (rs # PC <- v) m = Next (rs' # PC <- v) m'.
Proof.
  intros. unfold exec_basic_instr in *. unfold bstep in *. destruct i.
  - unfold exec_arith_instr in *. destruct i; destruct i.
      all: try (exploreInst; inv H; apply next_eq; auto;
      apply functional_extensionality; intros; rewrite regset_double_set; auto; discriminate).
(* 
      (* Some cases treated seperately because exploreInst destructs too much *)
      all: try (inv H; apply next_eq; auto; apply functional_extensionality; intros; rewrite regset_double_set; auto; discriminate). *)
  - destruct i.
    + exploreInst; apply exec_load_offset_pc_var; auto.
    + exploreInst; apply exec_load_reg_pc_var; auto.
    + exploreInst; apply exec_load_regxs_pc_var; auto.
    + apply exec_load_offset_q_pc_var; auto.
    + apply exec_load_offset_o_pc_var; auto.
  - destruct i.
    + exploreInst; apply exec_store_offset_pc_var; auto.
    + exploreInst; apply exec_store_reg_pc_var; auto.
    + exploreInst; apply exec_store_regxs_pc_var; auto.
    + apply exec_store_q_offset_pc_var; auto.
    + apply exec_store_o_offset_pc_var; auto.
  - destruct (Mem.alloc _ _ _) as (m1 & stk). repeat (rewrite Pregmap.gso; try discriminate).
    destruct (Mem.storev _ _ _ _); try discriminate.
    inv H. apply next_eq; auto. apply functional_extensionality. intros.
    rewrite (regset_double_set GPR32 PC); try discriminate.
    rewrite (regset_double_set GPR12 PC); try discriminate.
    rewrite (regset_double_set FP PC); try discriminate. reflexivity.
  - repeat (rewrite Pregmap.gso; try discriminate).
    destruct (Mem.loadv _ _ _); try discriminate.
    destruct (rs GPR12); try discriminate.
    destruct (Mem.free _ _ _ _); try discriminate.
    inv H. apply next_eq; auto.
    rewrite (regset_double_set GPR32 PC).
    rewrite (regset_double_set GPR12 PC). reflexivity.
    all: discriminate.
  - destruct rs0; try discriminate. inv H. apply next_eq; auto.
    repeat (rewrite Pregmap.gso; try discriminate). apply regset_double_set; discriminate.
  - destruct rd; try discriminate. inv H. apply next_eq; auto.
    repeat (rewrite Pregmap.gso; try discriminate). apply regset_double_set; discriminate.
  - inv H. apply next_eq; auto.
Qed.


