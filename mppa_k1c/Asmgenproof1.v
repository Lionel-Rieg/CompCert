(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Errors Maps.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op Locations Mach Conventions.
Require Import Asm Asmgen Asmgenproof0.

(** Decomposition of integer constants. *)

Lemma make_immed32_sound:
  forall n,
  match make_immed32 n with
  | Imm32_single imm => n = imm
  end.
Proof.
  intros; unfold make_immed32. set (lo := Int.sign_ext 12 n).
  predSpec Int.eq Int.eq_spec n lo; auto.
(*
- auto.
- set (m := Int.sub n lo).
  assert (A: Int.eqmod (two_p 12) (Int.unsigned lo) (Int.unsigned n)) by (apply Int.eqmod_sign_ext'; compute; auto).
  assert (B: Int.eqmod (two_p 12) (Int.unsigned n - Int.unsigned  lo) 0).
  { replace 0 with (Int.unsigned n - Int.unsigned n) by omega.
    auto using Int.eqmod_sub, Int.eqmod_refl. }
  assert (C: Int.eqmod (two_p 12) (Int.unsigned m) 0).
  { apply Int.eqmod_trans with (Int.unsigned n - Int.unsigned lo); auto.
    apply Int.eqmod_divides with Int.modulus. apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
    exists (two_p (32-12)); auto. }
  assert (D: Int.modu m (Int.repr 4096) = Int.zero).
  { apply Int.eqmod_mod_eq in C. unfold Int.modu. 
    change (Int.unsigned (Int.repr 4096)) with (two_p 12). rewrite C. 
    reflexivity.
    apply two_p_gt_ZERO; omega. }
  rewrite <- (Int.divu_pow2 m (Int.repr 4096) (Int.repr 12)) by auto.
  rewrite Int.shl_mul_two_p. 
  change (two_p (Int.unsigned (Int.repr 12))) with 4096.
  replace (Int.mul (Int.divu m (Int.repr 4096)) (Int.repr 4096)) with m.
  unfold m. rewrite Int.sub_add_opp. rewrite Int.add_assoc. rewrite <- (Int.add_commut lo).
  rewrite Int.add_neg_zero. rewrite Int.add_zero. auto.
  rewrite (Int.modu_divu_Euclid m (Int.repr 4096)) at 1 by (vm_compute; congruence).
  rewrite D. apply Int.add_zero.
*)
Qed.

Lemma make_immed64_sound:
  forall n,
  match make_immed64 n with
  | Imm64_single imm => n = imm
(*| Imm64_pair hi lo => n = Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo
  | Imm64_large imm => n = imm
*)end.
Proof.
  intros; unfold make_immed64. set (lo := Int64.sign_ext 12 n).
  predSpec Int64.eq Int64.eq_spec n lo.
- auto.
- set (m := Int64.sub n lo).
  set (p := Int64.zero_ext 20 (Int64.shru m (Int64.repr 12))).
  predSpec Int64.eq Int64.eq_spec n (Int64.add (Int64.sign_ext 32 (Int64.shl p (Int64.repr 12))) lo).
  auto.
  auto.
Qed.

(** Properties of registers *)

Lemma ireg_of_not_GPR31:
  forall m r, ireg_of m = OK r -> IR r <> IR GPR31.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.

Lemma ireg_of_not_GPR31':
  forall m r, ireg_of m = OK r -> r <> GPR31.
Proof.
  intros. apply ireg_of_not_GPR31 in H. congruence.
Qed.

Hint Resolve ireg_of_not_GPR31 ireg_of_not_GPR31': asmgen.

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of RISC-V constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** 32-bit integer constants and arithmetic *)
(*
Lemma load_hilo32_correct:
  forall rd hi lo k rs m,
  exists rs',
     exec_straight ge fn (load_hilo32 rd hi lo k) rs m k rs' m
  /\ rs'#rd = Vint (Int.add (Int.shl hi (Int.repr 12)) lo)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold load_hilo32; intros. 
  predSpec Int.eq Int.eq_spec lo Int.zero.
- subst lo. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. rewrite Int.add_zero. Simpl.
  intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. 
  intros; Simpl.
Qed.
*)
Lemma loadimm32_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm32 rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm32; intros. generalize (make_immed32_sound n); intros E.
  destruct (make_immed32 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl.
  intros; Simpl.
Qed.

Lemma loadimm64_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm64 rd n k) rs m k rs' m
  /\ rs'#rd = Vlong n
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  unfold loadimm64; intros. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. 
  intros; Simpl.
Qed.

(*
Lemma opimm32_correct:
  forall (op: ireg -> ireg0 -> ireg0 -> instruction)
         (opi: ireg -> ireg0 -> int -> instruction)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_instr ge fn (op d s1 s2) rs m = Next (nextinstr (rs#d <- (sem rs##s1 rs##s2))) m) ->
  (forall d s n rs,
   exec_instr ge fn (opi d s n) rs m = Next (nextinstr (rs#d <- (sem rs##s (Vint n)))) m) ->
  forall rd r1 n k rs,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (opimm32 op opi rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs##r1 (Vint n)
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. unfold opimm32. generalize (make_immed32_sound n); intros E.
  destruct (make_immed32 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
- destruct (load_hilo32_correct GPR31 hi lo (op rd r1 GPR31 :: k) rs m)
  as (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. 
  rewrite H; eauto. auto.
  split. Simpl. simpl. rewrite B, C, E. auto. congruence. congruence.
  intros; Simpl. 
Qed.

(** 64-bit integer constants and arithmetic *)

Lemma load_hilo64_correct:
  forall rd hi lo k rs m,
  exists rs',
     exec_straight ge fn (load_hilo64 rd hi lo k) rs m k rs' m
  /\ rs'#rd = Vlong (Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold load_hilo64; intros. 
  predSpec Int64.eq Int64.eq_spec lo Int64.zero.
- subst lo. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. rewrite Int64.add_zero. Simpl.
  intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. 
  intros; Simpl.
Qed.
*)

Lemma opimm64_correct:
  forall (op: arith_name_rrr)
         (opi: arith_name_rri64)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_instr ge fn (op d s1 s2) rs m = Next (nextinstr (rs#d <- (sem rs###s1 rs###s2))) m) ->
  (forall d s n rs,
   exec_instr ge fn (opi d s n) rs m = Next (nextinstr (rs#d <- (sem rs###s (Vlong n)))) m) ->
  forall rd r1 n k rs,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (opimm64 op opi rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs##r1 (Vlong n)
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. unfold opimm64. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
(*
- destruct (load_hilo64_correct GPR31 hi lo (op rd r1 GPR31 :: k) rs m)
  as (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. 
  rewrite H; eauto. auto.
  split. Simpl. simpl. rewrite B, C, E. auto. congruence. congruence.
  intros; Simpl. 
- subst imm. econstructor; split. 
  eapply exec_straight_two. simpl; eauto. rewrite H. simpl; eauto. auto. auto.
  split. Simpl. intros; Simpl.
*)
Qed.

(** Add offset to pointer *)

Lemma addptrofs_correct:
  forall rd r1 n k rs m,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  unfold addptrofs; intros.
  destruct (Ptrofs.eq_dec n Ptrofs.zero).
- subst n. econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. destruct (rs r1); simpl; auto. rewrite Ptrofs.add_zero; auto.
  intros; Simpl.
- unfold addimm64.
  exploit (opimm64_correct Paddl Paddil Val.addl); eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto.
  rewrite B. unfold getw. destruct (rs r1); simpl; auto.
  rewrite Ptrofs.of_int64_to_int64 by auto. auto.
Qed.
(*
Lemma addptrofs_correct_2:
  forall rd r1 n k (rs: regset) m b ofs,
  r1 <> GPR31 -> rs#r1 = Vptr b of
s ->
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ rs'#rd = Vptr b (Ptrofs.add ofs n)
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. exploit (addptrofs_correct rd r1 n); eauto. intros (rs' & A & B & C).
  exists rs'; intuition eauto. 
  rewrite H0 in B. inv B. auto.
Qed.

(** Translation of conditional branches *)

Remark branch_on_GPR31:
  forall normal lbl (rs: regset) m b,
  rs#GPR31 = Val.of_bool (eqb normal b) ->
  exec_instr ge fn (if normal then Pbnew GPR31 X0 lbl else Pbeqw GPR31 X0 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct normal; simpl; rewrite H; simpl; destruct b; reflexivity. 
Qed.
*)

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
  end).

Inductive exec_straight_opt: code -> regset -> mem -> code -> regset -> mem -> Prop :=
  | exec_straight_opt_refl: forall c rs m,
      exec_straight_opt c rs m c rs m
  | exec_straight_opt_intro: forall c1 rs1 m1 c2 rs2 m2,
      exec_straight ge fn c1 rs1 m1 c2 rs2 m2 ->
      exec_straight_opt c1 rs1 m1 c2 rs2 m2.

Remark exec_straight_opt_right:
  forall c3 rs3 m3 c1 rs1 m1 c2 rs2 m2,
  exec_straight_opt c1 rs1 m1 c2 rs2 m2 ->
  exec_straight ge fn c2 rs2 m2 c3 rs3 m3 ->
  exec_straight ge fn c1 rs1 m1 c3 rs3 m3.
Proof.
  destruct 1; intros. auto. eapply exec_straight_trans; eauto. 
Qed.

Lemma transl_comp_correct:
  forall cmp r1 r2 lbl k rs m b,
  exists rs',
     exec_straight ge fn (transl_comp cmp Signed r1 r2 lbl k) rs m (Pcb BTwnez GPR31 lbl ::i k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmp_bool cmp rs##r1 rs##r2 = Some b ->
       exec_instr ge fn (Pcb BTwnez GPR31 lbl) rs' m = eval_branch fn lbl rs' m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_comp. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (nextinstr rs # GPR31 <- (compare_int (itest_for_cmp cmp Signed) rs ## r1 rs ## r2 m)) as rs'.
    simpl. assert (Val.cmp_bool Cne rs' ## GPR31 (Vint (Int.repr 0)) = Some b).
    { 
      assert (rs' ## GPR31 = (compare_int (itest_for_cmp cmp Signed) rs ## r1 rs ## r2 m)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmp_bool cmp rs##r1 rs##r2) as cmpbool.
      destruct cmp; simpl;
      unfold Val.cmp; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compu_correct:
  forall cmp r1 r2 lbl k rs m b,
  exists rs',
     exec_straight ge fn (transl_comp cmp Unsigned r1 r2 lbl k) rs m (Pcb BTwnez GPR31 lbl ::i k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpu_bool (Mem.valid_pointer m) cmp rs##r1 rs##r2 = Some b ->
       exec_instr ge fn (Pcb BTwnez GPR31 lbl) rs' m = eval_branch fn lbl rs' m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_comp. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (nextinstr rs # GPR31 <- (compare_int (itest_for_cmp cmp Unsigned) rs ## r1 rs ## r2 m)) as rs'.
    simpl. assert (Val.cmp_bool Cne rs' ## GPR31 (Vint (Int.repr 0)) = Some b).
    { 
      assert (rs' ## GPR31 = (compare_int (itest_for_cmp cmp Unsigned) rs ## r1 rs ## r2 m)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmpu_bool (Mem.valid_pointer m) cmp rs##r1 rs##r2) as cmpubool.
      destruct cmp; simpl; unfold Val.cmpu; rewrite <- Heqcmpubool; destruct cmpubool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compl_correct:
  forall cmp r1 r2 lbl k rs m b,
  exists rs',
     exec_straight ge fn (transl_compl cmp Signed r1 r2 lbl k) rs m (Pcb BTwnez GPR31 lbl ::i k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpl_bool cmp rs###r1 rs###r2 = Some b ->
       exec_instr ge fn (Pcb BTwnez GPR31 lbl) rs' m = eval_branch fn lbl rs' m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compl. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (nextinstr rs # GPR31 <- (compare_long (itest_for_cmp cmp Signed) rs ### r1 rs ### r2 m)) as rs'.
    simpl. assert (Val.cmp_bool Cne rs' ## GPR31 (Vint (Int.repr 0)) = Some b).
    { 
      assert (rs' ## GPR31 = (compare_long (itest_for_cmp cmp Signed) rs ### r1 rs ### r2 m)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmpl_bool cmp rs###r1 rs###r2) as cmpbool.
      destruct cmp; simpl;
      unfold compare_long;
      unfold Val.cmpl; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_complu_correct:
  forall cmp r1 r2 lbl k rs m b,
  exists rs',
     exec_straight ge fn (transl_compl cmp Unsigned r1 r2 lbl k) rs m (Pcb BTwnez GPR31 lbl ::i k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmplu_bool (Mem.valid_pointer m) cmp rs###r1 rs###r2 = Some b ->
       exec_instr ge fn (Pcb BTwnez GPR31 lbl) rs' m = eval_branch fn lbl rs' m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compl. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (nextinstr rs # GPR31 <- (compare_long (itest_for_cmp cmp Unsigned) rs ### r1 rs ### r2 m)) as rs'.
    simpl. assert (Val.cmp_bool Cne rs' ## GPR31 (Vint (Int.repr 0)) = Some b).
    { 
      assert (rs' ## GPR31 = (compare_long (itest_for_cmp cmp Unsigned) rs ### r1 rs ### r2 m)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmplu_bool (Mem.valid_pointer m) cmp rs###r1 rs###r2) as cmpbool.
      destruct cmp; simpl;
      unfold compare_long;
      unfold Val.cmplu; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_opt_compuimm_correct:
  forall n cmp r1 lbl k rs m b c,
  select_comp n cmp = Some c ->
  exists rs', exists insn,
     exec_straight_opt (transl_opt_compuimm n cmp r1 lbl k) rs m (insn :: k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpu_bool (Mem.valid_pointer m) cmp rs##r1 (Vint n) = Some b ->
       exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b))
  .
Proof.
  intros.
  unfold transl_opt_compuimm; rewrite H; simpl.
  remember c as c'.
  destruct c'.
  - (* c = Ceq *)
    assert (Int.eq n Int.zero = true) as H'. 
    { remember (Int.eq n Int.zero) as termz. destruct termz; auto.
      generalize H. unfold select_comp; rewrite <- Heqtermz; simpl.
      discriminate. }
    assert (n = (Int.repr 0)) as H0. { 
      destruct (Int.eq_dec n (Int.repr 0)) as [Ha|Ha]; auto. 
      generalize (Int.eq_false _ _ Ha).  unfold Int.zero in H'.
      rewrite H'. discriminate.
    }
    assert (Ceq = cmp). { 
      remember cmp as c0'. destruct c0'; auto; generalize H; unfold select_comp;
      rewrite H'; simpl; auto;
      intros; contradict H; discriminate.
    }

    exists rs, (Pcbu BTweqz r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      (*assert (Val.cmp_bool Ceq (rs r1) (Vint (Int.repr 0)) = Some b) as EVAL'S.
      { rewrite <- H2. rewrite <- H0. rewrite <- H1. auto. }*)
      auto;
      unfold eval_branch. unfold getw. rewrite H0 in H2. unfold getw in H2.
      rewrite H1. rewrite H2; auto.
  - (* c = Cne *)
    assert (Int.eq n Int.zero = true) as H'. 
    { remember (Int.eq n Int.zero) as termz. destruct termz; auto.
      generalize H. unfold select_comp; rewrite <- Heqtermz; simpl.
      discriminate. }
    assert (n = (Int.repr 0)) as H0. { 
      destruct (Int.eq_dec n (Int.repr 0)) as [Ha|Ha]; auto. 
      generalize (Int.eq_false _ _ Ha).  unfold Int.zero in H'.
      rewrite H'. discriminate.
    }
    assert (Cne = cmp). { 
      remember cmp as c0'. destruct c0'; auto; generalize H; unfold select_comp;
      rewrite H'; simpl; auto;
      intros; contradict H; discriminate.
    }
    exists rs, (Pcbu BTwnez r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      auto;
      unfold eval_branch. rewrite <- H0. rewrite H1. rewrite H2. auto.
  - (* c = Clt *) contradict H; unfold select_comp; destruct (Int.eq n Int.zero);
    destruct cmp; discriminate.
  - (* c = Cle *) contradict H; unfold select_comp; destruct (Int.eq n Int.zero);
    destruct cmp; discriminate.
  - (* c = Cgt *) contradict H; unfold select_comp; destruct (Int.eq n Int.zero);
    destruct cmp; discriminate.
  - (* c = Cge *) contradict H; unfold select_comp; destruct (Int.eq n Int.zero);
    destruct cmp; discriminate.
Qed.

Lemma transl_opt_compluimm_correct:
  forall n cmp r1 lbl k rs m b c,
  select_compl n cmp = Some c ->
  exists rs', exists insn,
     exec_straight_opt (transl_opt_compluimm n cmp r1 lbl k) rs m (insn :: k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmplu_bool (Mem.valid_pointer m) cmp rs###r1 (Vlong n) = Some b ->
       exec_instr ge fn insn rs' m = eval_branch fn lbl rs' m (Some b))
  .
Proof.
  intros.
  unfold transl_opt_compluimm; rewrite H; simpl.
  remember c as c'.
  destruct c'.
  - (* c = Ceq *)
    assert (Int64.eq n Int64.zero = true) as H'. 
    { remember (Int64.eq n Int64.zero) as termz. destruct termz; auto.
      generalize H. unfold select_compl; rewrite <- Heqtermz; simpl.
      discriminate. }
    assert (n = (Int64.repr 0)) as H0. { 
      destruct (Int64.eq_dec n (Int64.repr 0)) as [Ha|Ha]; auto. 
      generalize (Int64.eq_false _ _ Ha).  unfold Int64.zero in H'.
      rewrite H'. discriminate.
    }
    assert (Ceq = cmp). { 
      remember cmp as c0'. destruct c0'; auto; generalize H; unfold select_compl;
      rewrite H'; simpl; auto;
      intros; contradict H; discriminate.
    }

    exists rs, (Pcbu BTdeqz r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      auto;
      unfold eval_branch. rewrite H1. rewrite <- H0. destruct b; rewrite H2; auto.
  - (* c = Cne *)
    assert (Int64.eq n Int64.zero = true) as H'. 
    { remember (Int64.eq n Int64.zero) as termz. destruct termz; auto.
      generalize H. unfold select_compl; rewrite <- Heqtermz; simpl.
      discriminate. }
    assert (n = (Int64.repr 0)) as H0. { 
      destruct (Int64.eq_dec n (Int64.repr 0)) as [Ha|Ha]; auto. 
      generalize (Int64.eq_false _ _ Ha).  unfold Int64.zero in H'.
      rewrite H'. discriminate.
    }
    assert (Cne = cmp). { 
      remember cmp as c0'. destruct c0'; auto; generalize H; unfold select_compl;
      rewrite H'; simpl; auto;
      intros; contradict H; discriminate.
    }
    exists rs, (Pcbu BTdnez r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      auto;
      unfold eval_branch. rewrite H1. rewrite <- H0. destruct b; rewrite H2; auto.
  - (* c = Clt *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
  - (* c = Cle *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
  - (* c = Cgt *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
  - (* c = Cge *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
Qed.

Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = eval_branch fn lbl rs' m' (Some b)
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until m'; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)). 
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_lessdef with (map ms args) m; auto. eapply preg_vals; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
(* Ccomp *)
- exploit (transl_comp_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez GPR31 lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
(* Ccompu *)
- exploit (transl_compu_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez GPR31 lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
(* Ccompimm *)
- remember (Int.eq n Int.zero) as eqz.
  destruct eqz.
  + assert (n = (Int.repr 0)). { 
        destruct (Int.eq_dec n (Int.repr 0)) as [H|H]; auto. 
        generalize (Int.eq_false _ _ H).  unfold Int.zero in Heqeqz.
        rewrite <- Heqeqz. discriminate.
    }
    exists rs, (Pcb (btest_for_cmpswz c0) x lbl).
    split. 
    * constructor.
    * split; auto.
      destruct c0; simpl; auto;
      unfold eval_branch; rewrite <- H; unfold getw; rewrite EVAL'; auto.
  + exploit (loadimm32_correct GPR31 n); eauto. intros (rs' & A & B & C).
    exploit (transl_comp_correct c0 x GPR31 lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez GPR31 lbl).
    split.
    * constructor. apply exec_straight_trans 
         with (c2 := (transl_comp c0 Signed x GPR31 lbl k)) (rs2 := rs') (m2 := m').
      eexact A. eexact A'.
    * split; auto.
      { apply C'; auto. unfold getw. rewrite B, C; eauto with asmgen. }
      { intros. rewrite B'; eauto with asmgen. }
(* Ccompuimm *)
- remember (select_comp n c0) as selcomp.
  destruct selcomp.
  + exploit (transl_opt_compuimm_correct n c0 x lbl k). apply eq_sym. apply Heqselcomp.
    intros (rs' & i & A & B & C).
    exists rs', i.
    split.
    * apply A.
    * split; auto. apply C. apply EVAL'.
  + unfold transl_opt_compuimm. rewrite <- Heqselcomp; simpl.
    exploit (loadimm32_correct GPR31 n); eauto. intros (rs' & A & B & C).
    exploit (transl_compu_correct c0 x GPR31 lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez GPR31 lbl).
    split.
    * constructor. apply exec_straight_trans 
         with (c2 := (transl_comp c0 Unsigned x GPR31 lbl k)) (rs2 := rs') (m2 := m').
      eexact A. eexact A'.
    * split; auto.
      { apply C'; auto. unfold getw. rewrite B, C; eauto with asmgen. }
      { intros. rewrite B'; eauto with asmgen. }
(* Ccompl *)
- exploit (transl_compl_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez GPR31 lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
(* Ccomplu *)
- exploit (transl_complu_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez GPR31 lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
(* Ccomplimm *)
- remember (Int64.eq n Int64.zero) as eqz.
  destruct eqz.
  + assert (n = (Int64.repr 0)). { 
        destruct (Int64.eq_dec n (Int64.repr 0)) as [H|H]; auto. 
        generalize (Int64.eq_false _ _ H).  unfold Int64.zero in Heqeqz.
        rewrite <- Heqeqz. discriminate.
    }
    exists rs, (Pcb (btest_for_cmpsdz c0) x lbl).
    split. 
    * constructor.
    * split; auto.
      destruct c0; simpl; auto;
      unfold eval_branch; rewrite <- H; unfold getl; rewrite EVAL'; auto.
  + exploit (loadimm64_correct GPR31 n); eauto. intros (rs' & A & B & C).
    exploit (transl_compl_correct c0 x GPR31 lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez GPR31 lbl).
    split.
    * constructor. apply exec_straight_trans 
         with (c2 := (transl_compl c0 Signed x GPR31 lbl k)) (rs2 := rs') (m2 := m').
      eexact A. eexact A'.
    * split; auto.
      { apply C'; auto. unfold getl. rewrite B, C; eauto with asmgen. }
      { intros. rewrite B'; eauto with asmgen. }

(* Ccompluimm *)
- remember (select_compl n c0) as selcomp.
  destruct selcomp.
  + exploit (transl_opt_compluimm_correct n c0 x lbl k). apply eq_sym. apply Heqselcomp.
    intros (rs' & i & A & B & C).
    exists rs', i.
    split.
    * apply A.
    * split; auto. apply C. apply EVAL'.
  + unfold transl_opt_compluimm. rewrite <- Heqselcomp; simpl.
    exploit (loadimm64_correct GPR31 n); eauto. intros (rs' & A & B & C).
    exploit (transl_complu_correct c0 x GPR31 lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez GPR31 lbl).
    split.
    * constructor. apply exec_straight_trans 
         with (c2 := (transl_compl c0 Unsigned x GPR31 lbl k)) (rs2 := rs') (m2 := m').
      eexact A. eexact A'.
    * split; auto.
      { apply C'; auto. unfold getl. rewrite B, C; eauto with asmgen. }
      { intros. rewrite B'; eauto with asmgen. }
Qed.

Lemma transl_cbranch_correct_true:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = goto_label fn lbl rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed. 

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1; eauto. simpl. 
  intros (rs' & insn & A & B & C).
  exists (nextinstr rs').
  split. eapply exec_straight_opt_right; eauto. apply exec_straight_one; auto.
  intros; Simpl. 
Qed.

(** Translation of condition operators *)

Lemma transl_cond_int32s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32s cmp rd r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs##r1 rs##r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_int32u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32u cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.cmpu (Mem.valid_pointer m) cmp rs##r1 rs##r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_int64s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int64s cmp rd r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs###r1 rs###r2)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_int64u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int64u cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs###r1 rs###r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int32s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32s cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int32u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32u cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int64s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int64s cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int64u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int64u cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
+ (* cmp *)
  exploit transl_cond_int32s_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpu *)
  exploit transl_cond_int32u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B; auto.
+ (* cmpimm *)
  apply transl_condimm_int32s_correct; eauto with asmgen.
+ (* cmpuimm *)
  apply transl_condimm_int32u_correct; eauto with asmgen.
+ (* cmpl *)
  exploit transl_cond_int64s_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmplu *)
  exploit transl_cond_int64u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B, MKTOT; eauto.
+ (* cmplimm *)
  exploit transl_condimm_int64s_correct; eauto. instantiate (1 := x); eauto with asmgen. 
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpluimm *)
  exploit transl_condimm_int64u_correct; eauto. instantiate (1 := x); eauto with asmgen. 
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
Qed.

(*
+ (* cmpf *)
  destruct (transl_cond_float c0 rd x x0) as [insn normal] eqn:TR.
  fold (Val.cmpf c0 (rs x) (rs x0)).
  set (v := Val.cmpf c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split; intros; Simpl.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_float_correct with (v := Val.notbool v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpf. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; auto.
+ (* notcmpf *)
  destruct (transl_cond_float c0 rd x x0) as [insn normal] eqn:TR.
  rewrite Val.notbool_negb_3. fold (Val.cmpf c0 (rs x) (rs x0)).
  set (v := Val.cmpf c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_float_correct with (v := v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpf. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; auto.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_float_correct with (v := Val.notbool v); eauto. auto.
  split; intros; Simpl.
+ (* cmpfs *)
  destruct (transl_cond_single c0 rd x x0) as [insn normal] eqn:TR.
  fold (Val.cmpfs c0 (rs x) (rs x0)).
  set (v := Val.cmpfs c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split; intros; Simpl.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_single_correct with (v := Val.notbool v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpfs. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; auto.
+ (* notcmpfs *)
  destruct (transl_cond_single c0 rd x x0) as [insn normal] eqn:TR.
  rewrite Val.notbool_negb_3. fold (Val.cmpfs c0 (rs x) (rs x0)).
  set (v := Val.cmpfs c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_single_correct with (v := v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpfs. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; auto.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_single_correct with (v := Val.notbool v); eauto. auto.
  split; intros; Simpl.
*)

(** Some arithmetic properties. *)

Remark cast32unsigned_from_cast32signed:
  forall i, Int64.repr (Int.unsigned i) = Int64.zero_ext 32 (Int64.repr (Int.signed i)).
Proof.
  intros. apply Int64.same_bits_eq; intros. 
  rewrite Int64.bits_zero_ext, !Int64.testbit_repr by tauto.
  rewrite Int.bits_signed by tauto. fold (Int.testbit i i0).
  change Int.zwordsize with 32.
  destruct (zlt i0 32). auto. apply Int.bits_above. auto.
Qed.

Lemma cast32signed_correct:
  forall (d s: ireg) (k: code) (rs: regset) (m: mem),
  exists rs': regset,
    exec_straight ge fn (cast32signed d s k) rs m k rs' m
 /\ Val.lessdef (Val.longofint (rs s)) (rs' d)
 /\ (forall r: preg, r <> PC -> r <> d -> rs' r = rs r).
Proof.
  intros. unfold cast32signed. destruct (ireg_eq d s).
- econstructor; split.
  + apply exec_straight_one. simpl. eauto with asmgen. Simpl.
  + split.
    * rewrite e. Simpl.
    * intros. destruct r; Simpl.
- econstructor; split.
  + apply exec_straight_one. simpl. eauto with asmgen. Simpl.
  + split.
    * Simpl.
    * intros. destruct r; Simpl.
Qed.

(* Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.
- (* Omove *)
  destruct (preg_of res), (preg_of m0); inv TR; TranslOpSimpl.
- (* Oaddrsymbol *)
  destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)).
+ set (rs1 := nextinstr (rs#x <- (Genv.symbol_address ge id Ptrofs.zero))).
  exploit (addptrofs_correct x x ofs k rs1 m); eauto with asmgen. 
  intros (rs2 & A & B & C).
  exists rs2; split. 
  apply exec_straight_step with rs1 m; auto.
  split. replace ofs with (Ptrofs.add Ptrofs.zero ofs) by (apply Ptrofs.add_zero_l). 
  rewrite Genv.shift_symbol_address.
  replace (rs1 x) with (Genv.symbol_address ge id Ptrofs.zero) in B by (unfold rs1; Simpl).
  exact B.
  intros. rewrite C by eauto with asmgen. unfold rs1; Simpl.  
+ TranslOpSimpl.
- (* Oaddrstack *)
  exploit addptrofs_correct. instantiate (1 := GPR12); auto with asmgen. intros (rs' & A & B & C).
  exists rs'; split; eauto. auto with asmgen.
- (* Ocast8signed *)
  econstructor; split.
  eapply exec_straight_two. simpl;eauto. simpl;eauto. auto. auto.
  split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 24) Int.iwordsize = true) by auto. unfold getw.
  destruct (rs x0); auto; simpl. rewrite A; simpl. Simpl. unfold Val.shr. rewrite A.
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. split; reflexivity.
- (* Ocast16signed *)
  econstructor; split.
  eapply exec_straight_two. simpl;eauto. simpl;eauto. auto. auto.
  split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 16) Int.iwordsize = true) by auto. unfold getw.
  destruct (rs x0); auto; simpl. rewrite A; simpl. Simpl. unfold Val.shr. rewrite A. 
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. split; reflexivity.
- (* Oshrximm *)
  clear H. exploit Val.shrx_shr_2; eauto. intros E; subst v; clear EV.
  destruct (Int.eq n Int.zero).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ change (Int.repr 32) with Int.iwordsize. set (n' := Int.sub Int.iwordsize n).
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  apply exec_straight_one. simpl; reflexivity. auto. 
  split; intros; unfold getw; Simpl.
- (* Ocast32signed *)
  exploit cast32signed_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. split. apply B.
  intros. assert (r <> PC). { destruct r; auto; contradict H; discriminate. }
  apply C; auto.
- (* longofintu *)
  econstructor; split.
  eapply exec_straight_three. simpl; eauto. simpl; eauto. simpl; eauto. auto. auto. auto.
  split; intros; Simpl. unfold getl; unfold Pregmap.set; Simpl. destruct (PregEq.eq x0 x0).
  + destruct (rs x0); auto. simpl. 
    assert (A: Int.ltu (Int.repr 32) Int64.iwordsize' = true) by auto.
    rewrite A; simpl. rewrite A. apply Val.lessdef_same. f_equal.
    rewrite cast32unsigned_from_cast32signed. apply Int64.zero_ext_shru_shl. compute; auto.
  + contradict n. auto.
- (* Ocmp *)
  exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. eauto with asmgen.
(*
- (* intconst *)
  exploit loadimm32_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* longconst *)
  exploit loadimm64_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* floatconst *)
  destruct (Float.eq_dec n Float.zero).
+ subst n. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
- (* singleconst *)
  destruct (Float32.eq_dec n Float32.zero).
+ subst n. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
- (* stackoffset *)
  exploit addptrofs_correct. instantiate (1 := X2); auto with asmgen. intros (rs' & A & B & C).
  exists rs'; split; eauto. auto with asmgen.
- (* addimm *)
  exploit (opimm32_correct Paddw Paddiw Val.add); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen. 
- (* andimm *)
  exploit (opimm32_correct Pandw Pandiw Val.and); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* orimm *)
  exploit (opimm32_correct Porw Poriw Val.or); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* xorimm *)
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.



- (* addlimm *)
  exploit (opimm64_correct Paddl Paddil Val.addl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.

- (* andimm *)
  exploit (opimm64_correct Pandl Pandil Val.andl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* orimm *)
  exploit (opimm64_correct Porl Poril Val.orl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* xorimm *)
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* shrxlimm *)
  clear H. exploit Val.shrxl_shrl_2; eauto. intros E; subst v; clear EV.
  destruct (Int.eq n Int.zero).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ change (Int.repr 64) with Int64.iwordsize'. set (n' := Int.sub Int64.iwordsize' n).
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  apply exec_straight_one. simpl; reflexivity. auto. 
  split; intros; Simpl.
*)
Qed.


(** Memory accesses *)

Lemma indexed_memory_access_correct:
  forall mk_instr base ofs k rs m,
  base <> GPR31 ->
  exists base' ofs' rs',
     exec_straight_opt (indexed_memory_access mk_instr base ofs k) rs m
                       (mk_instr base' ofs' :: k) rs' m
  /\ Val.offset_ptr rs'#base' (eval_offset ge ofs') = Val.offset_ptr rs#base ofs
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  unfold indexed_memory_access; intros.
  (* destruct Archi.ptr64 eqn:SF. *)
  assert (Archi.ptr64 = true) as SF; auto.
- generalize (make_immed64_sound (Ptrofs.to_int64 ofs)); intros EQ.
  destruct (make_immed64 (Ptrofs.to_int64 ofs)).
+ econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl. 
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
(*
+ econstructor; econstructor; econstructor; split. 
  constructor. eapply exec_straight_two. 
  simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal. 
  rewrite <- (Ptrofs.of_int64_to_int64 SF ofs). rewrite EQ. 
  symmetry; auto with ptrofs.
+ econstructor; econstructor; econstructor; split. 
  constructor. eapply exec_straight_two. 
  simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold eval_offset. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_zero. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
(* 32 bits part, irrelevant for us
- generalize (make_immed32_sound (Ptrofs.to_int ofs)); intros EQ.
  destruct (make_immed32 (Ptrofs.to_int ofs)).
+ econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl. 
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int_to_int by auto. auto.
+ econstructor; econstructor; econstructor; split. 
  constructor. eapply exec_straight_two. 
  simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal. 
  rewrite <- (Ptrofs.of_int_to_int SF ofs). rewrite EQ. 
  symmetry; auto with ptrofs.
*)*)
Qed.

Lemma indexed_load_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) rd m,
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_load ge chunk rs m rd base ofs) ->
  forall (base: ireg) ofs k (rs: regset) v,
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR31 -> rd <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base ofs k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, r <> PC -> r <> GPR31 -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until v; intros LOAD NOT31 NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_load. rewrite B, LOAD. eauto. Simpl. 
  split; intros; Simpl.
Qed.

Lemma indexed_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) r1 m,
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_store ge chunk rs m r1 base ofs) ->
  forall (base: ireg) ofs k (rs: regset) m',
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs#r1) = Some m' ->
  base <> GPR31 -> r1 <> GPR31 -> r1 <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until m'; intros STORE NOT31 NOT31' NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_store. rewrite B, C, STORE by auto. eauto. auto. 
  intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> GPR31 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR LOAD NOT31. 
  assert (A: exists mk_instr,
                c = indexed_memory_access mk_instr base ofs k
             /\ forall base' ofs' rs',
                   exec_instr ge fn (mk_instr base' ofs') rs' m =
                   exec_load ge (chunk_of_type ty) rs' m (preg_of dst) base' ofs').
  { unfold loadind in TR.
    destruct ty, (preg_of dst); inv TR; econstructor; split; eauto. }
  destruct A as (mk_instr & B & C). subst c. 
  eapply indexed_load_access_correct; eauto with asmgen. 
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  base <> GPR31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR STORE NOT31. 
  assert (A: exists mk_instr,
                c = indexed_memory_access mk_instr base ofs k
             /\ forall base' ofs' rs',
                   exec_instr ge fn (mk_instr base' ofs') rs' m =
                   exec_store ge (chunk_of_type ty) rs' m (preg_of src) base' ofs').
  { unfold storeind in TR. destruct ty, (preg_of src); inv TR; econstructor; split; eauto. }
  destruct A as (mk_instr & B & C). subst c. 
  eapply indexed_store_access_correct; eauto with asmgen. 
Qed.


Lemma Pget_correct:
  forall (dst: gpreg) (src: preg) k (rs: regset) m,
  src = RA ->
  exists rs',
     exec_straight ge fn (Pget dst src ::i k) rs m k rs' m
  /\ rs'#dst = rs#src
  /\ forall r, r <> PC -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. econstructor; econstructor; econstructor.
- simpl. rewrite H. auto.
- Simpl.
- Simpl.
- intros. rewrite H. Simpl.
Qed.

Lemma Pset_correct:
  forall (dst: preg) (src: gpreg) k (rs: regset) m,
  dst = RA ->
  exists rs',
     exec_straight ge fn (Pset dst src ::i k) rs m k rs' m
  /\ rs'#dst = rs#src
  /\ forall r, r <> PC -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. econstructor; econstructor; econstructor; simpl.
  rewrite H. auto.
  Simpl.
  Simpl.
  intros. rewrite H. Simpl.
Qed.

Lemma loadind_ptr_correct:
  forall (base: ireg) ofs (dst: ireg) k (rs: regset) m v,
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR31 ->
  exists rs',
     exec_straight ge fn (loadind_ptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> GPR31 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_load_access_correct; eauto with asmgen.
  intros. unfold Mptr. assert (Archi.ptr64 = true). auto. rewrite H1. auto.
Qed.

Lemma storeind_ptr_correct:
  forall (base: ireg) ofs (src: ireg) k (rs: regset) m m',
  Mem.storev Mptr m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  base <> GPR31 -> src <> GPR31 ->
  exists rs',
     exec_straight ge fn (storeind_ptr src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_store_access_correct with (r1 := src); eauto with asmgen.
  intros. unfold Mptr. assert (Archi.ptr64 = true); auto.
Qed.

Lemma transl_memory_access_correct:
  forall mk_instr addr args k c (rs: regset) m v,
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  exists base ofs rs',
     exec_straight_opt c rs m (mk_instr base ofs :: k) rs' m
  /\ Val.offset_ptr rs'#base (eval_offset ge ofs) = v
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV. 
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
- (* indexed *)
  inv EV. apply indexed_memory_access_correct; eauto with asmgen.
- (* global *)
  simpl in EV. inv EV. inv TR.  econstructor; econstructor; econstructor; split.
  constructor. apply exec_straight_one. simpl; eauto. auto. 
  split; intros; Simpl. unfold eval_offset.
  assert (Val.lessdef (Val.offset_ptr (Genv.symbol_address ge i i0) Ptrofs.zero) (Genv.symbol_address ge i i0)).
  { apply Val.offset_ptr_zero. }
  remember (Genv.symbol_address ge i i0) as symbol.
  destruct symbol; auto.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + simpl. rewrite Ptrofs.add_zero; auto.
- (* stack *)
  inv TR. inv EV. apply indexed_memory_access_correct; eauto with asmgen.
Qed.

Lemma transl_load_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) addr args k c rd (rs: regset) m v v',
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_load ge chunk rs m rd base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> GPR31 -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros INSTR TR EV LOAD NOTPC. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_load. rewrite B, LOAD. reflexivity. Simpl. 
  split; intros; Simpl.
Qed.

Lemma transl_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) addr args k c r1 (rs: regset) m v m',
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_store ge chunk rs m r1 base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> PC -> r1 <> GPR31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros INSTR TR EV STORE NOTPC NOT31. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_store. rewrite B, C, STORE by auto. reflexivity. auto.
  intros; Simpl.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> GPR31 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD. 
  assert (A: exists mk_instr,
      transl_memory_access mk_instr addr args k = OK c
   /\ forall base ofs rs,
        exec_instr ge fn (mk_instr base ofs) rs m = exec_load ge chunk rs m (preg_of dst) base ofs).
  { unfold transl_load in TR; destruct chunk; ArgsInv; econstructor; (split; [eassumption|auto]). }
  destruct A as (mk_instr & B & C).
  eapply transl_load_access_correct; eauto with asmgen.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR EV STORE. 
  assert (A: exists mk_instr chunk',
      transl_memory_access mk_instr addr args k = OK c
   /\ (forall base ofs rs,
        exec_instr ge fn (mk_instr base ofs) rs m = exec_store ge chunk' rs m (preg_of src) base ofs)
   /\ Mem.storev chunk m a rs#(preg_of src) = Mem.storev chunk' m a rs#(preg_of src)).
  { unfold transl_store in TR; destruct chunk; ArgsInv;
    (econstructor; econstructor; split; [eassumption | split; [ intros; simpl; reflexivity | auto]]).
    destruct a; auto. apply Mem.store_signed_unsigned_8. 
    destruct a; auto. apply Mem.store_signed_unsigned_16. 
  }
  destruct A as (mk_instr & chunk' & B & C & D).
  rewrite D in STORE; clear D. 
  eapply transl_store_access_correct; eauto with asmgen.
Qed.

Lemma make_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (make_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#RA = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, r <> PC -> r <> RA -> r <> SP -> r <> GPR31 -> r <> GPR8 -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue. 
  rewrite chunk_of_Tptr in *.

  exploit (loadind_ptr_correct SP (fn_retaddr_ofs f) GPR8 (Pset RA GPR8
           ::i Pfreeframe (fn_stacksize f) (fn_link_ofs f) ::i k) rs tm).
  - rewrite <- (sp_val _ _ rs AG). simpl. eexact LRA'.
  - congruence.
  - intros (rs1 & A1 & B1 & C1).
    assert (agree ms (Vptr stk soff) rs1) as AG1.
    + destruct AG.
      apply mkagree; auto.
      rewrite C1; discriminate || auto.
      intro. rewrite C1; auto; destruct r; simpl; try discriminate.
    + exploit (Pset_correct RA GPR8 (Pfreeframe (fn_stacksize f) (fn_link_ofs f) ::i k) rs1 tm). auto.
      intros (rs2 & A2 & B2 & C2).
      econstructor; econstructor; split.
      * eapply exec_straight_trans.
        { eexact A1. }
        { eapply exec_straight_trans.
          { eapply A2. }
          { apply exec_straight_one. simpl.
            rewrite (C2 GPR12) by auto with asmgen. rewrite <- (sp_val _ _ rs1 AG1). simpl; rewrite LP'.
            rewrite FREE'; eauto. auto. } }
      * split. apply agree_nextinstr. apply agree_set_other; auto with asmgen. 
    apply agree_change_sp with (Vptr stk soff).
    apply agree_exten with rs; auto. intros; rewrite C2; auto with asmgen.
    eapply parent_sp_def; eauto.
  split. auto.
  split. Simpl. rewrite B2. auto.
  split. Simpl. 
  intros. Simpl.
  rewrite C2; auto.
Qed.

End CONSTRUCTORS.


 
