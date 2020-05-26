(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           Xavier Leroy       INRIA Paris-Rocquencourt       *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** * Proof of correctness for individual instructions *)

Require Import Coqlib Errors Maps.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op Locations Machblock Conventions.
Require Import Asmblock Asmblockgen Asmblockgenproof0 Asmblockprops.
Require Import Chunks.

Import PArithCoercions.

(** Decomposition of integer constants. *)

Lemma make_immed32_sound:
  forall n,
  match make_immed32 n with
  | Imm32_single imm => n = imm
  end.
Proof.
  intros; unfold make_immed32. set (lo := Int.sign_ext 12 n).
  predSpec Int.eq Int.eq_spec n lo; auto.
Qed.

Lemma make_immed64_sound:
  forall n,
  match make_immed64 n with
  | Imm64_single imm => n = imm
  end.
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

Lemma ireg_of_not_RTMP:
  forall m r, ireg_of m = OK r -> IR r <> IR RTMP.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.

Lemma ireg_of_not_RTMP':
  forall m r, ireg_of m = OK r -> r <> RTMP.
Proof.
  intros. apply ireg_of_not_RTMP in H. congruence.
Qed.

Hint Resolve ireg_of_not_RTMP ireg_of_not_RTMP': asmgen.


(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextblock_inv by eauto with asmgen)
  || (rewrite nextblock_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextblock_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)
  ); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of RISC-V constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

Lemma loadimm32_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge (loadimm32 rd n ::g k) rs m k rs' m
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
     exec_straight ge (loadimm64 rd n ::g k) rs m k rs' m
  /\ rs'#rd = Vlong n
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  unfold loadimm64; intros. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. 
  intros; Simpl.
Qed.

Lemma opimm64_correct:
  forall (op: arith_name_rrr)
         (opi: arith_name_rri64)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_basic_instr ge (op d s1 s2) rs m = Next ((rs#d <- (sem rs#s1 rs#s2))) m) ->
  (forall d s n rs,
   exec_basic_instr ge (opi d s n) rs m = Next ((rs#d <- (sem rs#s (Vlong n)))) m) ->
  forall rd r1 n k rs,
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (opimm64 op opi rd r1 n ::g k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 (Vlong n)
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. unfold opimm64. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
Qed.

(** Add offset to pointer *)

Lemma addptrofs_correct:
  forall rd r1 n k rs m,
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (addptrofs rd r1 n ::g k) rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
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
  rewrite B. destruct (rs r1); simpl; auto.
  rewrite Ptrofs.of_int64_to_int64 by auto. auto.
Qed.

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

Inductive exec_straight_opt: list instruction -> regset -> mem -> list instruction -> regset -> mem -> Prop :=
  | exec_straight_opt_refl: forall c rs m,
      exec_straight_opt c rs m c rs m
  | exec_straight_opt_intro: forall c1 rs1 m1 c2 rs2 m2,
      exec_straight ge c1 rs1 m1 c2 rs2 m2 ->
      exec_straight_opt c1 rs1 m1 c2 rs2 m2.

Remark exec_straight_opt_right:
  forall c3 rs3 m3 c1 rs1 m1 c2 rs2 m2,
  exec_straight_opt c1 rs1 m1 c2 rs2 m2 ->
  exec_straight ge c2 rs2 m2 c3 rs3 m3 ->
  exec_straight ge c1 rs1 m1 c3 rs3 m3.
Proof.
  destruct 1; intros. auto. eapply exec_straight_trans; eauto. 
Qed.

Lemma transl_comp_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_comp cmp Signed r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmp_bool cmp rs#r1 rs#r2 = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_comp. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_int (itest_for_cmp cmp Signed) rs # r1 rs # r2)) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_int (itest_for_cmp cmp Signed) rs # r1 rs # r2)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmp_bool cmp rs#r1 rs#r2) as cmpbool.
      destruct cmp; simpl;
      unfold Val.cmp; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compi_correct:
  forall cmp r1 n lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_compi cmp Signed r1 n lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmp_bool cmp rs#r1 (Vint n) = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compi. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_int (itest_for_cmp cmp Signed) rs # r1 (Vint n))) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_int (itest_for_cmp cmp Signed) rs # r1 (Vint n))).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmp_bool cmp rs#r1 (Vint n)) as cmpbool.
      destruct cmp; simpl;
      unfold Val.cmp; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compu_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_comp cmp Unsigned r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ (Val_cmpu_bool cmp rs#r1 rs#r2 = Some b ->
       exec_control ge fn (Some (PCtlFlow ((Pcb BTwnez RTMP lbl)))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_comp. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_int (itest_for_cmp cmp Unsigned) rs # r1 rs # r2)) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_int (itest_for_cmp cmp Unsigned) rs # r1 rs # r2)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val_cmpu_bool cmp rs#r1 rs#r2) as cmpubool.
      destruct cmp; simpl; unfold Val_cmpu;
        rewrite <- Heqcmpubool; destruct cmpubool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compui_correct:
  forall cmp r1 n lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_compi cmp Unsigned r1 n lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ (Val_cmpu_bool cmp rs#r1 (Vint n) = Some b ->
       exec_control ge fn (Some (PCtlFlow ((Pcb BTwnez RTMP lbl)))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compi. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_int (itest_for_cmp cmp Unsigned) rs # r1 (Vint n))) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_int (itest_for_cmp cmp Unsigned) rs # r1 (Vint n))).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val_cmpu_bool cmp rs#r1 (Vint n)) as cmpubool.
      destruct cmp; simpl; unfold Val_cmpu;
        rewrite <- Heqcmpubool; destruct cmpubool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compl_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_compl cmp Signed r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpl_bool cmp rs#r1 rs#r2 = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compl. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_long (itest_for_cmp cmp Signed) rs # r1 rs # r2)) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_long (itest_for_cmp cmp Signed) rs # r1 rs # r2)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmpl_bool cmp rs#r1 rs#r2) as cmpbool.
      destruct cmp; simpl;
      unfold compare_long, Val.cmpl;
      rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compil_correct:
  forall cmp r1 n lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_compil cmp Signed r1 n lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpl_bool cmp rs#r1 (Vlong n) = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compil. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_long (itest_for_cmp cmp Signed) rs # r1 (Vlong n))) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_long (itest_for_cmp cmp Signed) rs # r1 (Vlong n))).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val.cmpl_bool cmp rs#r1 (Vlong n)) as cmpbool.
      destruct cmp; simpl;
      unfold compare_long, Val.cmpl;
      rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma swap_comparison_cmpf_eq:
  forall v1 v2 cmp,
  (Val.cmpf cmp v1 v2) = (Val.cmpf (swap_comparison cmp) v2 v1).
Proof.
  intros. unfold Val.cmpf. unfold Val.cmpf_bool. destruct v1; destruct v2; auto.
  rewrite Float.cmp_swap. auto.
Qed.

Lemma swap_comparison_cmpf_bool:
  forall cmp ft v1 v2,
  ftest_for_cmp cmp = Reversed ft ->
  Val.cmpf_bool cmp v1 v2 = Val.cmpf_bool (swap_comparison cmp) v2 v1.
Proof.
  intros. unfold Val.cmpf_bool. destruct v1; destruct v2; auto. rewrite Float.cmp_swap. reflexivity.
Qed.

Lemma transl_compf_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_comp_float64 cmp r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpf_bool cmp rs#r1 rs#r2 = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. unfold transl_comp_float64. destruct (ftest_for_cmp cmp) eqn:FT.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_float _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_float ft (rs r1) (rs r2))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (Val.cmpf_bool cmp rs#r1 rs#r2) as cmpbool.
          destruct cmp; simpl;
          unfold compare_float;
          unfold Val.cmpf; simpl in FT; inversion FT; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
          destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_float _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_float ft (rs r2) (rs r1))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (Val.cmpf_bool cmp rs#r1 rs#r2) as cmpbool.
          erewrite swap_comparison_cmpf_bool in Heqcmpbool; eauto.
          destruct cmp; simpl;
          unfold compare_float;
          unfold Val.cmpf; simpl in FT; inversion FT; simpl in Heqcmpbool; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
          destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
Qed.

Lemma cmpf_bool_ne_eq:
  forall v1 v2,
  Val.cmpf_bool Cne v1 v2 = option_map negb (Val.cmpf_bool Ceq v1 v2).
Proof.
  intros. unfold Val.cmpf_bool. destruct v1; destruct v2; auto. rewrite Float.cmp_ne_eq. simpl. reflexivity.
Qed.

Lemma cmpf_bool_ne_eq_rev:
  forall v1 v2,
  Val.cmpf_bool Ceq v1 v2 = option_map negb (Val.cmpf_bool Cne v1 v2).
Proof.
  intros. unfold Val.cmpf_bool. destruct v1; destruct v2; auto. rewrite Float.cmp_ne_eq. simpl. rewrite negb_involutive. reflexivity.
Qed.

Lemma option_map_negb_negb:
  forall v,
  option_map negb (option_map negb v) = v.
Proof.
  destruct v; simpl; auto. rewrite negb_involutive. reflexivity.
Qed.

Lemma notbool_option_map_negb:
  forall v, Val.notbool (Val.of_optbool v) = Val.of_optbool (option_map negb v).
Proof.
  unfold Val.notbool. unfold Val.of_optbool.
  destruct v; auto. destruct b; auto.
Qed.

Lemma swap_comparison_cmpf_bool_notftest:
  forall cmp ft v1 v2,
  notftest_for_cmp cmp = Reversed ft ->
  Val.cmpf_bool cmp v1 v2 = Val.cmpf_bool (swap_comparison cmp) v2 v1.
Proof.
  intros. unfold Val.cmpf_bool. destruct v1; destruct v2; auto. rewrite Float.cmp_swap. reflexivity.
Qed.

Lemma transl_compnotf_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_comp_notfloat64 cmp r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\   (option_map negb (Val.cmpf_bool cmp rs#r1 rs#r2) = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. unfold transl_comp_notfloat64. destruct (notftest_for_cmp cmp) eqn:FT.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_float _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_float ft (rs r1) (rs r2))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (option_map negb (Val.cmpf_bool cmp rs#r1 rs#r2)) as cmpbool.
          destruct cmp; simpl;
          unfold compare_float;
          unfold Val.cmpf; simpl in FT; inversion FT.
          * rewrite cmpf_bool_ne_eq; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite cmpf_bool_ne_eq_rev. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_float _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_float ft (rs r2) (rs r1))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (Val.cmpf_bool cmp rs#r1 rs#r2) as cmpbool.
          erewrite swap_comparison_cmpf_bool_notftest in Heqcmpbool; eauto.
          destruct cmp; simpl;
          unfold compare_float;
          unfold Val.cmpf; simpl in FT; inversion FT; simpl in Heqcmpbool.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
Qed.

Lemma swap_comparison_cmpfs_bool:
  forall cmp ft v1 v2,
  ftest_for_cmp cmp = Reversed ft ->
  Val.cmpfs_bool cmp v1 v2 = Val.cmpfs_bool (swap_comparison cmp) v2 v1.
Proof.
  intros. unfold Val.cmpfs_bool. destruct v1; destruct v2; auto. rewrite Float32.cmp_swap. reflexivity.
Qed.

Lemma transl_compfs_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_comp_float32 cmp r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val.cmpfs_bool cmp rs#r1 rs#r2 = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. unfold transl_comp_float32. destruct (ftest_for_cmp cmp) eqn:FT.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_single _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_single ft (rs r1) (rs r2))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (Val.cmpfs_bool cmp rs#r1 rs#r2) as cmpbool.
          destruct cmp; simpl;
          unfold compare_single;
          unfold Val.cmpfs; simpl in FT; inversion FT; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
          destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_single _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_single ft (rs r2) (rs r1))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (Val.cmpfs_bool cmp rs#r1 rs#r2) as cmpbool.
          erewrite swap_comparison_cmpfs_bool in Heqcmpbool; eauto.
          destruct cmp; simpl;
          unfold compare_single;
          unfold Val.cmpfs; simpl in FT; inversion FT; simpl in Heqcmpbool; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
          destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
Qed.

Lemma swap_comparison_cmpfs_bool_notftest:
  forall cmp ft v1 v2,
  notftest_for_cmp cmp = Reversed ft ->
  Val.cmpfs_bool cmp v1 v2 = Val.cmpfs_bool (swap_comparison cmp) v2 v1.
Proof.
  intros. unfold Val.cmpfs_bool. destruct v1; destruct v2; auto. rewrite Float32.cmp_swap. reflexivity.
Qed.

Lemma cmpfs_bool_ne_eq:
  forall v1 v2,
  Val.cmpfs_bool Cne v1 v2 = option_map negb (Val.cmpfs_bool Ceq v1 v2).
Proof.
  intros. unfold Val.cmpfs_bool. destruct v1; destruct v2; auto. rewrite Float32.cmp_ne_eq. simpl. reflexivity.
Qed.

Lemma cmpfs_bool_ne_eq_rev:
  forall v1 v2,
  Val.cmpfs_bool Ceq v1 v2 = option_map negb (Val.cmpfs_bool Cne v1 v2).
Proof.
  intros. unfold Val.cmpfs_bool. destruct v1; destruct v2; auto. rewrite Float32.cmp_ne_eq. simpl. rewrite negb_involutive. reflexivity.
Qed.

Lemma transl_compnotfs_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_comp_notfloat32 cmp r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\   (option_map negb (Val.cmpfs_bool cmp rs#r1 rs#r2) = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. unfold transl_comp_notfloat32. destruct (notftest_for_cmp cmp) eqn:FT.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_single _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_single ft (rs r1) (rs r2))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (option_map negb (Val.cmpfs_bool cmp rs#r1 rs#r2)) as cmpbool.
          destruct cmp; simpl;
          unfold compare_single;
          unfold Val.cmpfs; simpl in FT; inversion FT.
          * rewrite cmpfs_bool_ne_eq; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite cmpfs_bool_ne_eq_rev. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
  * esplit. split.
    - apply exec_straight_one; simpl; eauto.
    - split.
      + intros; Simpl.
      + intros. remember (rs # RTMP <- (compare_single _ _ _)) as rs'.
        simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
        { 
          assert ((nextblock tbb rs') # RTMP = (compare_single ft (rs r2) (rs r1))).
          { rewrite Heqrs'. auto. }
          rewrite H0. rewrite <- H.
          remember (Val.cmpfs_bool cmp rs#r1 rs#r2) as cmpbool.
          erewrite swap_comparison_cmpfs_bool_notftest in Heqcmpbool; eauto.
          destruct cmp; simpl;
          unfold compare_single;
          unfold Val.cmpfs; simpl in FT; inversion FT; simpl in Heqcmpbool.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
          * rewrite notbool_option_map_negb. rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto; destruct b0; simpl; auto.
        }
        rewrite H0. simpl; auto.
Qed.

Lemma transl_complu_correct:
  forall cmp r1 r2 lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_compl cmp Unsigned r1 r2 lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val_cmplu_bool cmp rs#r1 rs#r2 = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compl. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_long (itest_for_cmp cmp Unsigned) rs # r1 rs # r2)) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_long (itest_for_cmp cmp Unsigned) rs # r1 rs # r2)).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val_cmplu_bool cmp rs#r1 rs#r2) as cmpbool.
      destruct cmp; simpl;
      unfold compare_long, Val_cmplu; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_compilu_correct:
  forall cmp r1 n lbl k rs m tbb b,
  exists rs',
     exec_straight ge (transl_compil cmp Unsigned r1 n lbl k) rs m (Pcb BTwnez RTMP lbl ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val_cmplu_bool cmp rs#r1 (Vlong n) = Some b ->
       exec_control ge fn (Some (PCtlFlow (Pcb BTwnez RTMP lbl))) (nextblock tbb rs') m
        = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros. esplit. split.
- unfold transl_compil. apply exec_straight_one; simpl; eauto.
- split.
  + intros; Simpl.
  + intros.
    remember (rs # RTMP <- (compare_long (itest_for_cmp cmp Unsigned) rs # r1 (Vlong n))) as rs'.
    simpl. assert (Val.cmp_bool Cne (nextblock tbb rs') # RTMP (Vint (Int.repr 0)) = Some b).
    { 
      assert ((nextblock tbb rs') # RTMP = (compare_long (itest_for_cmp cmp Unsigned) rs # r1 (Vlong n))).
      { rewrite Heqrs'. auto. }
      rewrite H0. rewrite <- H.
      remember (Val_cmplu_bool cmp rs#r1 (Vlong n)) as cmpbool.
      destruct cmp; simpl;
      unfold compare_long, Val_cmplu; rewrite <- Heqcmpbool; destruct cmpbool; simpl; auto;
      destruct b0; simpl; auto.
    }
    rewrite H0. simpl; auto.
Qed.

Lemma transl_opt_compuimm_correct:
  forall n cmp r1 lbl k rs m b tbb c,
  select_comp n cmp = Some c ->
  exists rs', exists insn,
     exec_straight_opt (transl_opt_compuimm n cmp r1 lbl k) rs m ((PControl insn) ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)  
  /\ ( Val_cmpu_bool cmp rs#r1 (Vint n) = Some b ->
       exec_control ge fn (Some insn) (nextblock tbb rs') m = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros.
(*   unfold transl_opt_compuimm. unfold select_comp in H. rewrite H; simpl. *)
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
    unfold transl_opt_compuimm. subst. rewrite H'.

    exists rs, (Pcbu BTweqz r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      assert (rs r1 = (nextblock tbb rs) r1).
        unfold nextblock, incrPC. Simpl. rewrite H1 in H0.
      (*assert (Val.cmp_bool Ceq (rs r1) (Vint (Int.repr 0)) = Some b) as EVAL'S.
      { rewrite <- H2. rewrite <- H0. rewrite <- H1. auto. }*)
      auto;
      unfold eval_branch. rewrite H0; auto.
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
    unfold transl_opt_compuimm. subst. rewrite H'.

    exists rs, (Pcbu BTwnez r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      assert (rs r1 = (nextblock tbb rs) r1).
        unfold nextblock, incrPC. Simpl. rewrite H1 in H0.
      auto;
      unfold eval_branch. rewrite H0. auto.
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
  forall n cmp r1 lbl k rs m b tbb c,
  select_compl n cmp = Some c ->
  exists rs', exists insn,
     exec_straight_opt (transl_opt_compluimm n cmp r1 lbl k) rs m ((PControl insn) ::g k) rs' m
  /\ (forall r : preg, r <> PC -> r <> RTMP -> rs' r = rs r)
  /\ ( Val_cmplu_bool cmp rs#r1 (Vlong n) = Some b ->
       exec_control ge fn (Some insn) (nextblock tbb rs') m = eval_branch fn lbl (nextblock tbb rs') m (Some b))
  .
Proof.
  intros.
(*   unfold transl_opt_compluimm; rewrite H; simpl. *)
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
    unfold transl_opt_compluimm; subst; rewrite H'.

    exists rs, (Pcbu BTdeqz r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      assert (rs r1 = (nextblock tbb rs) r1).
        unfold nextblock, incrPC. Simpl. rewrite H1 in H0.
      auto;
      unfold eval_branch. rewrite H0; auto.
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
    unfold transl_opt_compluimm; subst; rewrite H'.

    exists rs, (Pcbu BTdnez r1 lbl).
    split.
    * constructor.
    * split; auto. simpl. intros.
      assert (rs r1 = (nextblock tbb rs) r1).
        unfold nextblock, incrPC. Simpl. rewrite H1 in H0.
      auto;
      unfold eval_branch. rewrite H0; auto.
  - (* c = Clt *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
  - (* c = Cle *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
  - (* c = Cgt *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
  - (* c = Cge *) contradict H; unfold select_compl; destruct (Int64.eq n Int64.zero);
    destruct cmp; discriminate.
Qed.

Local Hint Resolve Val_cmpu_bool_correct Val_cmplu_bool_correct: core.

Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs m' tbb,
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' ((PControl insn) ::g k) rs' m'
  /\ exec_control ge fn (Some insn) (nextblock tbb rs') m' = eval_branch fn lbl (nextblock tbb rs') m' (Some b)
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until tbb; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)). 
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_lessdef with (map ms args) m; auto. eapply preg_vals; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
(* Ccomp *)
- exploit (transl_comp_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
(* Ccompu *)
- exploit (transl_compu_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; eauto.
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
      assert (rs x = (nextblock tbb rs) x).
        unfold nextblock, incrPC. Simpl. rewrite H0 in EVAL'. clear H0.
      destruct c0; simpl; auto;
      unfold eval_branch; rewrite <- H; rewrite EVAL'; auto.
  + exploit (transl_compi_correct c0 x n lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez RTMP lbl).
    split.
    * constructor. eexact A'.
    * split; auto.
      { apply C'; auto. }
(* Ccompuimm *)
- remember (select_comp n c0) as selcomp.
  destruct selcomp.
  + exploit (transl_opt_compuimm_correct n c0 x lbl k). apply eq_sym. apply Heqselcomp.
    intros (rs' & i & A & B & C).
    exists rs', i.
    split.
    * apply A.
    * split; auto. apply C. apply EVAL'.
  + assert (transl_opt_compuimm n c0 x lbl k = transl_compi c0 Unsigned x n lbl k).
    { unfold transl_opt_compuimm.
      destruct (Int.eq n Int.zero) eqn:EQN.
      all: unfold select_comp in Heqselcomp; rewrite EQN in Heqselcomp; destruct c0; simpl in *; auto.
      all: discriminate. }
    rewrite H. clear H.
    exploit (transl_compui_correct c0 x n lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez RTMP lbl).
    split.
    * constructor. eexact A'.
    * split; auto.
      { apply C'; auto. }
(* Ccompl *)
- exploit (transl_compl_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
(* Ccomplu *)
- exploit (transl_complu_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; eauto.
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
      assert (rs x = (nextblock tbb rs) x).
        unfold nextblock, incrPC. Simpl. rewrite H0 in EVAL'. clear H0.
      destruct c0; simpl; auto;
      unfold eval_branch; rewrite <- H; rewrite EVAL'; auto.
  + exploit (transl_compil_correct c0 x n lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez RTMP lbl).
    split.
    * constructor. eexact A'.
    * split; auto.
      { apply C'; auto. }

(* Ccompluimm *)
- remember (select_compl n c0) as selcomp.
  destruct selcomp.
  + exploit (transl_opt_compluimm_correct n c0 x lbl k). apply eq_sym. apply Heqselcomp.
    intros (rs' & i & A & B & C).
    exists rs', i.
    split.
    * apply A.
    * split; eauto. (*  apply C. apply EVAL'. *)
  + assert (transl_opt_compluimm n c0 x lbl k = transl_compil c0 Unsigned x n lbl k).
    { unfold transl_opt_compluimm.
      destruct (Int64.eq n Int64.zero) eqn:EQN.
      all: unfold select_compl in Heqselcomp; rewrite EQN in Heqselcomp; destruct c0; simpl in *; auto.
      all: discriminate. }
    rewrite H. clear H.
    exploit (transl_compilu_correct c0 x n lbl); eauto. intros (rs'2 & A' & B' & C').
    exists rs'2, (Pcb BTwnez RTMP lbl).
    split.
    * constructor. eexact A'.
    * split; auto.
      { apply C'; auto. eapply Val_cmplu_bool_correct; eauto. }

(* Ccompf *)
- exploit (transl_compf_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.

(* Cnotcompf *)
- exploit (transl_compnotf_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.

(* Ccompfs *)
- exploit (transl_compfs_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.

(* Cnotcompfs *)
- exploit (transl_compnotfs_correct c0 x x0 lbl); eauto. intros (rs' & A & B & C).
  exists rs', (Pcb BTwnez RTMP lbl).
  split.
  + constructor. eexact A.
  + split; auto. apply C; auto.
Qed.

Lemma transl_cbranch_correct_true:
  forall cond args lbl k c m ms sp rs m' tbb,
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' ((PControl insn) ::g k) rs' m'
  /\ exec_control ge fn (Some insn) (nextblock tbb rs') m' = goto_label fn lbl (nextblock tbb rs') m'
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed. 

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs tbb m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' ((PControl insn) ::g k) rs' m'
  /\ exec_control ge fn (Some insn) (nextblock tbb rs') m' = Next (nextblock tbb rs') m'
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1. all: eauto. simpl eval_branch. instantiate (1 := tbb).
  intros (rs' & insn & A & B & C). rewrite regset_same_assign in B.
  eexists; eexists. split; try split. all: eassumption.
Qed.

(** Translation of condition operators *)

Lemma transl_cond_int32s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_int32s cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 rs#r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.


Lemma transl_cond_int32u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_int32u cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ rs'#rd = Val_cmpu cmp rs#r1 rs#r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_int64s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_int64s cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 rs#r2)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_int64u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_int64u cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ rs'#rd = Val_cmplu cmp rs#r1 rs#r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int32s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code (transl_condimm_int32s cmp rd r1 n k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Local Hint Resolve Val_cmpu_correct Val_cmplu_correct: core.

Lemma transl_condimm_int32u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code (transl_condimm_int32u cmp rd r1 n k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int64s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code (transl_condimm_int64s cmp rd r1 n k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Lemma transl_condimm_int64u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code (transl_condimm_int64u cmp rd r1 n k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl;
  (econstructor; split; 
  [ apply exec_straight_one; [simpl; eauto] | 
    split; intros; Simpl; unfold compare_long; eauto]).
Qed.

Lemma swap_comparison_cmpfs:
  forall v1 v2 cmp,
  Val.lessdef (Val.cmpfs cmp v1 v2) (Val.cmpfs (swap_comparison cmp) v2 v1).
Proof.
  intros. unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct v1; destruct v2; auto.
  rewrite Float32.cmp_swap. auto.
Qed.

Lemma transl_cond_float32_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_float32 cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.cmpfs cmp rs#r1 rs#r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl. apply swap_comparison_cmpfs.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl. apply swap_comparison_cmpfs.
- econstructor; split. apply exec_straight_one; [simpl;
 eauto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_nofloat32_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_notfloat32 cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.of_optbool (option_map negb (Val.cmpfs_bool cmp (rs r1) (rs r2)))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct (rs r1); auto. destruct (rs r2); auto.
  rewrite Float32.cmp_ne_eq. auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct (rs r1); auto. destruct (rs r2); auto.
  rewrite Float32.cmp_ne_eq. simpl. destruct (Float32.cmp Ceq f f0); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  destruct (Float32.cmp Clt f f0); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  cutrewrite (Cge = swap_comparison Cle); auto. rewrite Float32.cmp_swap.
  destruct (Float32.cmp _ _ _); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  cutrewrite (Clt = swap_comparison Cgt); auto. rewrite Float32.cmp_swap.
  destruct (Float32.cmp _ _ _); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpfs. unfold Val.cmpfs_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  destruct (Float32.cmp _ _ _); auto.
Qed.

Lemma swap_comparison_cmpf:
  forall v1 v2 cmp,
  Val.lessdef (Val.cmpf cmp v1 v2) (Val.cmpf (swap_comparison cmp) v2 v1).
Proof.
  intros. unfold Val.cmpf. unfold Val.cmpf_bool. destruct v1; destruct v2; auto.
  rewrite Float.cmp_swap. auto.
Qed.

Lemma transl_cond_float64_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_float64 cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.cmpf cmp rs#r1 rs#r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl. apply swap_comparison_cmpf.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl. apply swap_comparison_cmpf.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
Qed.

Lemma transl_cond_nofloat64_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge (basics_to_code (transl_cond_notfloat64 cmp rd r1 r2 k)) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.of_optbool (option_map negb (Val.cmpf_bool cmp (rs r1) (rs r2)))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. destruct cmp; simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpf. unfold Val.cmpf_bool. destruct (rs r1); auto. destruct (rs r2); auto.
  rewrite Float.cmp_ne_eq. auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpf. unfold Val.cmpf_bool. destruct (rs r1); auto. destruct (rs r2); auto.
  rewrite Float.cmp_ne_eq. simpl. destruct (Float.cmp Ceq f f0); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpf. unfold Val.cmpf_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  destruct (Float.cmp Clt f f0); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpf. unfold Val.cmpf_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  cutrewrite (Cge = swap_comparison Cle); auto. rewrite Float.cmp_swap.
  destruct (Float.cmp _ _ _); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpf. unfold Val.cmpf_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  cutrewrite (Clt = swap_comparison Cgt); auto. rewrite Float.cmp_swap.
  destruct (Float.cmp _ _ _); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto].
  split; intros; Simpl.
  unfold Val.cmpf. unfold Val.cmpf_bool. destruct (rs r1); auto. destruct (rs r2); auto. simpl.
  destruct (Float.cmp _ _ _); auto.
Qed.

Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> RTMP -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
+ (* cmp *)
  exploit transl_cond_int32s_correct; eauto. simpl. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpu *)
  exploit transl_cond_int32u_correct; eauto. simpl. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B; eapply Val_cmpu_correct.
+ (* cmpimm *)
  apply transl_condimm_int32s_correct; eauto with asmgen.
+ (* cmpuimm *)
  apply transl_condimm_int32u_correct; eauto with asmgen.
+ (* cmpl *)
  exploit transl_cond_int64s_correct; eauto. simpl. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmplu *)
  exploit transl_cond_int64u_correct; eauto. simpl. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B, MKTOT; eauto.
  eapply Val_cmplu_correct.
+ (* cmplimm *)
  exploit transl_condimm_int64s_correct; eauto. instantiate (1 := x); eauto with asmgen. simpl. 
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpluimm *)
  exploit transl_condimm_int64u_correct; eauto. instantiate (1 := x); eauto with asmgen. simpl. 
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpfloat *) 
  exploit transl_cond_float64_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpnosingle *)
  exploit transl_cond_nofloat64_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpsingle *) 
  exploit transl_cond_float32_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpnosingle *)
  exploit transl_cond_nofloat32_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
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
  [ apply exec_straight_one; reflexivity
  | split; [ apply Val.lessdef_same; simpl; Simpl; fail | intros; simpl; Simpl; fail ] ].

Lemma int_eq_comm:
  forall (x y: int),
  (Int.eq x y) = (Int.eq y x).
Proof.
  intros.
  unfold Int.eq.
  unfold zeq.
  destruct (Z.eq_dec _ _); destruct (Z.eq_dec _ _); congruence.
Qed.

Lemma int64_eq_comm:
  forall (x y: int64),
  (Int64.eq x y) = (Int64.eq y x).
Proof.
  intros.
  unfold Int64.eq.
  unfold zeq.
  destruct (Z.eq_dec _ _); destruct (Z.eq_dec _ _); congruence.
Qed.

Lemma select_same_lessdef:
  forall ty c v,
    Val.lessdef (Val.select c v v ty) v.
Proof.
  intros.
  unfold Val.select.
  destruct c; try econstructor.
  replace (if b then v else v) with v by (destruct b ; trivial).
  destruct v; destruct ty; simpl; econstructor.
Qed.

Lemma if_neg : forall X,
    forall a,
    forall b c : X,
    (if (negb a) then b else c) = (if a then c else b).
Proof.
  destruct a; reflexivity.
Qed.

Lemma int_ltu_to_neq:
  forall x,
    Int.ltu Int.zero x = negb (Int.eq x Int.zero).
Proof.
  intros.
  unfold Int.ltu, Int.eq.
  change (Int.unsigned Int.zero) with 0.
  pose proof (Int.unsigned_range x) as RANGE.
  unfold zlt, zeq.
  destruct (Z_lt_dec _ _); destruct (Z.eq_dec _ _); trivial; omega.
Qed.

Lemma int64_ltu_to_neq:
  forall x,
    Int64.ltu Int64.zero x = negb (Int64.eq x Int64.zero).
Proof.
  intros.
  unfold Int64.ltu, Int64.eq.
  change (Int64.unsigned Int64.zero) with 0.
  pose proof (Int64.unsigned_range x) as RANGE.
  unfold zlt, zeq.
  destruct (Z_lt_dec _ _); destruct (Z.eq_dec _ _); trivial; omega.
Qed.

Ltac splitall := repeat match goal with |- _ /\ _ => split end.

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
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
+ set (rs1 := (rs#x <- (Genv.symbol_address ge id Ptrofs.zero))).
  exploit (addptrofs_correct x x ofs (basics_to_code k) rs1 m); eauto with asmgen. 
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
  exploit addptrofs_correct. instantiate (1 := SP); auto with asmgen. intros (rs' & A & B & C).
  exists rs'; split; eauto. auto with asmgen.
- (* Ocast8signed *)
  econstructor; split.
  eapply exec_straight_two. simpl;eauto. simpl;eauto.
  repeat split; intros; simpl; Simpl.
  assert (A: Int.ltu (Int.repr 24) Int.iwordsize = true) by auto.
  destruct (rs x0); auto; simpl. rewrite A; simpl. Simpl. unfold Val.shr. rewrite A.
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. split; reflexivity.
- (* Ocast16signed *)
  econstructor; split.
  eapply exec_straight_two. simpl;eauto. simpl;eauto.
  repeat split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 16) Int.iwordsize = true) by auto.
  destruct (rs x0); auto; simpl. rewrite A; simpl. Simpl. unfold Val.shr. rewrite A. 
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. split; reflexivity.
- (* Oshrximm *)
  econstructor; split.
  + apply exec_straight_one. simpl. eauto.
  + repeat split.
    * rewrite Pregmap.gss.
      destruct (rs x0); simpl; trivial.
      unfold Val.maketotal.
      destruct (Int.ltu _ _); simpl; trivial.
    * intros.
      rewrite Pregmap.gso; trivial.
- (* Oshrxlimm *)
  econstructor; split.
  + apply exec_straight_one. simpl. eauto.
  + repeat split.
    * rewrite Pregmap.gss.
      destruct (rs x0); simpl; trivial.
      unfold Val.maketotal.
      destruct (Int.ltu _ _); simpl; trivial.
    * intros.
      rewrite Pregmap.gso; trivial.
      
- (* Ocmp *)
  exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto with asmgen.
  
- (* Osel *)
  unfold conditional_move in *.
  destruct (ireg_eq _ _).
  {
    subst x. inv EQ2.
    econstructor; split.
    {
      apply exec_straight_one.
      simpl. reflexivity.
    }
    split.
    { apply select_same_lessdef. } 
    intros; trivial.
  }

  destruct c0; simpl in *.

    all: destruct c.
    all: simpl in *.
    all: inv EQ2.
    all: econstructor; splitall.
    all: try apply exec_straight_one.
    all: intros; simpl; trivial.
    all: unfold Val.select, cmove, cmoveu; simpl.
    all: destruct (rs x1); simpl; trivial.
    all: try rewrite int_ltu_to_neq.
    all: try rewrite int64_ltu_to_neq.
    all: try change (Int64.eq Int64.zero Int64.zero) with true.
    all: try destruct Archi.ptr64.
    all: try rewrite Pregmap.gss.
    all: repeat rewrite if_neg.
    all: simpl.
    all: try destruct (_ || _).
    all: try apply Val.lessdef_normalize.
    all: trivial. (* no more lessdef *)
    all: apply Pregmap.gso; congruence.

- (* Oselimm *)
  unfold conditional_move_imm32 in *.
  destruct c0; simpl in *.

    all: destruct c.
    all: simpl in *.
    all: inv EQ0.
    all: econstructor; splitall.
    all: try apply exec_straight_one.
    all: intros; simpl; trivial.
    all: unfold Val.select, cmove, cmoveu; simpl.
    all: destruct (rs x0); simpl; trivial.
    all: try rewrite int_ltu_to_neq.
    all: try rewrite int64_ltu_to_neq.
    all: try change (Int64.eq Int64.zero Int64.zero) with true.
    all: try destruct Archi.ptr64.
    all: try rewrite Pregmap.gss.
    all: repeat rewrite if_neg.
    all: simpl.
    all: try destruct (_ || _).
    all: try apply Val.lessdef_normalize.
    all: trivial. (* no more lessdef *)
    all: apply Pregmap.gso; congruence.

- (* Osellimm *)
  unfold conditional_move_imm64 in *.
  destruct c0; simpl in *.

    all: destruct c.
    all: simpl in *.
    all: inv EQ0.
    all: econstructor; splitall.
    all: try apply exec_straight_one.
    all: intros; simpl; trivial.
    all: unfold Val.select, cmove, cmoveu; simpl.
    all: destruct (rs x0); simpl; trivial.
    all: try rewrite int_ltu_to_neq.
    all: try rewrite int64_ltu_to_neq.
    all: try change (Int64.eq Int64.zero Int64.zero) with true.
    all: try destruct Archi.ptr64.
    all: try rewrite Pregmap.gss.
    all: repeat rewrite if_neg.
    all: simpl.
    all: try destruct (_ || _).
    all: try apply Val.lessdef_normalize.
    all: trivial. (* no more lessdef *)
    all: apply Pregmap.gso; congruence.
Qed.

(** Memory accesses *)

Lemma indexed_memory_access_correct:
  forall mk_instr base ofs k rs m,
  exists base' ofs' rs' ptr',
     exec_straight_opt (indexed_memory_access mk_instr base ofs ::g k) rs m
                       (mk_instr base' ofs' ::g k) rs' m
  /\ eval_offset ofs' = OK ptr'
  /\ Val.offset_ptr rs'#base' ptr' = Val.offset_ptr rs#base ofs
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  unfold indexed_memory_access; intros.
  (* destruct Archi.ptr64 eqn:SF. *)
  assert (Archi.ptr64 = true) as SF; auto.
- generalize (make_immed64_sound (Ptrofs.to_int64 ofs)); intros EQ.
  destruct (make_immed64 (Ptrofs.to_int64 ofs)).
+ econstructor; econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl. 
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
Qed.


Lemma indexed_load_access_correct:
  forall trap chunk (mk_instr: ireg -> offset -> basic) rd m,
  (forall base ofs rs,
     exec_basic_instr ge (mk_instr base ofs) rs m = exec_load_offset trap chunk rs m rd base ofs) ->
  forall (base: ireg) ofs k (rs: regset) v,
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge (indexed_memory_access mk_instr base ofs ::g k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until v; intros LOAD.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & ptr' & A & PtrEq & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_load_offset. unfold parexec_load_offset. rewrite PtrEq. rewrite B, LOAD. eauto. Simpl. 
  split; intros; Simpl. auto.
Qed.

Lemma indexed_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> basic) r1 m,
  (forall base ofs rs,
     exec_basic_instr ge (mk_instr base ofs) rs m = exec_store_offset chunk rs m r1 base ofs) ->
  forall (base: ireg) ofs k (rs: regset) m',
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs#r1) = Some m' ->
  exists rs',
     exec_straight ge (indexed_memory_access mk_instr base ofs ::g k) rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until m'; intros STORE.
  exploit indexed_memory_access_correct. (* instantiate (1 := base). eauto. *)
  intros (base' & ofs' & rs' & ptr' & A & PtrEq & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eapply A. apply exec_straight_one. rewrite EXEC.
  unfold exec_store_offset. unfold parexec_store_offset. rewrite PtrEq. rewrite B, C, STORE.
    eauto.
    discriminate.
  auto.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR LOAD. 
  assert (A: exists mk_instr rd,
                preg_of dst = IR rd
             /\ c = indexed_memory_access mk_instr base ofs :: k
             /\ forall base' ofs' rs',
                   exec_basic_instr ge (mk_instr base' ofs') rs' m =
                   exec_load_offset TRAP (chunk_of_type ty) rs' m rd base' ofs').
  { unfold loadind in TR.
    destruct ty, (preg_of dst); inv TR; econstructor; esplit; eauto. }
  destruct A as (mk_instr & rd & rdEq & B & C). subst c. rewrite rdEq.
  eapply indexed_load_access_correct; eauto with asmgen. 
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR STORE.
  assert (A: exists mk_instr rr,
                preg_of src = IR rr
             /\ c = indexed_memory_access mk_instr base ofs :: k
             /\ forall base' ofs' rs',
                   exec_basic_instr ge (mk_instr base' ofs') rs' m =
                   exec_store_offset (chunk_of_type ty) rs' m rr base' ofs').
  { unfold storeind in TR. destruct ty, (preg_of src); inv TR; econstructor; esplit; eauto. }
  destruct A as (mk_instr & rr & rsEq & B & C). subst c.
  eapply indexed_store_access_correct; eauto with asmgen.
  congruence.
Qed.

Ltac bsimpl := unfold exec_bblock; simpl.

Lemma Pget_correct:
  forall (dst: gpreg) (src: preg) k (rs: regset) m,
  src = RA ->
  exists rs',
     exec_straight ge (Pget dst src ::g k) rs m k rs' m
  /\ rs'#dst = rs#src
  /\ forall r, r <> PC -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. econstructor; econstructor; econstructor.
- rewrite H. bsimpl. auto.
- Simpl.
- intros. Simpl.
Qed.

Lemma Pset_correct:
  forall (dst: preg) (src: gpreg) k (rs: regset) m,
  dst = RA ->
  exists rs',
     exec_straight ge (Pset dst src ::g k) rs m k rs' m
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
  exists rs',
     exec_straight ge (loadind_ptr base ofs dst ::g k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_load_access_correct; eauto with asmgen.
  intros. unfold Mptr. assert (Archi.ptr64 = true). auto. rewrite H0.
  instantiate (1 := TRAP).
  auto.
Qed.

Lemma storeind_ptr_correct:
  forall (base: ireg) ofs (src: ireg) k (rs: regset) m m',
  Mem.storev Mptr m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  exists rs',
     exec_straight ge (storeind_ptr src base ofs ::g k) rs m k rs' m'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_store_access_correct with (r1 := src); eauto with asmgen.
  intros. unfold Mptr. assert (Archi.ptr64 = true); auto.
Qed.

Lemma transl_memory_access_correct:
  forall mk_instr addr args k c (rs: regset) m v,
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  exists base ofs rs' ptr,
     exec_straight_opt (basics_to_code c) rs m (mk_instr base ofs ::g (basics_to_code k)) rs' m
  /\ eval_offset ofs = OK ptr
  /\ Val.offset_ptr rs'#base ptr = v
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV. 
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
- (* indexed *)
  inv EV. exploit indexed_memory_access_correct; eauto. intros (base' & ofs' & rs' & ptr' & EOPT & EVALOFF & VALOFF & RSEQ).
  eexists; eexists; eexists; eexists. split; try split; try split.
  eapply EOPT. unfold eval_offset in EVALOFF. inv EVALOFF. eauto.
  { intros. destruct r; rewrite RSEQ; auto. }
- (* global *)
  simpl in EV. inv EV. inv TR.  econstructor; econstructor; econstructor; econstructor; split.
  constructor. apply exec_straight_one. simpl; eauto. auto. 
  split; split; intros; Simpl.
  assert (Val.lessdef (Val.offset_ptr (Genv.symbol_address ge i i0) Ptrofs.zero) (Genv.symbol_address ge i i0)).
  { apply Val.offset_ptr_zero. }
  remember (Genv.symbol_address ge i i0) as symbol.
  destruct symbol; auto.
  + contradict Heqsymbol; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge i); discriminate.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + contradict Heqsymbol; unfold Genv.symbol_address;
    destruct (Genv.find_symbol ge i); discriminate.
  + simpl. rewrite Ptrofs.add_zero; auto.
- (* stack *)
  inv TR. inv EV. 
  exploit indexed_memory_access_correct; eauto. intros (base' & ofs' & rs' & ptr' & EOPT & EVALOFF & VALOFF & RSEQ).
  eexists; eexists; eexists; eexists. split; try split; try split.
  eapply EOPT. unfold eval_offset in EVALOFF. inv EVALOFF. eauto.
  { intros. destruct r; rewrite RSEQ; auto. }
Qed.

Lemma transl_memory_access2_correct:
  forall mk_instr addr args k c (rs: regset) m v,
  transl_memory_access2 mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  exists base ro mro mr1 rs',
     args = mr1 :: mro :: nil
  /\ ireg_of mro = OK ro
  /\ exec_straight_opt (basics_to_code c) rs m (mk_instr base ro ::g (basics_to_code k)) rs' m
  /\ Val.addl rs'#base rs'#ro = v
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV. 
  unfold transl_memory_access2 in TR; destruct addr; ArgsInv.
  inv EV. repeat eexists. eassumption. econstructor; eauto.
Qed.

Lemma transl_memory_access2XS_correct:
  forall chunk mk_instr (scale : Z) args k c (rs: regset) m v,
  transl_memory_access2XS chunk mk_instr scale args k = OK c ->
  eval_addressing ge rs#SP (Aindexed2XS scale) (map rs (map preg_of args)) = Some v ->
  exists base ro mro mr1 rs',
     args = mr1 :: mro :: nil
  /\ ireg_of mro = OK ro
  /\ exec_straight_opt (basics_to_code c) rs m (mk_instr base ro ::g (basics_to_code k)) rs' m
  /\ Val.addl rs'#base (Val.shll rs'#ro (Vint (Int.repr scale))) = v
  /\ (forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r)
  /\ scale = (zscale_of_chunk chunk).
Proof.
  intros until v; intros TR EV. 
  unfold transl_memory_access2XS in TR; ArgsInv.
  inv EV. repeat eexists. eassumption. econstructor; eauto.
  symmetry.
  apply Z.eqb_eq.
  assumption.
Qed.

Lemma transl_load_access2_correct:
  forall trap chunk (mk_instr: ireg -> ireg -> basic) addr args k c rd (rs: regset) m v mro mr1 ro v',
  args = mr1 :: mro :: nil ->
  ireg_of mro = OK ro ->
  (forall base rs,
     exec_basic_instr ge (mk_instr base ro) rs m = exec_load_reg trap chunk rs m rd base ro) ->
  transl_memory_access2 mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> RTMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros ARGS IREGE INSTR TR EV LOAD. 
  exploit transl_memory_access2_correct; eauto.
  intros (base & ro2 & mro2 & mr2 & rs' & ARGSS & IREGEQ & A & B & C). rewrite ARGSS in ARGS. inversion ARGS. subst mr2 mro2. clear ARGS.
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. assert (ro = ro2) by congruence. subst ro2.
  rewrite INSTR. unfold exec_load_reg. unfold parexec_load_reg. rewrite B, LOAD. reflexivity. Simpl. 
  split; intros; Simpl. auto.
Qed.

Lemma transl_load_access2_correct_notrap2:
  forall chunk (mk_instr: ireg -> ireg -> basic) addr args k c rd (rs: regset) m v mro mr1 ro,
  args = mr1 :: mro :: nil ->
  ireg_of mro = OK ro ->
  (forall base rs,
     exec_basic_instr ge (mk_instr base ro) rs m = exec_load_reg NOTRAP chunk rs m rd base ro) ->
  transl_memory_access2 mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = None ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#rd = concrete_default_notrap_load_value chunk
  /\ forall r, r <> PC -> r <> RTMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until ro; intros ARGS IREGE INSTR TR EV LOAD. 
  exploit transl_memory_access2_correct; eauto.
  intros (base & ro2 & mro2 & mr2 & rs' & ARGSS & IREGEQ & A & B & C). rewrite ARGSS in ARGS. inversion ARGS. subst mr2 mro2. clear ARGS.
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. assert (ro = ro2) by congruence. subst ro2.
  rewrite INSTR. unfold exec_load_reg. unfold parexec_load_reg. rewrite B, LOAD. reflexivity. Simpl. 
  split; intros; Simpl. auto.
Qed.

Lemma transl_load_access2XS_correct:
  forall trap chunk (mk_instr: ireg -> ireg -> basic) (scale : Z) args k c rd (rs: regset) m v mro mr1 ro v',
  args = mr1 :: mro :: nil ->
  ireg_of mro = OK ro ->
  (forall base rs,
     exec_basic_instr ge (mk_instr base ro) rs m = exec_load_regxs trap chunk rs m rd base ro) ->
  transl_memory_access2XS chunk mk_instr scale args k = OK c ->
  eval_addressing ge rs#SP (Aindexed2XS scale) (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> RTMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros ARGS IREGE INSTR TR EV LOAD. 
  exploit transl_memory_access2XS_correct; eauto.
  intros (base & ro2 & mro2 & mr2 & rs' & ARGSS & IREGEQ & A & B & C & D). rewrite ARGSS in ARGS. inversion ARGS. subst mr2 mro2. clear ARGS.
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. assert (ro = ro2) by congruence. subst ro2.
  rewrite INSTR. unfold exec_load_regxs. unfold parexec_load_regxs.
  unfold scale_of_chunk.
  subst scale.
  rewrite B, LOAD. reflexivity. Simpl. 
  split. trivial. intros. Simpl.
Qed.

Lemma transl_load_access2XS_correct_notrap2:
  forall chunk (mk_instr: ireg -> ireg -> basic) (scale : Z) args k c rd (rs: regset) m v mro mr1 ro,
  args = mr1 :: mro :: nil ->
  ireg_of mro = OK ro ->
  (forall base rs,
     exec_basic_instr ge (mk_instr base ro) rs m = exec_load_regxs NOTRAP chunk rs m rd base ro) ->
  transl_memory_access2XS chunk mk_instr scale args k = OK c ->
  eval_addressing ge rs#SP (Aindexed2XS scale) (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = None ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#rd = concrete_default_notrap_load_value chunk
  /\ forall r, r <> PC -> r <> RTMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until ro; intros ARGS IREGE INSTR TR EV LOAD. 
  exploit transl_memory_access2XS_correct; eauto.
  intros (base & ro2 & mro2 & mr2 & rs' & ARGSS & IREGEQ & A & B & C & D). rewrite ARGSS in ARGS. inversion ARGS. subst mr2 mro2. clear ARGS.
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. assert (ro = ro2) by congruence. subst ro2.
  rewrite INSTR. unfold exec_load_regxs. unfold parexec_load_regxs.
  unfold scale_of_chunk.
  subst scale.
  rewrite B, LOAD. reflexivity. Simpl. 
  split. trivial. intros. Simpl.
Qed.

Lemma transl_load_access_correct:
  forall trap chunk (mk_instr: ireg -> offset -> basic) addr args k c rd (rs: regset) m v v',
  (forall base ofs rs,
     exec_basic_instr ge (mk_instr base ofs) rs m = exec_load_offset trap chunk rs m rd base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> RTMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros INSTR TR EV LOAD. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & ptr & A & PtrEq & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_load_offset. unfold parexec_load_offset. rewrite PtrEq, B, LOAD. reflexivity. Simpl. 
  split; intros; Simpl. auto.
Qed.

Lemma transl_load_access_correct_notrap2:
  forall chunk (mk_instr: ireg -> offset -> basic) addr args k c rd (rs: regset) m v,
  (forall base ofs rs,
     exec_basic_instr ge (mk_instr base ofs) rs m = exec_load_offset NOTRAP chunk rs m rd base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = None ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#rd = concrete_default_notrap_load_value chunk
  /\ forall r, r <> PC -> r <> RTMP -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v; intros INSTR TR EV LOAD. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & ptr & A & PtrEq & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_load_offset. unfold parexec_load_offset. rewrite PtrEq, B, LOAD. reflexivity. Simpl. 
  split. trivial. intros. Simpl.
Qed.

Lemma transl_load_memory_access_ok:
  forall addr trap chunk args dst k c rs a v m,
  (match addr with Aindexed2XS _ | Aindexed2 => False | _ => True end) ->
  transl_load trap chunk addr args dst k = OK c ->
  eval_addressing ge (rs (IR SP)) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists mk_instr rd,
     preg_of dst = IR rd
  /\ transl_memory_access mk_instr addr args k = OK c
  /\ forall base ofs rs,
        exec_basic_instr ge (mk_instr base ofs) rs m = exec_load_offset trap chunk rs m rd base ofs.
Proof.
  intros until m. intros ADDR TR ? ?.
  unfold transl_load in TR. destruct addr; try contradiction.
  - monadInv TR. destruct chunk; ArgsInv; econstructor; (esplit; eauto).
  - monadInv TR. destruct chunk. all: ArgsInv; destruct args; try discriminate; monadInv EQ0; eexists; eexists; split; try split;
    [ instantiate (1 := (PLoadRRO _ _ x)); simpl; reflexivity
    | eauto ].
  - monadInv TR. destruct chunk. all: ArgsInv; destruct args; try discriminate; monadInv EQ0; eexists; eexists; split; try split;
    [ instantiate (1 := (PLoadRRO _ _ x)); simpl; reflexivity
    | eauto ].
Qed.

Lemma transl_load_memory_access_ok_notrap2:
  forall addr chunk args dst k c rs a m,
  (match addr with Aindexed2XS _ | Aindexed2 => False | _ => True end) ->
  transl_load NOTRAP chunk addr args dst k = OK c ->
  eval_addressing ge (rs (IR SP)) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = None ->
  exists mk_instr rd,
     preg_of dst = IR rd
  /\ transl_memory_access mk_instr addr args k = OK c
  /\ forall base ofs rs,
        exec_basic_instr ge (mk_instr base ofs) rs m = exec_load_offset NOTRAP chunk rs m rd base ofs.
Proof.
  intros until m. intros ADDR TR ? ?.
  unfold transl_load in TR. destruct addr; try contradiction.
  - monadInv TR. destruct chunk; ArgsInv; econstructor; (esplit; eauto).
  - monadInv TR. destruct chunk. all: ArgsInv; destruct args; try discriminate; monadInv EQ0; eexists; eexists; split; try split;
    [ instantiate (1 := (PLoadRRO _ _ x)); simpl; reflexivity
    | eauto ].
  - monadInv TR. destruct chunk. all: ArgsInv; destruct args; try discriminate; monadInv EQ0; eexists; eexists; split; try split;
    [ instantiate (1 := (PLoadRRO _ _ x)); simpl; reflexivity
    | eauto ].
Qed.

Lemma transl_load_memory_access2_ok:
  forall trap chunk args dst k c rs a v m,
  transl_load trap chunk Aindexed2 args dst k = OK c ->
  eval_addressing ge (rs (IR SP)) Aindexed2 (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists mk_instr mr0 mro rd ro,
      args = mr0 :: mro :: nil
   /\ preg_of dst = IR rd
   /\ preg_of mro = IR ro
   /\ transl_memory_access2 mk_instr Aindexed2 args k = OK c
   /\ forall base rs,
      exec_basic_instr ge (mk_instr base ro) rs m = exec_load_reg trap chunk rs m rd base ro.
Proof.
  intros until m. intros TR ? ?.
  unfold transl_load in TR. subst. monadInv TR. destruct chunk. all:
  unfold transl_memory_access2 in EQ0; repeat (destruct args; try discriminate); monadInv EQ0; ArgsInv; repeat eexists;
  [ unfold ireg_of in EQ0; destruct (preg_of m1); eauto; try discriminate; monadInv EQ0; reflexivity
  | rewrite EQ1; rewrite EQ0; simpl; instantiate (1 := (PLoadRRR _ _ x)); simpl; reflexivity
  | eauto].
Qed.


Lemma transl_load_memory_access2_ok_notrap2:
  forall chunk args dst k c rs a m,
  transl_load NOTRAP chunk Aindexed2 args dst k = OK c ->
  eval_addressing ge (rs (IR SP)) Aindexed2 (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = None ->
  exists mk_instr mr0 mro rd ro,
      args = mr0 :: mro :: nil
   /\ preg_of dst = IR rd
   /\ preg_of mro = IR ro
   /\ transl_memory_access2 mk_instr Aindexed2 args k = OK c
   /\ forall base rs,
      exec_basic_instr ge (mk_instr base ro) rs m = exec_load_reg NOTRAP chunk rs m rd base ro.
Proof.
  intros until m. intros TR ? ?.
  unfold transl_load in TR. subst. monadInv TR. destruct chunk. all:
  unfold transl_memory_access2 in EQ0; repeat (destruct args; try discriminate); monadInv EQ0; ArgsInv; repeat eexists;
  [ unfold ireg_of in EQ0; destruct (preg_of m1); eauto; try discriminate; monadInv EQ0; reflexivity
  | rewrite EQ1; rewrite EQ0; simpl; instantiate (1 := (PLoadRRR _ _ x)); simpl; reflexivity
  | eauto].
Qed.

Lemma transl_load_memory_access2XS_ok:
  forall scale trap chunk args dst k c rs a v m,
  transl_load trap chunk (Aindexed2XS scale) args dst k = OK c ->
  eval_addressing ge (rs (IR SP)) (Aindexed2XS scale) (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists mk_instr mr0 mro rd ro,
      args = mr0 :: mro :: nil
   /\ preg_of dst = IR rd
   /\ preg_of mro = IR ro
   /\ transl_memory_access2XS chunk mk_instr scale args k = OK c
   /\ forall base rs,
      exec_basic_instr ge (mk_instr base ro) rs m = exec_load_regxs trap chunk rs m rd base ro.
Proof.
  intros until m. intros TR ? ?.
  unfold transl_load in TR. subst. monadInv TR. destruct chunk. all:
  unfold transl_memory_access2XS in EQ0; repeat (destruct args; try discriminate); monadInv EQ0; ArgsInv; repeat eexists;
  [ unfold ireg_of in EQ0; destruct (preg_of m1); eauto; try discriminate; monadInv EQ0; reflexivity
  | rewrite EQ1; rewrite EQ0; simpl; instantiate (1 := (PLoadRRRXS _ _ x)); simpl; rewrite Heqb; eauto
  | eauto].
Qed.


Lemma transl_load_memory_access2XS_ok_notrap2:
  forall scale chunk args dst k c rs a m,
  transl_load NOTRAP chunk (Aindexed2XS scale) args dst k = OK c ->
  eval_addressing ge (rs (IR SP)) (Aindexed2XS scale) (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = None ->
  exists mk_instr mr0 mro rd ro,
      args = mr0 :: mro :: nil
   /\ preg_of dst = IR rd
   /\ preg_of mro = IR ro
   /\ transl_memory_access2XS chunk mk_instr scale args k = OK c
   /\ forall base rs,
      exec_basic_instr ge (mk_instr base ro) rs m = exec_load_regxs NOTRAP chunk rs m rd base ro.
Proof.
  intros until m. intros TR ? ?.
  unfold transl_load in TR. subst. monadInv TR. destruct chunk. all:
  unfold transl_memory_access2XS in EQ0; repeat (destruct args; try discriminate); monadInv EQ0; ArgsInv; repeat eexists;
  [ unfold ireg_of in EQ0; destruct (preg_of m1); eauto; try discriminate; monadInv EQ0; reflexivity
  | rewrite EQ1; rewrite EQ0; simpl; instantiate (1 := (PLoadRRRXS _ _ x)); simpl; rewrite Heqb; eauto
  | eauto].
Qed.

Lemma transl_load_correct:
  forall trap chunk addr args dst k c (rs: regset) m a v,
  transl_load trap chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> RTMP -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD. destruct addr.
  - exploit transl_load_memory_access2XS_ok; eauto. intros (mk_instr & mr0 & mro & rd & ro & argsEq & rdEq & roEq & B & C).
    rewrite rdEq. eapply transl_load_access2XS_correct; eauto with asmgen. unfold ireg_of. rewrite roEq. reflexivity.
  - exploit transl_load_memory_access2_ok; eauto. intros (mk_instr & mr0 & mro & rd & ro & argsEq & rdEq & roEq & B & C).
    rewrite rdEq. eapply transl_load_access2_correct; eauto with asmgen. unfold ireg_of. rewrite roEq. reflexivity.
  - exploit transl_load_memory_access_ok; eauto; try discriminate; try (simpl; reflexivity).
    intros A; destruct A as (mk_instr & rd & rdEq & B & C); rewrite rdEq;
      eapply transl_load_access_correct; eauto with asmgen.
  - exploit transl_load_memory_access_ok; eauto; try discriminate; try (simpl; reflexivity).
    intros A; destruct A as (mk_instr & rd & rdEq & B & C); rewrite rdEq;
      eapply transl_load_access_correct; eauto with asmgen.
  - exploit transl_load_memory_access_ok; eauto; try discriminate; try (simpl; reflexivity).
    intros A; destruct A as (mk_instr & rd & rdEq & B & C); rewrite rdEq;
      eapply transl_load_access_correct; eauto with asmgen.
Qed.

Lemma transl_load_correct_notrap2:
  forall chunk addr args dst k c (rs: regset) m a,
  transl_load NOTRAP chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = None ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m
  /\ rs'#(preg_of dst) = (concrete_default_notrap_load_value chunk)
  /\ forall r, r <> PC -> r <> RTMP -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until a; intros TR EV LOAD. destruct addr.
  - exploit transl_load_memory_access2XS_ok_notrap2; eauto. intros (mk_instr & mr0 & mro & rd & ro & argsEq & rdEq & roEq & B & C).
    rewrite rdEq. eapply transl_load_access2XS_correct_notrap2; eauto with asmgen. unfold ireg_of. rewrite roEq. reflexivity.
  - exploit transl_load_memory_access2_ok_notrap2; eauto. intros (mk_instr & mr0 & mro & rd & ro & argsEq & rdEq & roEq & B & C).
    rewrite rdEq. eapply transl_load_access2_correct_notrap2; eauto with asmgen. unfold ireg_of. rewrite roEq. reflexivity.
  - exploit transl_load_memory_access_ok_notrap2; eauto; try discriminate; try (simpl; reflexivity).
    intros A; destruct A as (mk_instr & rd & rdEq & B & C); rewrite rdEq;
      eapply transl_load_access_correct_notrap2; eauto with asmgen.
  - exploit transl_load_memory_access_ok_notrap2; eauto; try discriminate; try (simpl; reflexivity).
    intros A; destruct A as (mk_instr & rd & rdEq & B & C); rewrite rdEq;
      eapply transl_load_access_correct_notrap2; eauto with asmgen.
  - exploit transl_load_memory_access_ok_notrap2; eauto; try discriminate; try (simpl; reflexivity).
    intros A; destruct A as (mk_instr & rd & rdEq & B & C); rewrite rdEq;
      eapply transl_load_access_correct_notrap2; eauto with asmgen.
Qed.

Lemma transl_store_access2_correct:
  forall chunk (mk_instr: ireg -> ireg -> basic) addr args k c r1 (rs: regset) m v mr1 mro ro m',
  args = mr1 :: mro :: nil ->
  ireg_of mro = OK ro ->
  (forall base rs,
     exec_basic_instr ge (mk_instr base ro) rs m = exec_store_reg chunk rs m r1 base ro) ->
  transl_memory_access2 mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m'
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until m'; intros ARGS IREG INSTR TR EV STORE NOT31. 
  exploit transl_memory_access2_correct; eauto.
  intros (base & ro2 & mr2 & mro2 & rs' & ARGSS & IREGG & A & B & C). rewrite ARGSS in ARGS. inversion ARGS. subst mro2 mr2. clear ARGS.
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. assert (ro = ro2) by congruence. subst ro2.
  rewrite INSTR. unfold exec_store_reg. unfold parexec_store_reg. rewrite B. rewrite C; try discriminate. rewrite STORE. auto.
  intro. inv H. contradiction.
  auto.
Qed.

Lemma transl_store_access2XS_correct:
  forall chunk (mk_instr: ireg -> ireg -> basic) scale args k c r1 (rs: regset) m v mr1 mro ro m',
  args = mr1 :: mro :: nil ->
  ireg_of mro = OK ro ->
  (forall base rs,
     exec_basic_instr ge (mk_instr base ro) rs m = exec_store_regxs chunk rs m r1 base ro) ->
  transl_memory_access2XS chunk mk_instr scale args k = OK c ->
  eval_addressing ge rs#SP (Aindexed2XS scale) (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m'
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until m'; intros ARGS IREG INSTR TR EV STORE NOT31. 
  exploit transl_memory_access2XS_correct; eauto.
  intros (base & ro2 & mr2 & mro2 & rs' & ARGSS & IREGG & A & B & C & D). rewrite ARGSS in ARGS. inversion ARGS. subst mro2 mr2. clear ARGS.
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. assert (ro = ro2) by congruence. subst ro2.
  rewrite INSTR. unfold exec_store_regxs. unfold parexec_store_regxs.
  unfold scale_of_chunk.
  subst scale.
  rewrite B. rewrite C; try discriminate. rewrite STORE. auto.
  intro. inv H. contradiction.
  auto.
Qed.

Lemma transl_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> basic) addr args k c r1 (rs: regset) m v m',
  (forall base ofs rs,
     exec_basic_instr ge (mk_instr base ofs) rs m = exec_store_offset chunk rs m r1 base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> RTMP ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m'
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until m'; intros INSTR TR EV STORE NOT31. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & ptr & A & PtrEq & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_store_offset. unfold parexec_store_offset. rewrite PtrEq, B. rewrite C; try discriminate. rewrite STORE. auto.
  intro. inv H. contradiction.
  auto.
Qed.


Remark exec_store_offset_8_sign rs m x base ofs:
  exec_store_offset Mint8unsigned rs m x base ofs = exec_store_offset Mint8signed rs m x base ofs.
Proof.
  unfold exec_store_offset. unfold parexec_store_offset. unfold eval_offset; auto. unfold Mem.storev.
  destruct (Val.offset_ptr _ _); auto. erewrite <- Mem.store_signed_unsigned_8. reflexivity.
Qed.

Remark exec_store_offset_16_sign rs m x base ofs:
  exec_store_offset Mint16unsigned rs m x base ofs = exec_store_offset Mint16signed rs m x base ofs.
Proof.
  unfold exec_store_offset. unfold parexec_store_offset. unfold eval_offset; auto. unfold Mem.storev.
  destruct (Val.offset_ptr _ _); auto. erewrite <- Mem.store_signed_unsigned_16. reflexivity.
Qed.

Lemma transl_store_memory_access_ok:
  forall addr chunk args src k c rs a m m',
  (match addr with Aindexed2XS _ | Aindexed2 => False | _ => True end) ->
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs (IR SP)) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists mk_instr chunk' rr,
     preg_of src = IR rr
  /\ transl_memory_access mk_instr addr args k = OK c
  /\ (forall base ofs rs,
       exec_basic_instr ge (mk_instr base ofs) rs m = exec_store_offset chunk' rs m rr base ofs)
  /\ Mem.storev chunk m a rs#(preg_of src) = Mem.storev chunk' m a rs#(preg_of src).
Proof.
  intros until m'. intros ? TR ? ?.
  unfold transl_store in TR. destruct addr; try contradiction.
  - monadInv TR. destruct chunk. all:
    ArgsInv; eexists; eexists; eexists; split; try split; [
      repeat (destruct args; try discriminate); eassumption
    | split; eauto; intros; simpl; try reflexivity].
    eapply exec_store_offset_8_sign.
    eapply exec_store_offset_16_sign.
  - monadInv TR. destruct chunk. all:
    ArgsInv; eexists; eexists; eexists; split; try split;
    [ repeat (destruct args; try discriminate); instantiate (1 := PStoreRRO _ x); simpl; eassumption
    | split; eauto; intros; simpl; try reflexivity].
    eapply exec_store_offset_8_sign.
    eapply exec_store_offset_16_sign.
  - monadInv TR. destruct chunk. all:
    ArgsInv; eexists; eexists; eexists; split; try split;
    [ repeat (destruct args; try discriminate); instantiate (1 := PStoreRRO _ x); simpl; eassumption
    | split; eauto; intros; simpl; try reflexivity].
    eapply exec_store_offset_8_sign.
    eapply exec_store_offset_16_sign.
Qed.

Remark exec_store_reg_8_sign rs m x base ofs:
  exec_store_reg Mint8unsigned rs m x base ofs = exec_store_reg Mint8signed rs m x base ofs.
Proof.
  unfold exec_store_reg. unfold parexec_store_reg. unfold Mem.storev. destruct (Val.addl _ _); auto.
  erewrite <- Mem.store_signed_unsigned_8. reflexivity.
Qed.

Remark exec_store_reg_16_sign rs m x base ofs:
  exec_store_reg Mint16unsigned rs m x base ofs = exec_store_reg Mint16signed rs m x base ofs.
Proof.
  unfold exec_store_reg. unfold parexec_store_reg. unfold Mem.storev. destruct (Val.addl _ _); auto.
  erewrite <- Mem.store_signed_unsigned_16. reflexivity.
Qed.

Remark exec_store_regxs_8_sign rs m x base ofs:
  exec_store_regxs Mint8unsigned rs m x base ofs = exec_store_regxs Mint8signed rs m x base ofs.
Proof.
  unfold exec_store_regxs. unfold parexec_store_regxs. unfold Mem.storev. destruct (Val.addl _ _); auto.
  erewrite <- Mem.store_signed_unsigned_8. reflexivity.
Qed.

Remark exec_store_regxs_16_sign rs m x base ofs:
  exec_store_regxs Mint16unsigned rs m x base ofs = exec_store_regxs Mint16signed rs m x base ofs.
Proof.
  unfold exec_store_regxs. unfold parexec_store_regxs. unfold Mem.storev. destruct (Val.addl _ _); auto.
  erewrite <- Mem.store_signed_unsigned_16. reflexivity.
Qed.

Lemma transl_store_memory_access2_ok:
  forall addr chunk args src k c rs a m m',
  addr = Aindexed2 ->
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs (IR SP)) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists mk_instr chunk' rr mr0 mro ro,
     args = mr0 :: mro :: nil
  /\ preg_of mro = IR ro
  /\ preg_of src = IR rr
  /\ transl_memory_access2 mk_instr addr args k = OK c
  /\ (forall base rs,
       exec_basic_instr ge (mk_instr base ro) rs m = exec_store_reg chunk' rs m rr base ro)
  /\ Mem.storev chunk m a rs#(preg_of src) = Mem.storev chunk' m a rs#(preg_of src).
Proof.
  intros until m'. intros ? TR ? ?.
  unfold transl_store in TR. subst addr. monadInv TR. destruct chunk. all:
  unfold transl_memory_access2 in EQ0; repeat (destruct args; try discriminate); monadInv EQ0; ArgsInv; repeat eexists;
  [ ArgsInv; reflexivity
  | rewrite EQ1; rewrite EQ0; instantiate (1 := (PStoreRRR _ x)); simpl; reflexivity
  | eauto ].
  - simpl. intros. eapply exec_store_reg_8_sign.
  - simpl. intros. eapply exec_store_reg_16_sign.
Qed.

Lemma transl_store_memory_access2XS_ok:
  forall scale chunk args src k c rs a m m',
  transl_store chunk (Aindexed2XS scale) args src k = OK c ->
  eval_addressing ge (rs (IR SP)) (Aindexed2XS scale) (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists mk_instr chunk' rr mr0 mro ro,
     args = mr0 :: mro :: nil
  /\ preg_of mro = IR ro
  /\ preg_of src = IR rr
  /\ transl_memory_access2XS chunk' mk_instr scale args k = OK c
  /\ (forall base rs,
       exec_basic_instr ge (mk_instr base ro) rs m = exec_store_regxs chunk' rs m rr base ro)
  /\ Mem.storev chunk m a rs#(preg_of src) = Mem.storev chunk' m a rs#(preg_of src).
Proof.
  intros until m'. intros TR ? ?.
  unfold transl_store in TR. monadInv TR. destruct chunk. all:
  unfold transl_memory_access2XS in EQ0; repeat (destruct args; try discriminate); monadInv EQ0; ArgsInv; repeat eexists;
  [ ArgsInv; reflexivity
  | rewrite EQ1; rewrite EQ0; instantiate (1 := (PStoreRRRXS _ x)); simpl; rewrite Heqb; eauto
  | eauto ].
  - simpl. intros. eapply exec_store_regxs_8_sign.
  - simpl. intros. eapply exec_store_regxs_16_sign.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge (basics_to_code c) rs m (basics_to_code k) rs' m'
  /\ forall r, r <> PC -> r <> RTMP -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR EV STORE. destruct addr.
  - exploit transl_store_memory_access2XS_ok; eauto. intros (mk_instr & chunk' & rr & mr0 & mro & ro & argsEq & roEq & srcEq & A & B & C).
    eapply transl_store_access2XS_correct; eauto with asmgen. unfold ireg_of. rewrite roEq. reflexivity. congruence.
    destruct rr; try discriminate. destruct src; simpl in srcEq; try discriminate.
  - exploit transl_store_memory_access2_ok; eauto. intros (mk_instr & chunk' & rr & mr0 & mro & ro & argsEq & roEq & srcEq & A & B & C).
    eapply transl_store_access2_correct; eauto with asmgen. unfold ireg_of. rewrite roEq. reflexivity. congruence.
    destruct rr; try discriminate. destruct src; simpl in srcEq; try discriminate.
  - exploit transl_store_memory_access_ok; eauto; try discriminate; try (simpl; reflexivity).
    intro A;
    destruct A as (mk_instr & chunk' & rr & rrEq & B & C & D);
    rewrite D in STORE; clear D; 
    eapply transl_store_access_correct; eauto with asmgen; try congruence;
    destruct rr; try discriminate; destruct src; try discriminate.
  - exploit transl_store_memory_access_ok; eauto; try discriminate; try (simpl; reflexivity).
    intro A;
    destruct A as (mk_instr & chunk' & rr & rrEq & B & C & D);
    rewrite D in STORE; clear D; 
    eapply transl_store_access_correct; eauto with asmgen; try congruence;
    destruct rr; try discriminate; destruct src; try discriminate.
  - exploit transl_store_memory_access_ok; eauto; try discriminate; try (simpl; reflexivity).
    intro A;
    destruct A as (mk_instr & chunk' & rr & rrEq & B & C & D);
    rewrite D in STORE; clear D; 
    eapply transl_store_access_correct; eauto with asmgen; try congruence;
    destruct rr; try discriminate; destruct src; try discriminate.
Qed.

Lemma make_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  Mach.load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  Mach.load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge (make_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#RA = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, r <> PC -> r <> RA -> r <> SP -> r <> RTMP -> r <> GPRA -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue. 
  rewrite chunk_of_Tptr in *.

  exploit ((loadind_ptr_correct SP (fn_retaddr_ofs f) GPRA (Pset RA GPRA ::g Pfreeframe (fn_stacksize f) (fn_link_ofs f) ::g k))
            rs tm).
  - rewrite <- (sp_val _ _ rs AG). simpl. eexact LRA'.
  - intros (rs1 & A1 & B1 & C1).
    assert (agree ms (Vptr stk soff) rs1) as AG1.
    + destruct AG.
      apply mkagree; auto.
      rewrite C1; discriminate || auto.
      intro. rewrite C1; auto; destruct r; simpl; try discriminate.
    + exploit (Pset_correct RA GPRA (Pfreeframe (fn_stacksize f) (fn_link_ofs f) ::g k) rs1 tm). auto.
      intros (rs2 & A2 & B2 & C2).
      econstructor; econstructor; split.
      * eapply exec_straight_trans.
        { eexact A1. }
        { eapply exec_straight_trans.
          { eapply A2. }
          { apply exec_straight_one. simpl.
            rewrite (C2 SP) by auto with asmgen. rewrite <- (sp_val _ _ rs1 AG1). simpl; rewrite LP'.
            rewrite FREE'. eauto. } }
      * split. apply agree_set_other; auto with asmgen. 
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

 
