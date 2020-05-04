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

Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Floats ExtFloats.

Open Scope Z_scope.

Definition abs_diff (x y : Z) := Z.abs (x - y).
Definition abs_diff2 (x y : Z) :=
  if x <=? y then y - x else x - y.
Lemma abs_diff2_correct :
  forall x y : Z, (abs_diff x y) = (abs_diff2 x y).
Proof.
  intros.
  unfold abs_diff, abs_diff2.
  unfold Z.leb.
  pose proof (Z.compare_spec x y) as Hspec.
  inv Hspec.
  - rewrite Z.abs_eq; omega.
  - rewrite Z.abs_neq; omega.
  - rewrite Z.abs_eq; omega.
Qed.

Inductive shift1_4 : Type :=
| SHIFT1 | SHIFT2 | SHIFT3 | SHIFT4.

Definition z_of_shift1_4 (x : shift1_4) :=
  match x with
  | SHIFT1 => 1
  | SHIFT2 => 2
  | SHIFT3 => 3
  | SHIFT4 => 4
  end.

Definition shift1_4_of_z (x : Z) :=
  if Z.eq_dec x 1 then Some SHIFT1
  else if Z.eq_dec x 2 then Some SHIFT2
  else if Z.eq_dec x 3 then Some SHIFT3
  else if Z.eq_dec x 4 then Some SHIFT4
  else None.

Lemma shift1_4_of_z_correct :
  forall z,
    match shift1_4_of_z z with
    | Some x => z_of_shift1_4 x = z
    | None => True
    end.
Proof.
  intro. unfold shift1_4_of_z.
  destruct (Z.eq_dec _ _); simpl; try congruence.
  destruct (Z.eq_dec _ _); simpl; try congruence.
  destruct (Z.eq_dec _ _); simpl; try congruence.
  destruct (Z.eq_dec _ _); simpl; try congruence.
  trivial.
Qed.

Definition int_of_shift1_4 (x : shift1_4) :=
  Int.repr (z_of_shift1_4 x).

Definition is_bitfield stop start :=
  (Z.leb start stop)
    && (Z.geb start Z.zero)
    && (Z.ltb stop Int.zwordsize).

Definition extfz stop start v :=
  if is_bitfield stop start 
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vint w =>
      Vint (Int.shru (Int.shl w (Int.repr (Z.sub Int.zwordsize stop'))) (Int.repr (Z.sub Int.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.


Definition extfs stop start v :=
  if is_bitfield stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vint w =>
      Vint (Int.shr (Int.shl w (Int.repr (Z.sub Int.zwordsize stop'))) (Int.repr (Z.sub Int.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.

Definition zbitfield_mask stop start :=
  (Z.shiftl 1 (Z.succ stop)) - (Z.shiftl 1 start).

Definition bitfield_mask stop start :=
  Vint(Int.repr (zbitfield_mask stop start)).

Definition bitfield_maskl stop start :=
  Vlong(Int64.repr (zbitfield_mask stop start)).

Definition insf stop start prev fld :=
  let mask := bitfield_mask stop start in
  if is_bitfield stop start
  then
    Val.or (Val.and prev (Val.notint mask))
           (Val.and (Val.shl fld (Vint (Int.repr start))) mask)
  else Vundef.

Definition is_bitfieldl stop start :=
  (Z.leb start stop)
    && (Z.geb start Z.zero)
    && (Z.ltb stop Int64.zwordsize).

Definition extfzl stop start v :=
  if is_bitfieldl stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vlong w =>
      Vlong (Int64.shru' (Int64.shl' w (Int.repr (Z.sub Int64.zwordsize stop'))) (Int.repr (Z.sub Int64.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.


Definition extfsl stop start v :=
  if is_bitfieldl stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vlong w =>
      Vlong (Int64.shr' (Int64.shl' w (Int.repr (Z.sub Int64.zwordsize stop'))) (Int.repr (Z.sub Int64.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.

Definition insfl stop start prev fld :=
  let mask := bitfield_maskl stop start in
  if is_bitfieldl stop start
  then
    Val.orl (Val.andl prev (Val.notl mask))
            (Val.andl (Val.shll fld (Vint (Int.repr start))) mask)
  else Vundef.

Fixpoint highest_bit (x : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n1 =>
    let n' := Z.of_N (N_of_nat n) in
    if Z.testbit x n'
    then n'
    else highest_bit x n1
  end.

Definition int_highest_bit (x : int) : Z :=
  highest_bit (Int.unsigned x) (31%nat).


Definition int64_highest_bit (x : int64) : Z :=
  highest_bit (Int64.unsigned x) (63%nat).

Definition val_shrx (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 31)
     then Vint(Int.shrx n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition val_shrxl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 63)
     then Vlong(Int64.shrx' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Remark modulus_fits_64: Int.modulus < Int64.max_unsigned.
Proof.
  compute.
  trivial.
Qed.

Remark unsigned64_repr :
  forall i,
    -1 < i < Int.modulus ->
    Int64.unsigned (Int64.repr i) = i.
Proof.
  intros i H.
  destruct H as [Hlow Hhigh].
  apply Int64.unsigned_repr.
  split. { omega. }
  pose proof modulus_fits_64.
  omega.
Qed.
  
Theorem divu_is_divlu: forall v1 v2 : val,
    Val.divu v1 v2 =
    match Val.divlu (Val.longofintu v1) (Val.longofintu v2) with
    | None => None
    | Some q => Some (Val.loword q)
    end.
Proof.
  intros.
  destruct v1; simpl; trivial.
  destruct v2; simpl; trivial.
  destruct i as [i_val i_range].
  destruct i0 as [i0_val i0_range].
  simpl.
  unfold Int.eq, Int64.eq, Int.zero, Int64.zero.
  simpl.
  rewrite Int.unsigned_repr by (compute; split; discriminate).
  rewrite (Int64.unsigned_repr 0) by (compute; split; discriminate).
  rewrite (unsigned64_repr i0_val) by assumption.
  destruct (zeq i0_val 0) as [ | Hnot0]; simpl; trivial.
  f_equal. f_equal.
  unfold Int.divu, Int64.divu. simpl.
  rewrite (unsigned64_repr i_val) by assumption.
  rewrite (unsigned64_repr i0_val) by assumption.
  unfold Int64.loword.
  rewrite Int64.unsigned_repr.
  reflexivity.
  destruct (Z.eq_dec i0_val 1).
  {subst i0_val.
   pose proof modulus_fits_64.
   rewrite Zdiv_1_r.
   omega.
  }
  destruct (Z.eq_dec i_val 0).
  { subst i_val. compute.
    split;
    intro ABSURD;
    discriminate ABSURD. }
  assert ((i_val / i0_val) < i_val).
  { apply Z_div_lt; omega. }
  split.
  { apply Z_div_pos; omega. }
  pose proof modulus_fits_64.
  omega.
Qed.
  
Theorem modu_is_modlu: forall v1 v2 : val,
    Val.modu v1 v2 =
    match Val.modlu (Val.longofintu v1) (Val.longofintu v2) with
    | None => None
    | Some q => Some (Val.loword q)
    end.
Proof.
  intros.
  destruct v1; simpl; trivial.
  destruct v2; simpl; trivial.
  destruct i as [i_val i_range].
  destruct i0 as [i0_val i0_range].
  simpl.
  unfold Int.eq, Int64.eq, Int.zero, Int64.zero.
  simpl.
  rewrite Int.unsigned_repr by (compute; split; discriminate).
  rewrite (Int64.unsigned_repr 0) by (compute; split; discriminate).
  rewrite (unsigned64_repr i0_val) by assumption.
  destruct (zeq i0_val 0) as [ | Hnot0]; simpl; trivial.
  f_equal. f_equal.
  unfold Int.modu, Int64.modu. simpl.
  rewrite (unsigned64_repr i_val) by assumption.
  rewrite (unsigned64_repr i0_val) by assumption.
  unfold Int64.loword.
  rewrite Int64.unsigned_repr.
  reflexivity.
  assert((i_val mod i0_val) < i0_val).
  apply Z_mod_lt.
  omega.
  split.
  { apply Z_mod_lt.
    omega. }
  pose proof modulus_fits_64.
  omega.
Qed.

Remark if_zlt_0_half_modulus :
  forall T : Type,
  forall x y: T,
    (if (zlt 0 Int.half_modulus) then x else y) = x.
Proof.
  reflexivity.
Qed.

Remark if_zlt_mone_half_modulus :
  forall T : Type,
  forall x y: T,
    (if (zlt (Int.unsigned Int.mone) Int.half_modulus) then x else y) = y.
Proof.
  reflexivity.
Qed.

Remark if_zlt_min_signed_half_modulus :
  forall T : Type,
  forall x y: T,
    (if (zlt (Int.unsigned (Int.repr Int.min_signed))
                     Int.half_modulus)
    then x
     else y)  = y.
Proof.
  reflexivity.
Qed.

Lemma repr_unsigned64_repr:
  forall x, Int.repr (Int64.unsigned (Int64.repr x)) = Int.repr x.
Proof.
  intros.
  apply Int.eqm_samerepr.
  unfold Int.eqm.
  unfold Zbits.eqmod.
  pose proof (Int64.eqm_unsigned_repr x) as H64.
  unfold Int64.eqm in H64.
  unfold Zbits.eqmod in H64.
  destruct H64 as [k64 H64].
  change Int64.modulus with 18446744073709551616 in *.
  change Int.modulus with 4294967296.
  exists (-4294967296 * k64).
  set (y := Int64.unsigned (Int64.repr x)) in *.
  rewrite H64.
  clear H64.
  omega.
Qed.

(*
Theorem divs_is_divls: forall v1 v2 : val,
    match Val.divs v1 v2 with
    | Some q =>
      match Val.divls (Val.longofint v1) (Val.longofint v2) with
      | None => False
      | Some q' => q = Val.loword q'
      end
    | None => True
    end.
Proof.
  intros.
  destruct v1; simpl; trivial.
  destruct v2; simpl; trivial.
  destruct i as [i_val i_range].
  destruct i0 as [i0_val i0_range].
  simpl.
  unfold Int.eq, Int64.eq, Int.zero, Int64.zero.
  simpl.
  replace (Int.unsigned (Int.repr 0)) with 0 in * by reflexivity.
  destruct (zeq _ _) as [H0' | Hnot0]; simpl; trivial.
  destruct (zeq i_val (Int.unsigned (Int.repr Int.min_signed))) as [Hmin | Hnotmin]; simpl.
  { subst.
    destruct (zeq i0_val (Int.unsigned Int.mone)) as [Hmone | Hnotmone]; trivial.
    unfold Int.signed. simpl.
    replace (Int64.unsigned (Int64.repr 0)) with 0 in * by reflexivity.
    rewrite if_zlt_min_signed_half_modulus.
    replace (if
           zeq
             (Int64.unsigned
                (Int64.repr
                   (Int.unsigned (Int.repr Int.min_signed) - Int.modulus)))
             (Int64.unsigned (Int64.repr Int64.min_signed))
          then true
              else false) with false by reflexivity.
    simpl.
    rewrite orb_false_r.
    destruct (zlt i0_val Int.half_modulus) as [Hlt_half | Hge_half].
    {
      replace Int.half_modulus with 2147483648 in * by reflexivity.
      rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; omega).
      destruct (zeq _ _) as [ | Hneq0]; try omega. clear Hneq0.
      unfold Val.loword.
      f_equal.
      unfold Int64.divs, Int.divs, Int64.loword.
      unfold Int.signed, Int64.signed. simpl.      
      rewrite if_zlt_min_signed_half_modulus.
      change Int.half_modulus with 2147483648 in *.
      destruct (zlt _ _) as [discard|]; try omega. clear discard.
      change (Int64.unsigned
                  (Int64.repr
                     (Int.unsigned (Int.repr Int.min_signed) - Int.modulus)))
      with 18446744071562067968.
      change Int64.half_modulus with 9223372036854775808.
      change Int64.modulus with 18446744073709551616.
      simpl.
      rewrite (Int64.unsigned_repr i0_val) by (change Int64.max_unsigned with 18446744073709551615; omega).
      destruct (zlt i0_val 9223372036854775808) as [discard |]; try omega.
      clear discard.
      change (Int.unsigned (Int.repr Int.min_signed) - Int.modulus) with  (-2147483648).
      destruct (Z.eq_dec i0_val 1) as [H1 | Hnot1].
      { subst.
        rewrite Z.quot_1_r.
        apply Int.eqm_samerepr.
        unfold Int.eqm.
        change (Int64.unsigned (Int64.repr (-2147483648))) with 18446744071562067968.
        unfold Zbits.eqmod.
        change Int.modulus with 4294967296.
        exists (-4294967296).
        compute.
        reflexivity.
      }
      change (-2147483648) with (-(2147483648)).
      rewrite Z.quot_opp_l by assumption.
      rewrite repr_unsigned64_repr.
      reflexivity.
    }
    destruct (zeq _ _) as [Hmod|Hnmod].
    {
      rewrite Int64.unsigned_repr_eq in Hmod.
      set (delta := (i0_val - Int.modulus)) in *.
      assert (delta = Int64.modulus*(delta/Int64.modulus)) as Hdelta.
      { apply Z_div_exact_full_2.
        compute. omega.
        assumption. }
      set (k := (delta / Int64.modulus)) in *.
      change Int64.modulus with 18446744073709551616 in *.
      change Int.modulus with 4294967296 in *.
      change Int.half_modulus with 2147483648 in *.
      change (Int.unsigned Int.mone) with 4294967295 in *.
      omega.
    }
    unfold Int.divs, Int64.divs, Val.loword, Int64.loword.
    change (Int.unsigned (Int.repr Int.min_signed)) with 2147483648.
    change Int.modulus with 4294967296.
    change (Int64.signed (Int64.repr (2147483648 - 4294967296))) with (-2147483648).
    f_equal.
    change (Int.signed {| Int.intval := 2147483648; Int.intrange := i_range |})
           with (-2147483648).
    rewrite Int64.signed_repr.
    {
      replace (Int.signed {| Int.intval := i0_val; Int.intrange := i0_range |}) with (i0_val - 4294967296).
      { rewrite repr_unsigned64_repr.
        reflexivity.
      }
 *)

Lemma big_unsigned_signed:
  forall x,
    (Int.unsigned x >= Int.half_modulus) ->
    (Int.signed x) = (Int.unsigned x) - Int.modulus.
Proof.
  destruct x as [xval xrange].
  intro BIG.
  unfold Int.signed, Int.unsigned in *. simpl in *.
  destruct (zlt _ _).
  omega.
  trivial.
Qed.

(*
Lemma signed_0_eqb :
  forall x, (Z.eqb (Int.signed x) 0) = Int.eq x Int.zero.
Qed.
 *)

Lemma Z_quot_le: forall a b,
    0 <= a -> 1 <= b -> Z.quot a b <= a.
Proof.
  intros a b Ha Hb.
  destruct (Z.eq_dec b 1) as [Hb1 | Hb1].
  { (* b=1 *)
    subst.
    rewrite Z.quot_1_r.
    auto with zarith.
  }
  destruct (Z.eq_dec a 0) as [Ha0 | Ha0].
  { (* a=0 *)
    subst.
    rewrite Z.quot_0_l.
    auto with zarith.
    omega.
  }
  assert ((Z.quot a b) < a).
  {
    apply Z.quot_lt; omega.
  }
  auto with zarith.
Qed.

(*
Lemma divs_is_quot: forall v1 v2 : val,
    Val.divs v1 v2 =
    match v1, v2 with
    | (Vint w1), (Vint w2) =>
      let q := Z.quot (Int.signed w1) (Int.signed w2) in
      if (negb (Z.eqb (Int.signed w2) 0))
           && (Z.geb q Int.min_signed) && (Z.leb q Int.max_signed)
      then Some (Vint (Int.repr q))
      else None
    | _, _ => None
    end.

Proof.
  destruct v1; destruct v2; simpl; trivial.
  unfold Int.divs.
  rewrite signed_0_eqb.
  destruct (Int.eq i0 Int.zero) eqn:Eeq0; simpl; trivial.
  destruct (Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone) eqn:EXCEPTION.
  { replace (Int.signed i0) with (-1).
    replace (Int.signed i) with Int.min_signed.
    change Int.min_signed with (-2147483648).
    change Int.max_signed with (2147483647).
    compute.
    reflexivity.
    { unfold Int.eq in EXCEPTION.
      destruct (zeq _ _) as [Hmin | ]  in EXCEPTION; try discriminate.
      change Int.min_signed with (-2147483648).
      change (Int.unsigned (Int.repr Int.min_signed)) with (2147483648) in *.
      rewrite big_unsigned_signed.
      change Int.modulus with 4294967296.
      omega.
      change Int.half_modulus with 2147483648.
      omega.
    }
    unfold Int.eq in EXCEPTION.
    destruct (zeq _ _) in EXCEPTION; try discriminate.
    destruct (zeq _ _) as [Hmone | ]  in EXCEPTION; try discriminate.
    destruct i0 as [i0val i0range]; unfold Int.signed in *; simpl in *.
    rewrite Hmone.
    reflexivity.
  }
  replace (Int.signed i ÷ Int.signed i0 >=? Int.min_signed) with true.
  replace (Int.signed i ÷ Int.signed i0 <=? Int.max_signed) with true.
  reflexivity.
  { assert (Int.signed i ÷ Int.signed i0 <= Int.max_signed).
    {
      destruct (Z_lt_le_dec (Int.signed i) 0).
      {
        apply Z.le_trans with (m:=0).
        rewrite <- (Z.quot_0_l (Int.signed i0)).
        Require Import Coq.ZArith.Zquot.
        apply Z_quot_monotone.                                      
      }
        assert ( Int.signed i ÷ Int.signed i0 <= Int.signed i).
      apply Z_quot_le.
    }
  }

 *)

Require Import Coq.ZArith.Zquot.
Lemma Z_quot_pos_pos_bound: forall a b m,
    0 <= a <= m -> 1 <= b -> 0 <= Z.quot a b <= m.
Proof.
  intros.
  split.
  { rewrite <- (Z.quot_0_l b) by omega.
    apply Z_quot_monotone; omega.
  }
  apply Z.le_trans with (m := a).
  {
    apply Z_quot_le; tauto.
  }
  tauto.
Qed.
Lemma Z_quot_neg_pos_bound: forall a b m,
    m <= a <= 0 -> 1 <= b -> m <= Z.quot a b <= 0.
  intros.
  assert (0 <= - (a ÷ b) <= -m).
  {
    rewrite <- Z.quot_opp_l by omega.
    apply Z_quot_pos_pos_bound; omega.
  }
  omega.
Qed.

Lemma Z_quot_signed_pos_bound: forall a b,
    Int.min_signed <= a <= Int.max_signed -> 1 <= b ->
    Int.min_signed <= Z.quot a b <= Int.max_signed.
Proof.
  intros.
  destruct (Z_lt_ge_dec a 0).
  {
    split.
    { apply Z_quot_neg_pos_bound; omega. }
    { eapply Z.le_trans with (m := 0).
      { apply Z_quot_neg_pos_bound with (m := Int.min_signed); trivial.
        split. tauto. auto with zarith.
      }
      discriminate.
    }
  }
  { split.
    { eapply Z.le_trans with (m := 0).
      discriminate.
      apply Z_quot_pos_pos_bound with (m := Int.max_signed); trivial.
      split. omega. tauto.
    }
    { apply Z_quot_pos_pos_bound; omega.
    }
  }
Qed.

Lemma Z_quot_signed_neg_bound: forall a b,
    Int.min_signed <= a <= Int.max_signed -> b < -1 ->
    Int.min_signed <= Z.quot a b <= Int.max_signed.
Proof.
  change Int.min_signed with (-2147483648).
  change Int.max_signed with 2147483647.
  intros.

  replace b with (-(-b)) by auto with zarith.
  rewrite Z.quot_opp_r by omega.
  assert (-2147483647 <= (a ÷ - b) <= 2147483648).
  2: omega.
  
  destruct (Z_lt_ge_dec a 0).
  {
    replace a with (-(-a)) by auto with zarith.
    rewrite Z.quot_opp_l by omega.
    assert (-2147483648 <= - a ÷ - b <= 2147483647).
    2: omega.
    split.
    {
      rewrite Z.quot_opp_l by omega.
      assert (a ÷ - b <= 2147483648).
      2: omega.
      {
        apply Z.le_trans with (m := 0).
        rewrite <- (Z.quot_0_l (-b)) by omega.
        apply Z_quot_monotone; omega.
        discriminate.
      }
    }
    assert (- a ÷ - b < -a ).
    2: omega.
    apply Z_quot_lt; omega.
  }
  {
    split.
    { apply Z.le_trans with (m := 0).
      discriminate.
      rewrite <- (Z.quot_0_l (-b)) by omega.
      apply Z_quot_monotone; omega.
    }
    { apply Z.le_trans with (m := a).
      apply Z_quot_le.
      all: omega.
    }
  }
Qed.

Lemma sub_add_neg :
  forall x y, Val.sub x y = Val.add x (Val.neg y).
Proof.
  destruct x; destruct y; simpl; trivial.
  f_equal.
  apply Int.sub_add_opp.
Qed.

Lemma neg_mul_distr_r :
  forall x y, Val.neg (Val.mul x y) = Val.mul x (Val.neg y).
Proof.
  destruct x; destruct y; simpl; trivial.
  f_equal.
  apply Int.neg_mul_distr_r.
Qed.

(* pointer diff
Lemma sub_addl_negl :
  forall x y, Val.subl x y = Val.addl x (Val.negl y).
Proof.
  destruct x; destruct y; simpl; trivial.
  + f_equal. apply Int64.sub_add_opp.
  + destruct (Archi.ptr64) eqn:ARCHI64; trivial.
    f_equal. rewrite Ptrofs.sub_add_opp.
    pose (Ptrofs.agree64_neg ARCHI64 (Ptrofs.of_int64 i0) i0) as Hagree.
    unfold Ptrofs.agree64 in Hagree.
    unfold Ptrofs.add.
    f_equal. f_equal.
    rewrite Hagree.
    pose (Ptrofs.agree64_of_int ARCHI64 (Int64.neg i0)) as Hagree2.
    rewrite Hagree2.
    reflexivity.
    exact (Ptrofs.agree64_of_int ARCHI64 i0).
  +  destruct (Archi.ptr64) eqn:ARCHI64; simpl; trivial.
     destruct (eq_block _ _); simpl; trivial.
Qed.
 *)

Lemma negl_mull_distr_r :
  forall x y, Val.negl (Val.mull x y) = Val.mull x (Val.negl y).
Proof.
  destruct x; destruct y; simpl; trivial.
  f_equal.
  apply Int64.neg_mul_distr_r.
Qed.

Definition addx sh v1 v2 :=
  Val.add v2 (Val.shl v1 (Vint sh)).

Definition addxl sh v1 v2 :=
  Val.addl v2 (Val.shll v1 (Vint sh)).

Definition revsubx sh v1 v2 :=
  Val.sub v2 (Val.shl v1 (Vint sh)).

Definition revsubxl sh v1 v2 :=
  Val.subl v2 (Val.shll v1 (Vint sh)).

Definition minf v1 v2 :=
  match v1, v2 with
  | (Vfloat f1), (Vfloat f2) => Vfloat (ExtFloat.min f1 f2)
  | _, _ => Vundef
  end.

Definition maxf v1 v2 :=
  match v1, v2 with
  | (Vfloat f1), (Vfloat f2) => Vfloat (ExtFloat.max f1 f2)
  | _, _ => Vundef
  end.

Definition minfs v1 v2 :=
  match v1, v2 with
  | (Vsingle f1), (Vsingle f2) => Vsingle (ExtFloat32.min f1 f2)
  | _, _ => Vundef
  end.

Definition maxfs v1 v2 :=
  match v1, v2 with
  | (Vsingle f1), (Vsingle f2) => Vsingle (ExtFloat32.max f1 f2)
  | _, _ => Vundef
  end.

Definition invfs v1 :=
  match v1 with
  | (Vsingle f1) => Vsingle (ExtFloat32.inv f1)
  | _ => Vundef
  end.

Definition triple_op_float f v1 v2 v3 :=
  match v1, v2, v3 with
  | (Vfloat f1), (Vfloat f2), (Vfloat f3) => Vfloat (f f1 f2 f3)
  | _, _, _ => Vundef
  end.

Definition triple_op_single f v1 v2 v3 :=
  match v1, v2, v3 with
  | (Vsingle f1), (Vsingle f2), (Vsingle f3) => Vsingle (f f1 f2 f3)
  | _, _, _ => Vundef
  end.

Definition fmaddf := triple_op_float (fun f1 f2 f3 => Float.fma f2 f3 f1).
Definition fmaddfs := triple_op_single (fun f1 f2 f3 => Float32.fma f2 f3 f1).

Definition fmsubf := triple_op_float (fun f1 f2 f3 => Float.fma (Float.neg f2) f3 f1).
Definition fmsubfs := triple_op_single (fun f1 f2 f3 => Float32.fma (Float32.neg f2) f3 f1).
