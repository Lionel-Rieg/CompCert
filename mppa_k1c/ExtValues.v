Require Import Coqlib.
Require Import Integers.
Require Import Values.

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
