Require Import Coqlib.
Require Import Integers.
Require Import Values.

Inductive shift1_4 : Type :=
| SHIFT1 | SHIFT2 | SHIFT3 | SHIFT4.

Definition z_of_shift1_4 (x : shift1_4) :=
  match x with
  | SHIFT1 => 1
  | SHIFT2 => 2
  | SHIFT3 => 3
  | SHIFT4 => 4
  end.

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