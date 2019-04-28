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
