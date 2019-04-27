Require Import Coqlib.
Require Import Integers.
Require Import Values.

Definition extfz stop start v :=
  if (Z.leb start stop)
       && (Z.geb start Z.zero)
       && (Z.ltb stop Int.zwordsize)
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vint w =>
      Vint (Int.shru (Int.shl w (Int.repr (Z.sub Int.zwordsize stop'))) (Int.repr (Z.sub Int.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.


Definition extfs stop start v :=
  if (Z.leb start stop)
       && (Z.geb start Z.zero)
       && (Z.ltb stop Int.zwordsize)
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vint w =>
      Vint (Int.shr (Int.shl w (Int.repr (Z.sub Int.zwordsize stop'))) (Int.repr (Z.sub Int.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.

Definition extfzl stop start v :=
  if (Z.leb start stop)
       && (Z.geb start Z.zero)
       && (Z.ltb stop Int64.zwordsize)
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vlong w =>
      Vlong (Int64.shru' (Int64.shl' w (Int.repr (Z.sub Int64.zwordsize stop'))) (Int.repr (Z.sub Int64.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.


Definition extfsl stop start v :=
  if (Z.leb start stop)
       && (Z.geb start Z.zero)
       && (Z.ltb stop Int64.zwordsize)
  then
    let stop' := Z.add stop Z.one in
    match v with
    | Vlong w =>
      Vlong (Int64.shr' (Int64.shl' w (Int.repr (Z.sub Int64.zwordsize stop'))) (Int.repr (Z.sub Int64.zwordsize (Z.sub stop' start))))
    | _ => Vundef
    end
  else Vundef.
