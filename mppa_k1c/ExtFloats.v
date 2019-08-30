Require Import Floats Integers ZArith.

Module ExtFloat.
(** TODO check with the actual K1c;
    this is what happens on x86 and may be inappropriate. *)

Definition min (x : float) (y : float) : float :=
  match Float.compare x y with
  | Some Eq | Some Lt => x
  | Some Gt | None => y
  end.

Definition max (x : float) (y : float) : float :=
  match Float.compare x y with
  | Some Eq | Some Gt => x
  | Some Lt | None => y
  end.
End ExtFloat.

Module ExtFloat32.
(** TODO check with the actual K1c *)

Definition min (x : float32) (y : float32) : float32 :=
  match Float32.compare x y with
  | Some Eq | Some Lt => x
  | Some Gt | None => y
  end.

Definition max (x : float32) (y : float32) : float32 :=
  match Float32.compare x y with
  | Some Eq | Some Gt => x
  | Some Lt | None => y
  end.

Definition inv (x : float32) : float32 :=
  Float32.div (Float32.of_int (Int.repr (1%Z))) x.

End ExtFloat32.
