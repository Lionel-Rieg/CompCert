(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                Jacques-Henri Jourdan, INRIA Paris                   *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for MPPA K1c. Mostly copied from the Risc-V backend *)

Require Import ZArith List.
Require Import Binary Bits.

Definition ptr64 := true.

Definition big_endian := false.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong. destruct ptr64; simpl; congruence. 
Qed.

(** THIS IS NOT CHECKED ! NONE OF THIS ! *)

(** Section 7.3: "Except when otherwise stated, if the result of a
   floating-point operation is NaN, it is the canonical NaN. The
   canonical NaN has a positive sign and all significand bits clear
   except the MSB, a.k.a. the quiet bit."
   We need to extend the [choose_binop_pl] functions to account for
   this case. *)

Definition default_nan_64 := (false, iter_nat 51 _ xO xH).
Definition default_nan_32 := (false, iter_nat 22 _ xO xH).

(* Always choose the first NaN argument, if any *)

Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_32 | n :: _ => n end.

Definition fpu_returns_default_qNaN := false.

Lemma choose_nan_64_idem: forall n,
  choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. auto. Qed.

Lemma choose_nan_32_idem: forall n,
  choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. auto. Qed.

Definition fma_order {A: Type} (x y z: A) := (x, z, y).

Definition fma_invalid_mul_is_nan := false.
Definition float_of_single_preserves_sNaN := false.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_nan_64
              default_nan_32 choose_nan_32
              fma_order fma_invalid_mul_is_nan
              float_of_single_preserves_sNaN.

(** Whether to generate position-independent code or not *)

Parameter pic_code: unit -> bool.
