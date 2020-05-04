(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*                                                             *)
(*  Copyright VERIMAG. All rights reserved.                    *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

Require Import Coqlib.
Require Import AST Integers Floats.
Require Import Op CminorSel.

(** Some arithmetic operations are transformed into calls to
  runtime library functions.  The following type class collects
  the names of these functions. *)

Definition sig_l_l := mksignature (Tlong :: nil) Tlong cc_default.
Definition sig_l_f := mksignature (Tlong :: nil) Tfloat cc_default.
Definition sig_l_s := mksignature (Tlong :: nil) Tsingle cc_default.
Definition sig_f_l := mksignature (Tfloat :: nil) Tlong cc_default.
Definition sig_ll_l := mksignature (Tlong :: Tlong :: nil) Tlong cc_default.
Definition sig_li_l := mksignature (Tlong :: Tint :: nil) Tlong cc_default.
Definition sig_ii_l := mksignature (Tint :: Tint :: nil) Tlong cc_default.
Definition sig_ii_i := mksignature (Tint :: Tint :: nil) Tint cc_default.
Definition sig_ff_f := mksignature (Tfloat :: Tfloat :: nil) Tfloat cc_default.
Definition sig_ss_s := mksignature (Tsingle :: Tsingle :: nil) Tsingle cc_default.

Class helper_functions := mk_helper_functions {
  i64_dtos: ident;                      (**r float64 -> signed long *)
  i64_dtou: ident;                      (**r float64 -> unsigned long *)
  i64_stod: ident;                      (**r signed long -> float64 *)
  i64_utod: ident;                      (**r unsigned long -> float64 *)
  i64_stof: ident;                      (**r signed long -> float32 *)
  i64_utof: ident;                      (**r unsigned long -> float32 *)
  i64_sdiv: ident;                      (**r signed division *)
  i64_udiv: ident;                      (**r unsigned division *)
  i64_smod: ident;                      (**r signed remainder *)
  i64_umod: ident;                      (**r unsigned remainder *)
  i64_shl: ident;                       (**r shift left *)
  i64_shr: ident;                       (**r shift right unsigned *)
  i64_sar: ident;                       (**r shift right signed *)
  i64_umulh: ident;                     (**r unsigned multiply high *)
  i64_smulh: ident;                     (**r signed multiply high *)
  i32_sdiv: ident;                      (**r signed division *)
  i32_udiv: ident;                      (**r unsigned division *)
  i32_smod: ident;                      (**r signed remainder *)
  i32_umod: ident;                      (**r unsigned remainder *)
  f64_div: ident;                       (**float division*)
  f32_div: ident;                       (**float division*)
}.
