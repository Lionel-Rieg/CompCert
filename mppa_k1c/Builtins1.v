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

(** Platform-specific built-in functions *)

Require Import String Coqlib.
Require Import AST Integers Floats Values ExtFloats.
Require Import Builtins0.

Inductive platform_builtin : Type :=
| BI_fmin
| BI_fmax
| BI_fminf
| BI_fmaxf
| BI_fabsf
| BI_fma
| BI_fmaf.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
     ("__builtin_fmin", BI_fmin)
  :: ("__builtin_fmax", BI_fmax)
  :: ("__builtin_fminf", BI_fminf)
  :: ("__builtin_fmaxf", BI_fmaxf)
  :: ("__builtin_fabsf", BI_fabsf)
  :: ("__builtin_fma", BI_fma)
  :: ("__builtin_fmaf", BI_fmaf)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_fmin | BI_fmax =>
      mksignature (Tfloat :: Tfloat :: nil) Tfloat cc_default
  | BI_fminf | BI_fmaxf =>
      mksignature (Tsingle :: Tsingle :: nil) Tsingle cc_default
  | BI_fabsf =>
      mksignature (Tsingle :: nil) Tsingle cc_default
  | BI_fma =>
      mksignature (Tfloat :: Tfloat :: Tfloat :: nil) Tfloat cc_default
  | BI_fmaf =>
      mksignature (Tsingle :: Tsingle :: Tsingle :: nil) Tsingle cc_default
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_fmin => mkbuiltin_n2t Tfloat Tfloat Tfloat ExtFloat.min
  | BI_fmax => mkbuiltin_n2t Tfloat Tfloat Tfloat ExtFloat.max
  | BI_fminf => mkbuiltin_n2t Tsingle Tsingle Tsingle ExtFloat32.min
  | BI_fmaxf => mkbuiltin_n2t Tsingle Tsingle Tsingle ExtFloat32.max
  | BI_fabsf => mkbuiltin_n1t Tsingle Tsingle Float32.abs
  | BI_fma => mkbuiltin_n3t Tfloat Tfloat Tfloat Tfloat Float.fma
  | BI_fmaf => mkbuiltin_n3t Tsingle Tsingle Tsingle Tsingle Float32.fma
  end.
