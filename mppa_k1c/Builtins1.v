(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Platform-specific built-in functions *)

Require Import String Coqlib.
Require Import AST Integers Floats Values ExtFloats.
Require Import Builtins0.

Inductive platform_builtin : Type :=
| BI_fmin
| BI_fmax
| BI_fminf
| BI_fmaxf.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
     ("__builtin_fmin", BI_fmin)
  :: ("__builtin_fmax", BI_fmax)
  :: ("__builtin_fminf", BI_fminf)
  :: ("__builtin_fmaxf", BI_fmaxf)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_fmin | BI_fmax =>
      mksignature (Tfloat :: Tfloat :: nil) (Some Tfloat) cc_default
  | BI_fminf | BI_fmaxf =>
      mksignature (Tsingle :: Tsingle :: nil) (Some Tsingle) cc_default
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (proj_sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_fmin => mkbuiltin_n2t Tfloat Tfloat Tfloat ExtFloat.min
  | BI_fmax => mkbuiltin_n2t Tfloat Tfloat Tfloat ExtFloat.max
  | BI_fminf => mkbuiltin_n2t Tsingle Tsingle Tsingle ExtFloat32.min
  | BI_fmaxf => mkbuiltin_n2t Tsingle Tsingle Tsingle ExtFloat32.max
  end.
