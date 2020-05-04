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
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import Events.
Require Import OpHelpers.

(** * Axiomatization of the helper functions *)

Definition external_implements (name: string) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall F V (ge: Genv.t F V) m,
  external_call (EF_runtime name sg) ge vargs m E0 vres m.

Definition builtin_implements (name: string) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall F V (ge: Genv.t F V) m,
  external_call (EF_builtin name sg) ge vargs m E0 vres m.

Axiom arith_helpers_correct :
    (forall x z, Val.longoffloat x = Some z -> external_implements "__compcert_i64_dtos" sig_f_l (x::nil) z)
 /\ (forall x z, Val.longuoffloat x = Some z -> external_implements "__compcert_i64_dtou" sig_f_l (x::nil) z)
 /\ (forall x z, Val.floatoflong x = Some z -> external_implements "__compcert_i64_stod" sig_l_f (x::nil) z)
 /\ (forall x z, Val.floatoflongu x = Some z -> external_implements "__compcert_i64_utod" sig_l_f (x::nil) z)
 /\ (forall x z, Val.singleoflong x = Some z -> external_implements "__compcert_i64_stof" sig_l_s (x::nil) z)
 /\ (forall x z, Val.singleoflongu x = Some z -> external_implements "__compcert_i64_utof" sig_l_s (x::nil) z)
 /\ (forall x, builtin_implements "__builtin_negl" sig_l_l (x::nil) (Val.negl x))
 /\ (forall x y, builtin_implements "__builtin_addl" sig_ll_l (x::y::nil) (Val.addl x y))
 /\ (forall x y, builtin_implements "__builtin_subl" sig_ll_l (x::y::nil) (Val.subl x y))
 /\ (forall x y, builtin_implements "__builtin_mull" sig_ii_l (x::y::nil) (Val.mull' x y))
 /\ (forall x y z, Val.divls x y = Some z -> external_implements "__compcert_i64_sdiv" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.divlu x y = Some z -> external_implements "__compcert_i64_udiv" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.modls x y = Some z -> external_implements "__compcert_i64_smod" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.modlu x y = Some z -> external_implements "__compcert_i64_umod" sig_ll_l (x::y::nil) z)
 /\ (forall x y, external_implements "__compcert_i64_shl" sig_li_l (x::y::nil) (Val.shll x y))
 /\ (forall x y, external_implements "__compcert_i64_shr" sig_li_l (x::y::nil) (Val.shrlu x y))
 /\ (forall x y, external_implements "__compcert_i64_sar" sig_li_l (x::y::nil) (Val.shrl x y))
 /\ (forall x y, external_implements "__compcert_i64_umulh" sig_ll_l (x::y::nil) (Val.mullhu x y))
 /\ (forall x y, external_implements "__compcert_i64_smulh" sig_ll_l (x::y::nil) (Val.mullhs x y))
 /\ (forall x y z, Val.divs x y = Some z -> external_implements "__compcert_i32_sdiv" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.divu x y = Some z -> external_implements "__compcert_i32_udiv" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.mods x y = Some z -> external_implements "__compcert_i32_smod" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.modu x y = Some z -> external_implements "__compcert_i32_umod" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.divfs x y = z -> external_implements "__compcert_f32_div" sig_ss_s (x::y::nil) z)
 /\ (forall x y z, Val.divf x y = z -> external_implements "__compcert_f64_div" sig_ff_f (x::y::nil) z)
.

Definition helper_declared {F V: Type} (p: AST.program (AST.fundef F) V) (id: ident) (name: string) (sg: signature) : Prop :=
  (prog_defmap p)!id = Some (Gfun (External (EF_runtime name sg))).

Definition helper_functions_declared {F V: Type} (p: AST.program (AST.fundef F) V) (hf: helper_functions) : Prop :=
     helper_declared p i64_dtos "__compcert_i64_dtos" sig_f_l
  /\ helper_declared p i64_dtou "__compcert_i64_dtou" sig_f_l
  /\ helper_declared p i64_stod "__compcert_i64_stod" sig_l_f
  /\ helper_declared p i64_utod "__compcert_i64_utod" sig_l_f
  /\ helper_declared p i64_stof "__compcert_i64_stof" sig_l_s
  /\ helper_declared p i64_utof "__compcert_i64_utof" sig_l_s
  /\ helper_declared p i64_sdiv "__compcert_i64_sdiv" sig_ll_l
  /\ helper_declared p i64_udiv "__compcert_i64_udiv" sig_ll_l
  /\ helper_declared p i64_smod "__compcert_i64_smod" sig_ll_l
  /\ helper_declared p i64_umod "__compcert_i64_umod" sig_ll_l
  /\ helper_declared p i64_shl "__compcert_i64_shl" sig_li_l
  /\ helper_declared p i64_shr "__compcert_i64_shr" sig_li_l
  /\ helper_declared p i64_sar "__compcert_i64_sar" sig_li_l
  /\ helper_declared p i64_umulh "__compcert_i64_umulh" sig_ll_l
  /\ helper_declared p i64_smulh "__compcert_i64_smulh" sig_ll_l
  /\ helper_declared p i32_sdiv "__compcert_i32_sdiv" sig_ii_i
  /\ helper_declared p i32_udiv "__compcert_i32_udiv" sig_ii_i
  /\ helper_declared p i32_smod "__compcert_i32_smod" sig_ii_i
  /\ helper_declared p i32_umod "__compcert_i32_umod" sig_ii_i
  /\ helper_declared p f32_div  "__compcert_f32_div"  sig_ss_s
  /\ helper_declared p f64_div  "__compcert_f64_div"  sig_ff_f
.
