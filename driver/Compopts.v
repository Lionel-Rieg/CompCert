(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Compilation options *)

(** This file collects Coq functions to query the command-line
  options that influence the code generated by the verified
  part of CompCert.   These functions are mapped by extraction
  to accessors for the flags in [Clflags.ml]. *)

(** Flag [-Os].  For instruction selection (mainly). *)
Parameter optim_for_size: unit -> bool.

(** Flag [-ffloat-const-prop].  For value analysis and constant propagation. *)
Parameter propagate_float_constants: unit -> bool.
Parameter generate_float_constants: unit -> bool.

(** For value analysis.  Currently always false. *)
Parameter va_strict: unit -> bool.

(** Flag -ftailcalls.  For tail call optimization. *)
Parameter optim_tailcalls: unit -> bool.

(** Flag -fconstprop.  For constant propagation. *)
Parameter optim_constprop: unit -> bool.

(** Flag -fcse.  For common subexpression elimination. *)
Parameter optim_CSE: unit -> bool.

(** Flag -fredundancy.  For dead code elimination. *)
Parameter optim_redundancy: unit -> bool.

(** Flag -fpostpass. Postpass scheduling for K1 architecture *)
Parameter optim_postpass: unit -> bool.

(** Flag -fthumb.  For the ARM back-end. *)
Parameter thumb: unit -> bool.

(** Flag -g.  For insertion of debugging information. *)
Parameter debug: unit -> bool.
