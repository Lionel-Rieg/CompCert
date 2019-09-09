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

(** FIXME TEMPORARY Flag -fglobaladdrtmp. Use a temporary register for loading the address of global variables (default false) *)
Parameter optim_globaladdrtmp: unit -> bool.

(** FIXME TEMPORARY Flag -fglobaladdroffset. Fold offsets into global addresses  (default false) *)
Parameter optim_globaladdroffset: unit -> bool.

(** FIXME TEMPORARY Flag -fxsaddr. Use .xs addressing mode (default true) *)
Parameter optim_xsaddr: unit -> bool.

(** FIXME TEMPORARY Flag -fcoaelesce-mem. Fuse (default true) *)
Parameter optim_coalesce_mem: unit -> bool.

(** FIXME TEMPORARY Flag -faddx. Fuse (default false) *)
Parameter optim_addx: unit -> bool.

(** Flag -fthumb.  For the ARM back-end. *)
Parameter thumb: unit -> bool.

(** Flag -g.  For insertion of debugging information. *)
Parameter debug: unit -> bool.

(** Flag -fall-loads-nontrap. Turn user loads into non trapping. *)
Parameter all_loads_nontrap: unit -> bool.