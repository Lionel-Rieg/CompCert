(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

Require Import Integers.
Require Import Mach Asm Asmblock Asmblockgen Machblockgen.
Require Import PostpassScheduling.
Require Import Errors String.

Local Open Scope error_monad_scope.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  let mbp := (time "Machblock generation" Machblockgen.transf_program) p in
  do abp <- (time "Asmblock generation" Asmblockgen.transf_program) mbp;
  do abp' <- (time "PostpassScheduling total oracle+verification" PostpassScheduling.transf_program) abp;
  OK ((time "Asm generation" Asm.transf_program) abp').

Definition transf_function (f: Mach.function) : res Asm.function :=
  let mbf := Machblockgen.transf_function f in
  do abf <- Asmblockgen.transf_function mbf;
  OK (Asm.transf_function abf).

Definition transl_code (f: Mach.function) (l: Mach.code) : res (list Asm.instruction) :=
  let mbf := Machblockgen.transf_function f in
  let mbc := Machblockgen.trans_code l in
  do abc <- transl_blocks mbf mbc true;
  OK (unfold abc).
