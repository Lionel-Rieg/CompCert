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

Require Import Asmblock.

(** Oracle taking as input a basic block,
    returns a basic block with its instruction reordered *)
Axiom schedule: bblock -> bblock.

(** Oracle taking as input a basic block
    splits it into several bblocks (representing bundles *)
Axiom split: bblock -> list bblock.

(* TODO - separate the postpass_schedule in two phases *)

Definition postpass_schedule (lb : list bblock) : list bblock :=
  match lb with
  | nil => nil
  | (cons b lb) => split (schedule b) ++ lb
  end.

Definition transf_function (f: function) : function :=
  mkfunction (fn_sig f) (postpass_schedule (fn_blocks f)).

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.