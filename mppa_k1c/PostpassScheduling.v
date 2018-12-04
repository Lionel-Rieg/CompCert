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

Require Import Coqlib Errors AST.
Require Import Asmblock.

Local Open Scope error_monad_scope.

(** Oracle taking as input a basic block,
    returns a basic block with its instructions reordered *)
Axiom schedule: bblock -> bblock.

(* TODO - implement the verificator *)
Definition transf_block (b : bblock) : res bblock := OK (schedule b).

Fixpoint transf_blocks (lb : list bblock) : res (list bblock) :=
  match lb with
  | nil => OK nil
  | (cons b lb) =>
      do lb' <- transf_blocks lb;
      do b' <- transf_block b;
      OK (b' :: lb')
  end.

Definition transf_function (f: function) : res function :=
  do lb <- transf_blocks (fn_blocks f);
  OK (mkfunction (fn_sig f) lb).

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.