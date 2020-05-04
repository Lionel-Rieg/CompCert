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

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.


Definition transf_ros (ros: reg + ident) : reg + ident := ros.

Definition transf_instr (pc: node) (instr: instruction) :=
  match instr with
  | Iload trap chunk addr args dst s => Iload NOTRAP chunk addr args dst s
  | _ => instr
  end.

Definition transf_function (f: function) : function :=
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := PTree.map transf_instr f.(fn_code);
     fn_entrypoint := f.(fn_entrypoint) |}.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

