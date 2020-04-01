Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.
Require Inject.

Definition gen_injections (f : function) (max_pc : node) (max_reg : reg):
  PTree.t (list Inject.inj_instr) := PTree.empty (list Inject.inj_instr).

Opaque gen_injections.

Definition transf_program : program -> res program :=
  Inject.transf_program gen_injections.
