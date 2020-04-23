Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.
Require Inject.

Axiom gen_injections : function -> node -> reg -> PTree.t (list Inject.inj_instr).

Definition transf_program : program -> res program :=
  Inject.transf_program gen_injections.
