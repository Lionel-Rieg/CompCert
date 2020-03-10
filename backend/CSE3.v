Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps CSE2deps.
Require Import CSE3analysis HashedSet.

Axiom preanalysis : RTL.function -> analysis_hints.

Definition run f := preanalysis f.

Definition transf_instr (fmap : analysis_hints)
           (pc: node) (instr: instruction) := instr.

Definition transf_function (f: function) : function :=
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := PTree.map (transf_instr (preanalysis f)) f.(fn_code);
     fn_entrypoint := f.(fn_entrypoint) |}.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
