Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.

Definition transf_function (f: function) : function :=
  let start_pc := Pos.succ (max_pc_function f) in
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := PTree.set start_pc (Inop f.(fn_entrypoint)) f.(fn_code);
     fn_entrypoint := start_pc |}.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

