Require Archi.
Require Import Coqlib Errors.
Require Import AST Integers Floats Memdata.
Require Import Op Locations Asmblock Asmbundle.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(* FIXME: STUB *)

Definition transl_blocks (lb: Asmblock.bblocks): res Asmblock.bblocks :=
  OK lb
.

Definition transf_function (f: Asmblock.function) :=
  do lb <- transl_blocks f.(Asmblock.fn_blocks);
  OK (mkfunction f.(Asmblock.fn_sig) lb).

Definition transf_fundef (f: Asmblock.fundef) : res Asmblock.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asmblock.program) : res Asmblock.program :=
  transform_partial_program transf_fundef p.
