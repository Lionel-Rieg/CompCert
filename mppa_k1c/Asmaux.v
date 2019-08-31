Require Import Asm.
Require Import AST.

(** Constant only needed by Asmexpandaux.ml *)
Program Definition dummy_function := {| fn_code := nil; fn_sig := signature_main; fn_blocks := nil |}.
