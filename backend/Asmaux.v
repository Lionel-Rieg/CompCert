Require Import Asm.
Require Import AST.

(* Constant only needed by Asmexpandaux.ml *)
Definition dummy_function := {| fn_code := nil; fn_sig := signature_main |}.