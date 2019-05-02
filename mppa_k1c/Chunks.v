Require Import AST.
Require Import Values.
Require Import Integers.

Local Open Scope Z_scope.

Definition zscale_of_chunk (chunk: memory_chunk) :=
  match chunk with
  | Mint8signed => 0
  | Mint8unsigned => 0
  | Mint16signed => 1
  | Mint16unsigned => 1
  | Mint32 => 2
  | Mint64 => 3
  | Mfloat32 => 2
  | Mfloat64 => 3
  | Many32 => 2
  | Many64 => 3
  end.
Definition scale_of_chunk chunk := Vint (Int.repr (zscale_of_chunk chunk)).
