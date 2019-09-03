(** RTL node duplication using external oracle. Used to form superblock
  structures *)

Require Import AST RTL Maps.
Require Import Coqlib Errors.

Local Open Scope error_monad_scope.

(** External oracle returning the new RTL function, along with a mapping
    of new nodes to old nodes *)
Axiom duplicate_aux: RTL.function -> RTL.function * (PTree.t nat).

Extract Constant duplicate_aux => "Duplicateaux.duplicate_aux".

(** * Verification of node duplications *)

(** Verifies that the mapping [mp] is giving correct information *)
Definition verify_mapping (f tf: function) (mp: PTree.t nat) : res unit := OK tt. (* TODO *)

(** * Entry points *)

Definition transf_function (f: function) : res function :=
  let (tf, mp) := duplicate_aux f in
  do u <- verify_mapping f tf mp;
  OK tf.

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.