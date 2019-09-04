(** RTL node duplication using external oracle. Used to form superblock
  structures *)

Require Import AST RTL Maps.
Require Import Coqlib Errors.

Local Open Scope error_monad_scope.

(** External oracle returning the new RTL code (entry point unchanged),
    along with a mapping of new nodes to old nodes *)
Axiom duplicate_aux: RTL.function -> RTL.code * (PTree.t nat).

Extract Constant duplicate_aux => "Duplicateaux.duplicate_aux".

(** * Verification of node duplications *)

(** Verifies that the mapping [mp] is giving correct information *)
Definition verify_mapping (f: function) (tc: code) (mp: PTree.t nat) : res unit := OK tt. (* TODO *)

(** * Entry points *)

Definition transf_function (f: function) : res function :=
  let (tc, mp) := duplicate_aux f in
  do u <- verify_mapping f tc mp;
  OK (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) tc (fn_entrypoint f)).

Theorem transf_function_preserves:
  forall f tf,
  transf_function f = OK tf ->
     fn_sig f = fn_sig tf /\ fn_params f = fn_params tf /\ fn_stacksize f = fn_stacksize tf /\ fn_entrypoint f = fn_entrypoint tf.
Proof.
  intros. unfold transf_function in H. destruct (duplicate_aux _) as (tc & mp). monadInv H.
  repeat (split; try reflexivity).
Qed.

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.