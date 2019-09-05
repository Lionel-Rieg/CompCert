(** RTL node duplication using external oracle. Used to form superblock
  structures *)

Require Import AST RTL Maps.
Require Import Coqlib Errors.

Local Open Scope error_monad_scope.

(** External oracle returning the new RTL code (entry point unchanged),
    along with the new entrypoint, and a mapping of new nodes to old nodes *)
Axiom duplicate_aux: RTL.function -> RTL.code * node * (PTree.t nat).

Extract Constant duplicate_aux => "Duplicateaux.duplicate_aux".

(** * Verification of node duplications *)

(** Verifies that the mapping [mp] is giving correct information *)
Definition verify_mapping (f: function) (tc: code) (tentry: node) (mp: PTree.t nat) : res unit := OK tt. (* TODO *)

(** * Entry points *)

Definition transf_function (f: function) : res function :=
  let (tcte, mp) := duplicate_aux f in
  let (tc, te) := tcte in
  do u <- verify_mapping f tc te mp;
  OK (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) tc te).

Theorem transf_function_preserves:
  forall f tf,
  transf_function f = OK tf ->
     fn_sig f = fn_sig tf /\ fn_params f = fn_params tf /\ fn_stacksize f = fn_stacksize tf.
Proof.
  intros. unfold transf_function in H. destruct (duplicate_aux _) as (tcte & mp). destruct tcte as (tc & te). monadInv H.
  repeat (split; try reflexivity).
Qed.

Remark transf_function_fnsig: forall f tf, transf_function f = OK tf -> fn_sig f = fn_sig tf.
  Proof. apply transf_function_preserves. Qed.
Remark transf_function_fnparams: forall f tf, transf_function f = OK tf -> fn_params f = fn_params tf.
  Proof. apply transf_function_preserves. Qed.
Remark transf_function_fnstacksize: forall f tf, transf_function f = OK tf -> fn_stacksize f = fn_stacksize tf.
  Proof. apply transf_function_preserves. Qed.

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.