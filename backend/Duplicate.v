(** RTL node duplication using external oracle. Used to form superblock
  structures *)

Require Import AST RTL Maps Globalenvs.
Require Import Coqlib Errors.

Local Open Scope error_monad_scope.

(** External oracle returning the new RTL code (entry point unchanged),
    along with the new entrypoint, and a mapping of new nodes to old nodes *)
Axiom duplicate_aux: function -> code * node * (PTree.t node).

Extract Constant duplicate_aux => "Duplicateaux.duplicate_aux".

Record xfunction : Type := 
 { fn_RTL: function;
   fn_revmap: PTree.t node;
 }.

Definition xfundef := AST.fundef xfunction.
Definition xprogram := AST.program xfundef unit.
Definition xgenv := Genv.t xfundef unit.

Definition fundef_RTL (fu: xfundef) : fundef := 
  match fu with
  | Internal f => Internal (fn_RTL f)
  | External ef => External ef
  end.

(** * Verification of node duplications *)

(** Verifies that the mapping [mp] is giving correct information *)
Definition verify_mapping (xf: xfunction) (tc: code) (tentry: node) : res unit := OK tt. (* TODO *)

(** * Entry points *)

Definition transf_function (f: function) : res xfunction :=
  let (tcte, mp) := duplicate_aux f in
  let (tc, te) := tcte in
  let xf := {| fn_RTL := (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) tc te); fn_revmap := mp |} in
  do u <- verify_mapping xf tc te;
  OK xf.

Theorem transf_function_preserves:
  forall f xf,
  transf_function f = OK xf ->
     fn_sig f = fn_sig (fn_RTL xf) /\ fn_params f = fn_params (fn_RTL xf) /\ fn_stacksize f = fn_stacksize (fn_RTL xf).
Proof.
  intros. unfold transf_function in H. destruct (duplicate_aux _) as (tcte & mp). destruct tcte as (tc & te). monadInv H.
  repeat (split; try reflexivity).
Qed.

Remark transf_function_fnsig: forall f xf, transf_function f = OK xf -> fn_sig f = fn_sig (fn_RTL xf).
  Proof. apply transf_function_preserves. Qed.
Remark transf_function_fnparams: forall f xf, transf_function f = OK xf -> fn_params f = fn_params (fn_RTL xf).
  Proof. apply transf_function_preserves. Qed.
Remark transf_function_fnstacksize: forall f xf, transf_function f = OK xf -> fn_stacksize f = fn_stacksize (fn_RTL xf).
  Proof. apply transf_function_preserves. Qed.

Definition transf_fundef_aux (f: fundef) : res xfundef :=
  transf_partial_fundef transf_function f.

Definition transf_fundef (f: fundef): res fundef :=
  do xf <- transf_fundef_aux f;
  OK (fundef_RTL xf).

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.