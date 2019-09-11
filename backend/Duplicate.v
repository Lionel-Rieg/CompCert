(** RTL node duplication using external oracle. Used to form superblock
  structures *)

Require Import AST RTL Maps Globalenvs.
Require Import Coqlib Errors.

Local Open Scope error_monad_scope.
Local Open Scope positive_scope.

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

Definition verify_mapping_entrypoint (f: function) (xf: xfunction) : res unit :=
  match ((fn_revmap xf)!(fn_entrypoint (fn_RTL xf))) with
  | None => Error (msg "verify_mapping: No node in xf revmap for entrypoint")
  | Some n => match (Pos.compare n (fn_entrypoint f)) with
              | Eq => OK tt
              | _ => Error (msg "verify_mapping_entrypoint: xf revmap for entrypoint does not correspond to the entrypoint of f")
              end
  end.

(** Verifies that the [fn_revmap] of the translated function [xf] is giving correct information in regards to [f] *)
Definition verify_mapping (f: function) (xf: xfunction) : res unit :=
  do u <- verify_mapping_entrypoint f xf; OK tt.
(* TODO - verify the other axiom *)

(** * Entry points *)

Definition transf_function_aux (f: function) : res xfunction :=
  let (tcte, mp) := duplicate_aux f in
  let (tc, te) := tcte in
  let xf := {| fn_RTL := (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) tc te); fn_revmap := mp |} in
  do u <- verify_mapping f xf;
  OK xf.

Theorem transf_function_aux_preserves:
  forall f xf,
  transf_function_aux f = OK xf ->
     fn_sig f = fn_sig (fn_RTL xf) /\ fn_params f = fn_params (fn_RTL xf) /\ fn_stacksize f = fn_stacksize (fn_RTL xf).
Proof.
  intros. unfold transf_function_aux in H. destruct (duplicate_aux _) as (tcte & mp). destruct tcte as (tc & te). monadInv H.
  repeat (split; try reflexivity).
Qed.

Remark transf_function_aux_fnsig: forall f xf, transf_function_aux f = OK xf -> fn_sig f = fn_sig (fn_RTL xf).
  Proof. apply transf_function_aux_preserves. Qed.
Remark transf_function_aux_fnparams: forall f xf, transf_function_aux f = OK xf -> fn_params f = fn_params (fn_RTL xf).
  Proof. apply transf_function_aux_preserves. Qed.
Remark transf_function_aux_fnstacksize: forall f xf, transf_function_aux f = OK xf -> fn_stacksize f = fn_stacksize (fn_RTL xf).
  Proof. apply transf_function_aux_preserves. Qed.

Definition transf_function (f: function) : res function :=
  do xf <- transf_function_aux f;
  OK (fn_RTL xf).

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.