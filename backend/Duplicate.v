(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** RTL node duplication using external oracle. Used to form superblock
  structures *)

Require Import AST RTL Maps Globalenvs.
Require Import Coqlib Errors Op.

Local Open Scope error_monad_scope.
Local Open Scope positive_scope.

(** External oracle returning the new RTL code (entry point unchanged),
    along with the new entrypoint, and a mapping of new nodes to old nodes *)
Axiom duplicate_aux: function -> code * node * (PTree.t node).

Extract Constant duplicate_aux => "Duplicateaux.duplicate_aux".

(** * Verification of node duplications *)

Definition verify_is_copy dupmap n n' :=
  match dupmap!n' with
  | None => Error(msg "verify_is_copy None")
  | Some revn => match (Pos.compare n revn) with Eq => OK tt | _ => Error(msg "verify_is_copy invalid map") end
  end.

Fixpoint verify_is_copy_list dupmap ln ln' :=
  match ln with
  | n::ln => match ln' with
             | n'::ln' => do u <- verify_is_copy dupmap n n';
                          verify_is_copy_list dupmap ln ln'
             | nil => Error (msg "verify_is_copy_list: ln' bigger than ln") end
  | nil => match ln' with
          | n :: ln' => Error (msg "verify_is_copy_list: ln bigger than ln'")
          | nil => OK tt end
  end.

Definition verify_mapping_entrypoint dupmap (f f': function): res unit :=
  verify_is_copy dupmap (fn_entrypoint f) (fn_entrypoint f').

Lemma product_eq {A B: Type} :
  (forall (a b: A), {a=b} + {a<>b}) ->
  (forall (c d: B), {c=d} + {c<>d}) ->
  forall (x y: A+B), {x=y} + {x<>y}.
Proof.
  intros H H'. intros. decide equality.
Qed.

(** FIXME Ideally i would like to put this in AST.v but i get an "illegal application"
 * error when doing so *)
Remark builtin_arg_eq_pos: forall (a b: builtin_arg positive), {a=b} + {a<>b}.
Proof.
  intros.
  apply (builtin_arg_eq Pos.eq_dec).
Defined.
Global Opaque builtin_arg_eq_pos.

Remark builtin_res_eq_pos: forall (a b: builtin_res positive), {a=b} + {a<>b}.
Proof. intros. apply (builtin_res_eq Pos.eq_dec). Qed.
Global Opaque builtin_res_eq_pos.

Definition verify_match_inst dupmap inst tinst :=
  match inst with
  | Inop n => match tinst with Inop n' => do u <- verify_is_copy dupmap n n'; OK tt | _ => Error(msg "verify_match_inst Inop") end

  | Iop op lr r n => match tinst with
      Iop op' lr' r' n' =>
          do u <- verify_is_copy dupmap n n';
          if (eq_operation op op') then
            if (list_eq_dec Pos.eq_dec lr lr') then
              if (Pos.eq_dec r r') then
                OK tt
              else Error (msg "Different r in Iop")
            else Error (msg "Different lr in Iop")
          else Error(msg "Different operations in Iop")
      | _ => Error(msg "verify_match_inst Inop") end

  | Iload tm m a lr r n => match tinst with
      | Iload tm' m' a' lr' r' n' =>
          do u <- verify_is_copy dupmap n n';
          if (trapping_mode_eq tm tm') then
            if (chunk_eq m m') then
              if (eq_addressing a a') then
                if (list_eq_dec Pos.eq_dec lr lr') then
                  if (Pos.eq_dec r r') then OK tt
                  else Error (msg "Different r in Iload")
                else Error (msg "Different lr in Iload")
              else Error (msg "Different addressing in Iload")
            else Error (msg "Different mchunk in Iload")
          else Error (msg "Different trapping_mode in Iload")
      | _ => Error (msg "verify_match_inst Iload") end

  | Istore m a lr r n => match tinst with
      | Istore m' a' lr' r' n' =>
          do u <- verify_is_copy dupmap n n';
          if (chunk_eq m m') then
            if (eq_addressing a a') then
              if (list_eq_dec Pos.eq_dec lr lr') then
                if (Pos.eq_dec r r') then OK tt
                else Error (msg "Different r in Istore")
              else Error (msg "Different lr in Istore")
            else Error (msg "Different addressing in Istore")
          else Error (msg "Different mchunk in Istore")
      | _ => Error (msg "verify_match_inst Istore") end

  | Icall s ri lr r n => match tinst with
      | Icall s' ri' lr' r' n' =>
          do u <- verify_is_copy dupmap n n';
          if (signature_eq s s') then
            if (product_eq Pos.eq_dec ident_eq ri ri') then
              if (list_eq_dec Pos.eq_dec lr lr') then
                if (Pos.eq_dec r r') then OK tt
                else Error (msg "Different r r' in Icall")
              else Error (msg "Different lr in Icall")
            else Error (msg "Different ri in Icall")
          else Error (msg "Different signatures in Icall")
      | _ => Error (msg "verify_match_inst Icall") end

  | Itailcall s ri lr => match tinst with
      | Itailcall s' ri' lr' =>
          if (signature_eq s s') then
            if (product_eq Pos.eq_dec ident_eq ri ri') then
              if (list_eq_dec Pos.eq_dec lr lr') then OK tt
              else Error (msg "Different lr in Itailcall")
            else Error (msg "Different ri in Itailcall")
          else Error (msg "Different signatures in Itailcall")
      | _ => Error (msg "verify_match_inst Itailcall") end

  | Ibuiltin ef lbar brr n => match tinst with
      | Ibuiltin ef' lbar' brr' n' =>
          do u <- verify_is_copy dupmap n n';
          if (external_function_eq ef ef') then
            if (list_eq_dec builtin_arg_eq_pos lbar lbar') then
              if (builtin_res_eq_pos brr brr') then OK tt
              else Error (msg "Different brr in Ibuiltin")
            else Error (msg "Different lbar in Ibuiltin")
          else Error (msg "Different ef in Ibuiltin")
      | _ => Error (msg "verify_match_inst Ibuiltin") end

  | Icond cond lr n1 n2 i => match tinst with
      | Icond cond' lr' n1' n2' i' =>
          if (list_eq_dec Pos.eq_dec lr lr') then
            if (eq_condition cond cond') then
              do u1 <- verify_is_copy dupmap n1 n1';
              do u2 <- verify_is_copy dupmap n2 n2'; OK tt
            else if (eq_condition (negate_condition cond) cond') then
              do u1 <- verify_is_copy dupmap n1 n2';
              do u2 <- verify_is_copy dupmap n2 n1'; OK tt
            else Error (msg "Incompatible conditions in Icond")
          else Error (msg "Different lr in Icond")
      | _ => Error (msg "verify_match_inst Icond") end

  | Ijumptable r ln => match tinst with
      | Ijumptable r' ln' =>
          do u <- verify_is_copy_list dupmap ln ln';
          if (Pos.eq_dec r r') then OK tt
          else Error (msg "Different r in Ijumptable")
      | _ => Error (msg "verify_match_inst Ijumptable") end

  | Ireturn or => match tinst with
      | Ireturn or' =>
          if (option_eq Pos.eq_dec or or') then OK tt
          else Error (msg "Different or in Ireturn")
      | _ => Error (msg "verify_match_inst Ireturn") end
  end.

Definition verify_mapping_mn dupmap f f' (m: positive*positive) :=
  let (tn, n) := m in
  match (fn_code f)!n with
  | None => Error (msg "verify_mapping_mn: Could not get an instruction at (fn_code f)!n")
  | Some inst => match (fn_code f')!tn with
                 | None => Error (msg "verify_mapping_mn: Could not get an instruction at (fn_code xf)!tn")
                 | Some tinst => verify_match_inst dupmap inst tinst
                 end
  end.

Fixpoint verify_mapping_mn_rec dupmap f f' lm :=
  match lm with
  | nil => OK tt
  | m :: lm => do u <- verify_mapping_mn dupmap f f' m;
               do u2 <- verify_mapping_mn_rec dupmap f f' lm;
               OK tt
  end.

Definition verify_mapping_match_nodes dupmap (f f': function): res unit :=
  verify_mapping_mn_rec dupmap f f' (PTree.elements dupmap).

(** Verifies that the [dupmap] of the translated function [f'] is giving correct information in regards to [f] *)
Definition verify_mapping dupmap (f f': function) : res unit :=
  do u <- verify_mapping_entrypoint dupmap f f';
  do v <- verify_mapping_match_nodes dupmap f f'; OK tt.

(** * Entry points *)

Definition transf_function (f: function) : res function :=
  let (tcte, dupmap) := duplicate_aux f in
  let (tc, te) := tcte in
  let f' := mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) tc te in
  do u <- verify_mapping dupmap f f';
  OK f'.

Definition transf_fundef (f: fundef) : res fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.
