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

Definition verify_is_copy revmap n n' :=
  match revmap!n' with
  | None => Error(msg "verify_is_copy None")
  | Some revn => match (Pos.compare n revn) with Eq => OK tt | _ => Error(msg "verify_is_copy invalid map") end
  end.

Fixpoint verify_is_copy_list revmap ln ln' :=
  match ln with
  | n::ln => match ln' with
             | n'::ln' => do u <- verify_is_copy revmap n n';
                          verify_is_copy_list revmap ln ln'
             | nil => Error (msg "verify_is_copy_list: ln' bigger than ln") end
  | nil => match ln' with
          | n :: ln' => Error (msg "verify_is_copy_list: ln bigger than ln'")
          | nil => OK tt end
  end.

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

Definition verify_match_inst revmap inst tinst :=
  match inst with
  | Inop n => match tinst with Inop n' => do u <- verify_is_copy revmap n n'; OK tt | _ => Error(msg "verify_match_inst Inop") end

  | Iop op lr r n => match tinst with
      Iop op' lr' r' n' =>
          do u <- verify_is_copy revmap n n';
          if (eq_operation op op') then
            if (list_eq_dec Pos.eq_dec lr lr') then
              if (Pos.eq_dec r r') then
                OK tt
              else Error (msg "Different r in Iop")
            else Error (msg "Different lr in Iop")
          else Error(msg "Different operations in Iop")
      | _ => Error(msg "verify_match_inst Inop") end

  | Iload m a lr r n => match tinst with
      | Iload m' a' lr' r' n' =>
          do u <- verify_is_copy revmap n n';
          if (chunk_eq m m') then
            if (eq_addressing a a') then
              if (list_eq_dec Pos.eq_dec lr lr') then
                if (Pos.eq_dec r r') then OK tt
                else Error (msg "Different r in Iload")
              else Error (msg "Different lr in Iload")
            else Error (msg "Different addressing in Iload")
          else Error (msg "Different mchunk in Iload")
      | _ => Error (msg "verify_match_inst Iload") end

  | Istore m a lr r n => match tinst with
      | Istore m' a' lr' r' n' =>
          do u <- verify_is_copy revmap n n';
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
          do u <- verify_is_copy revmap n n';
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
          do u <- verify_is_copy revmap n n';
          if (external_function_eq ef ef') then
            if (list_eq_dec builtin_arg_eq_pos lbar lbar') then
              if (builtin_res_eq_pos brr brr') then OK tt
              else Error (msg "Different brr in Ibuiltin")
            else Error (msg "Different lbar in Ibuiltin")
          else Error (msg "Different ef in Ibuiltin")
      | _ => Error (msg "verify_match_inst Ibuiltin") end

  | Icond cond lr n1 n2 => match tinst with
      | Icond cond' lr' n1' n2' =>
          do u1 <- verify_is_copy revmap n1 n1';
          do u2 <- verify_is_copy revmap n2 n2';
          if (eq_condition cond cond') then
            if (list_eq_dec Pos.eq_dec lr lr') then OK tt
            else Error (msg "Different lr in Icond")
          else Error (msg "Different cond in Icond")
      | _ => Error (msg "verify_match_inst Icond") end

  | Ijumptable r ln => match tinst with
      | Ijumptable r' ln' =>
          do u <- verify_is_copy_list revmap ln ln';
          if (Pos.eq_dec r r') then OK tt
          else Error (msg "Different r in Ijumptable")
      | _ => Error (msg "verify_match_inst Ijumptable") end

  | Ireturn or => match tinst with
      | Ireturn or' =>
          if (option_eq Pos.eq_dec or or') then OK tt
          else Error (msg "Different or in Ireturn")
      | _ => Error (msg "verify_match_inst Ireturn") end
  end.

Definition verify_mapping_mn f xf (m: positive*positive) :=
  let (tn, n) := m in
  match (fn_code f)!n with
  | None => Error (msg "verify_mapping_mn: Could not get an instruction at (fn_code f)!n")
  | Some inst => match (fn_code (fn_RTL xf))!tn with
                 | None => Error (msg "verify_mapping_mn: Could not get an instruction at (fn_code xf)!tn")
                 | Some tinst => verify_match_inst (fn_revmap xf) inst tinst
                 end
  end.

Fixpoint verify_mapping_mn_rec f xf lm :=
  match lm with
  | nil => OK tt
  | m :: lm => do u <- verify_mapping_mn f xf m;
               do u2 <- verify_mapping_mn_rec f xf lm;
               OK tt
  end.

Definition verify_mapping_match_nodes (f: function) (xf: xfunction) : res unit :=
  verify_mapping_mn_rec f xf (PTree.elements (fn_revmap xf)).

(** Verifies that the [fn_revmap] of the translated function [xf] is giving correct information in regards to [f] *)
Definition verify_mapping (f: function) (xf: xfunction) : res unit :=
  do u <- verify_mapping_entrypoint f xf;
  do v <- verify_mapping_match_nodes f xf; OK tt.
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