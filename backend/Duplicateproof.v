(** Correctness proof for code duplication *)
Require Import AST Linking Errors Globalenvs Smallstep.
Require Import Coqlib Maps.
Require Import RTL Duplicate.

Definition match_prog (p tp: program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Inductive match_nodes (f: function): node -> node -> Prop :=
  | match_node_intro: forall n, match_nodes f n n
  | match_node_nop: forall n n' n1 n1',
      (fn_code f)!n  = Some (Inop n1) ->
      (fn_code f)!n' = Some (Inop n1') ->
      match_nodes f n1 n1' ->
      match_nodes f n n'
  | match_node_op: forall n n' n1 n1' op lr r,
      (fn_code f)!n  = Some (Iop op lr r n1) ->
      (fn_code f)!n' = Some (Iop op lr r n1') ->
      match_nodes f n1 n1' ->
      match_nodes f n n'
  | match_node_load: forall n n' n1 n1' m a lr r,
      (fn_code f)!n  = Some (Iload m a lr r n1) ->
      (fn_code f)!n' = Some (Iload m a lr r n1') ->
      match_nodes f n1 n1' ->
      match_nodes f n n'
  | match_node_store: forall n n' n1 n1' m a lr r,
      (fn_code f)!n  = Some (Istore m a lr r n1) ->
      (fn_code f)!n' = Some (Istore m a lr r n1') ->
      match_nodes f n1 n1' ->
      match_nodes f n n'
  | match_node_call: forall n n' n1 n1' s ri lr r,
      (fn_code f)!n  = Some (Icall s ri lr r n1) ->
      (fn_code f)!n' = Some (Icall s ri lr r n1') ->
      match_nodes f n1 n1' ->
      match_nodes f n n'
  | match_node_tailcall: forall n n' s ri lr,
      (fn_code f)!n  = Some (Itailcall s ri lr) ->
      (fn_code f)!n' = Some (Itailcall s ri lr) ->
      match_nodes f n n'
  | match_node_builtin: forall n n' n1 n1' ef la br,
      (fn_code f)!n  = Some (Ibuiltin ef la br n1) ->
      (fn_code f)!n' = Some (Ibuiltin ef la br n1') ->
      match_nodes f n1 n1' ->
      match_nodes f n n'
  | match_node_cond: forall n n' n1 n1' n2 n2' c lr,
      (fn_code f)!n  = Some (Icond c lr n1 n2) ->
      (fn_code f)!n' = Some (Icond c lr n1' n2') ->
      match_nodes f n1 n1' ->
      match_nodes f n2 n2' ->
      match_nodes f n n'
  | match_node_jumptable: forall n n' ln ln' r,
      (fn_code f)!n  = Some (Ijumptable r ln) ->
      (fn_code f)!n' = Some (Ijumptable r ln') ->
      list_forall2 (match_nodes f) ln ln' ->
      match_nodes f n n'
  | match_node_return: forall n n' or,
      (fn_code f)!n  = Some (Ireturn or) ->
      (fn_code f)!n  = Some (Ireturn or) ->
      match_nodes f n n'
.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframe_intro:
    forall res f sp pc rs f' pc'
      (TRANSF: transf_function f = OK f')
      (DUPLIC: match_nodes f pc pc'),
      match_stackframes (Stackframe res f sp pc rs) (Stackframe res f' sp pc' rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
    forall st f sp pc rs m st' f' pc'
      (STACKS: list_forall2 match_stackframes st st')
      (TRANSF: transf_function f = OK f')
      (DUPLIC: match_nodes f pc pc'),
      match_states (State st f sp pc rs m) (State st' f' sp pc' rs m)
  (* TODO - fill the rest *).

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  (* TODO *)
Admitted.

End PRESERVATION.
