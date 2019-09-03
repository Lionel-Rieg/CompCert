(** Correctness proof for code duplication *)
Require Import AST Linking Errors Globalenvs Smallstep.
Require Import Coqlib.
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

Inductive match_nodes: node -> node -> Prop :=
  | match_node_intro: forall n, match_nodes n n
  (* TODO - fill out the rest *)
.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframe_intro:
    forall res f sp pc rs f' pc'
      (TRANSF: transf_function f = OK f')
      (DUPLIC: match_nodes pc pc'),
      match_stackframes (Stackframe res f sp pc rs) (Stackframe res f' sp pc' rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
    forall st f sp pc rs m st' f' pc'
      (STACKS: list_forall2 match_stackframes st st')
      (TRANSF: transf_function f = OK f')
      (DUPLIC: match_nodes pc pc'),
      match_states (State st f sp pc rs m) (State st' f' sp pc' rs m).

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  (* TODO *)
Admitted.

End PRESERVATION.