(** Correctness proof for code duplication *)
Require Import AST Linking Errors Globalenvs Smallstep.
Require Import Coqlib Maps Events.
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

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. simpl. symmetry; apply transf_function_preserves. assumption.
  inv H. reflexivity.
Qed.

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
  | match_states_call:
    forall st st' f f' args m
      (STACKS: list_forall2 match_stackframes st st')
      (TRANSF: transf_fundef f = OK f'),
      match_states (Callstate st f args m) (Callstate st' f' args m)
  | match_states_return:
    forall st st' v m
      (STACKS: list_forall2 match_stackframes st st'),
      match_states (Returnstate st v m) (Returnstate st' v m).

Theorem transf_initial_states:
  forall s1, initial_state prog s1 ->
  exists s2, initial_state tprog s2 /\ match_states s1 s2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (tf & FIND & TRANSF).
  eexists. split.
  - econstructor.
    + eapply (Genv.init_mem_transf_partial TRANSL); eauto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved. eauto.
      symmetry. eapply match_program_main. eauto.
    + exploit function_ptr_translated; eauto.
    + destruct f.
      * monadInv TRANSF. rewrite <- H3. symmetry; eapply transf_function_preserves. assumption.
      * monadInv TRANSF. assumption.
  - constructor; eauto. constructor.
Qed.

Theorem transf_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state s1 r -> final_state s2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem step_simulation:
  forall s1 t s1', step ge s1 t s1' ->
  forall s2 (MS: match_states s1 s2),
  exists s2',
     step tge s2 t s2'
  /\ match_states s1' s2'.
Proof.
  induction 1; intros; inv MS.
(* Inop *)
  - admit.
(* Iop *)
  - admit.
(* Iload *)
  - admit.
(* Istore *)
  - admit.
(* Icall *)
  - admit.
(* Itailcall *)
  - admit.
(* Ibuiltin *)
  - admit.
(* Icond *)
  - admit.
(* Ijumptable *)
  - admit.
(* Ireturn *)
  - admit.
(* exec_function_internal *)
  - monadInv TRANSF. eexists. split.
    + econstructor. erewrite <- transf_function_fnstacksize; eauto.
    + erewrite transf_function_fnentrypoint; eauto.
      erewrite transf_function_fnparams; eauto.
      econstructor; eauto. constructor.
(* exec_function_external *)
  - monadInv TRANSF. eexists. split.
    + econstructor. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + constructor. assumption.
(* exec_return *)
  - inv STACKS. destruct b1 as [res' f' sp' pc' rs']. eexists. split.
    + constructor.
    + inv H1. constructor; assumption.
Admitted.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_step with match_states.
  - eapply senv_preserved.
  - eapply transf_initial_states.
  - eapply transf_final_states.
  - eapply step_simulation.
Qed.

End PRESERVATION.
