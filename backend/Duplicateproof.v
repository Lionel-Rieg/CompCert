(** Correctness proof for code duplication *)
Require Import AST Linking Errors Globalenvs Smallstep.
Require Import Coqlib Maps Events Values.
Require Import Op RTL Duplicate.

Definition match_prog (p tp: program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(* est-ce plus simple de prendre is_copy: node -> node, avec un noeud hors CFG à la place de None ? *)
Inductive match_inst (is_copy: node -> option node): instruction -> instruction -> Prop :=
  | match_inst_nop: forall n n',
      is_copy n' = (Some n) -> match_inst is_copy (Inop n) (Inop n')
  | match_inst_op: forall n n' op lr r,
      is_copy n' = (Some n) -> match_inst is_copy (Iop op lr r n) (Iop op lr r n')
  | match_inst_load: forall n n' m a lr r,
      is_copy n' = (Some n) -> match_inst is_copy (Iload m a lr r n) (Iload m a lr r n')
  | match_inst_store: forall n n' m a lr r,
      is_copy n' = (Some n) -> match_inst is_copy (Istore m a lr r n) (Istore m a lr r n')
  | match_inst_call: forall n n' s ri lr r,
      is_copy n' = (Some n) -> match_inst is_copy (Icall s ri lr r n) (Icall s ri lr r n')
  | match_inst_tailcall: forall n n' s ri lr,
      is_copy n' = (Some n) -> match_inst is_copy (Itailcall s ri lr) (Itailcall s ri lr)
  | match_inst_builtin: forall n n' ef la br,
      is_copy n' = (Some n) -> match_inst is_copy (Ibuiltin ef la br n) (Ibuiltin ef la br n')
  | match_inst_cond: forall ifso ifso' ifnot ifnot' c lr,
      is_copy ifso' = (Some ifso) -> is_copy ifnot' = (Some ifnot) ->
      match_inst is_copy (Icond c lr ifso ifnot) (Icond c lr ifso' ifnot')
  | match_inst_jumptable: forall ln ln' r,
      list_forall2 (fun n n' => (is_copy n' = (Some n))) ln ln' ->
      match_inst is_copy (Ijumptable r ln) (Ijumptable r ln')
  | match_inst_return: forall or, match_inst is_copy (Ireturn or) (Ireturn or).

Axiom revmap: function -> node -> option node. (* mapping from nodes of [tprog], to nodes of [prog], for function [f] *)

Axiom revmap_correct: forall f f' n n',
    transf_function f = OK f' ->
    revmap f n' = Some n ->
    (forall i, (fn_code f)!n = Some i -> exists i', (fn_code f')!n' = Some i' /\ match_inst (revmap f) i i').

Axiom revmap_entrypoint:
  forall f f', transf_function f = OK f' -> revmap f (fn_entrypoint f') = Some (fn_entrypoint f).

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

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf cunit, transf_fundef f = OK tf /\ Genv.find_funct tge v = Some tf /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_match TRANSL); eauto.
  intros (cu & tf & A & B & C). exists tf, cu. split; auto.
Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma function_sig_translated:
  forall f f', transf_fundef f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f.
  - simpl in H. monadInv H. simpl. symmetry. apply transf_function_preserves. assumption.
  - simpl in H. monadInv H. reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. simpl. symmetry; apply transf_function_preserves. assumption.
  inv H. reflexivity.
Qed.

Lemma list_nth_z_revmap:
  forall ln f ln' (pc pc': node) val,
  list_nth_z ln val = Some pc ->
  list_forall2 (fun n n' => revmap f n' = Some n) ln ln' ->
  exists pc',
     list_nth_z ln' val = Some pc'
  /\ revmap f pc' = Some pc.
Proof.
  induction ln; intros until val; intros LNZ LFA.
  - inv LNZ.
  - inv LNZ. destruct (zeq val 0) eqn:ZEQ.
    + inv H0. destruct ln'; inv LFA.
      simpl. exists n. split; auto.
    + inv LFA. simpl. rewrite ZEQ. exploit IHln. 2: eapply H0. all: eauto.
      intros (pc'1 & LNZ & REV). exists pc'1. split; auto. congruence.
Qed.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframe_intro:
    forall res f sp pc rs f' pc'
      (TRANSF: transf_function f = OK f')
      (DUPLIC: revmap f pc' = Some pc),
      match_stackframes (Stackframe res f sp pc rs) (Stackframe res f' sp pc' rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
    forall st f sp pc rs m st' f' pc'
      (STACKS: list_forall2 match_stackframes st st')
      (TRANSF: transf_function f = OK f')
      (DUPLIC: revmap f pc' = Some pc),
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
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3).
    inv H3.
    eexists. split.
    + eapply exec_Inop; eauto.
    + constructor; eauto.
(* Iop *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
    + constructor; eauto.
(* Iload *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Iload; eauto. erewrite eval_addressing_preserved; eauto.
    + constructor; auto.
(* Istore *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Istore; eauto. erewrite eval_addressing_preserved; eauto.
    + constructor; auto.
(* Icall *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    destruct ros.
    * simpl in H0. apply functions_translated in H0.
      destruct H0 as (tf & cunit & TFUN & GFIND & LO).
      eexists. split.
      + eapply exec_Icall. eassumption. simpl. eassumption.
        apply function_sig_translated. assumption.
      + repeat (constructor; auto).
    * simpl in H0. destruct (Genv.find_symbol _ _) eqn:GFS; try discriminate.
      apply function_ptr_translated in H0. destruct H0 as (tf & GFF & TF).
      eexists. split.
      + eapply exec_Icall. eassumption. simpl. rewrite symbols_preserved. rewrite GFS.
        eassumption. apply function_sig_translated. assumption.
      + repeat (constructor; auto).
(* Itailcall *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H10 & H11). inv H11.
    pose symbols_preserved as SYMPRES.
    destruct ros.
    * simpl in H0. apply functions_translated in H0.
      destruct H0 as (tf & cunit & TFUN & GFIND & LO).
      eexists. split.
      + eapply exec_Itailcall. eassumption. simpl. eassumption.
        apply function_sig_translated. assumption.
        erewrite <- transf_function_fnstacksize; eauto.
      + repeat (constructor; auto).
    * simpl in H0. destruct (Genv.find_symbol _ _) eqn:GFS; try discriminate.
      apply function_ptr_translated in H0. destruct H0 as (tf & GFF & TF).
      eexists. split.
      + eapply exec_Itailcall. eassumption. simpl. rewrite symbols_preserved. rewrite GFS.
        eassumption. apply function_sig_translated. assumption.
        erewrite <- transf_function_fnstacksize; eauto.
      + repeat (constructor; auto).
(* Ibuiltin *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Ibuiltin; eauto. eapply eval_builtin_args_preserved; eauto.
      eapply external_call_symbols_preserved; eauto. eapply senv_preserved.
    + constructor; auto.
(* Icond *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Icond; eauto.
    + constructor; auto. destruct b; auto.
(* Ijumptable *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    exploit list_nth_z_revmap; eauto. intros (pc'1 & LNZ & REVM).
    eexists. split.
    + eapply exec_Ijumptable; eauto.
    + constructor; auto.
(* Ireturn *)
  - eapply revmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Ireturn; eauto. erewrite <- transf_function_fnstacksize; eauto.
    + constructor; auto.
(* exec_function_internal *)
  - monadInv TRANSF. eexists. split.
    + econstructor. erewrite <- transf_function_fnstacksize; eauto.
    + erewrite transf_function_fnparams; eauto.
      econstructor; eauto. apply revmap_entrypoint. assumption.
(* exec_function_external *)
  - monadInv TRANSF. eexists. split.
    + econstructor. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + constructor. assumption.
(* exec_return *)
  - inv STACKS. destruct b1 as [res' f' sp' pc' rs']. eexists. split.
    + constructor.
    + inv H1. constructor; assumption.
Qed.

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
