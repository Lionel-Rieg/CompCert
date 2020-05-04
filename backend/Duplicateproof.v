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

(** Correctness proof for code duplication *)
Require Import AST Linking Errors Globalenvs Smallstep.
Require Import Coqlib Maps Events Values.
Require Import Op RTL Duplicate.

Local Open Scope positive_scope.

(** * Definition of [match_states] (independently of the translation) *)

(* est-ce plus simple de prendre dupmap: node -> node, avec un noeud hors CFG à la place de None ? *)
Inductive match_inst (dupmap: PTree.t node): instruction -> instruction -> Prop :=
  | match_inst_nop: forall n n',
      dupmap!n' = (Some n) -> match_inst dupmap (Inop n) (Inop n')
  | match_inst_op: forall n n' op lr r,
      dupmap!n' = (Some n) -> match_inst dupmap (Iop op lr r n) (Iop op lr r n')
  | match_inst_load: forall n n' tm m a lr r,
      dupmap!n' = (Some n) -> match_inst dupmap (Iload tm m a lr r n) (Iload tm m a lr r n')
  | match_inst_store: forall n n' m a lr r,
      dupmap!n' = (Some n) -> match_inst dupmap (Istore m a lr r n) (Istore m a lr r n')
  | match_inst_call: forall n n' s ri lr r,
      dupmap!n' = (Some n) -> match_inst dupmap (Icall s ri lr r n) (Icall s ri lr r n')
  | match_inst_tailcall: forall s ri lr,
      match_inst dupmap (Itailcall s ri lr) (Itailcall s ri lr)
  | match_inst_builtin: forall n n' ef la br,
      dupmap!n' = (Some n) -> match_inst dupmap (Ibuiltin ef la br n) (Ibuiltin ef la br n')
  | match_inst_cond: forall ifso ifso' ifnot ifnot' c lr i i',
      dupmap!ifso' = (Some ifso) -> dupmap!ifnot' = (Some ifnot) ->
      match_inst dupmap (Icond c lr ifso ifnot i) (Icond c lr ifso' ifnot' i')
  | match_inst_revcond: forall ifso ifso' ifnot ifnot' c lr i i',
      dupmap!ifso' = (Some ifso) -> dupmap!ifnot' = (Some ifnot) ->
      match_inst dupmap (Icond c lr ifso ifnot i) (Icond (negate_condition c) lr ifnot' ifso' i')
  | match_inst_jumptable: forall ln ln' r,
      list_forall2 (fun n n' => (dupmap!n' = (Some n))) ln ln' ->
      match_inst dupmap (Ijumptable r ln) (Ijumptable r ln')
  | match_inst_return: forall or, match_inst dupmap (Ireturn or) (Ireturn or).

Record match_function dupmap f f': Prop := {
  dupmap_correct: forall n n', dupmap!n' = Some n ->
    (forall i, (fn_code f)!n = Some i -> exists i', (fn_code f')!n' = Some i' /\ match_inst dupmap i i');
  dupmap_entrypoint: dupmap!(fn_entrypoint f') = Some (fn_entrypoint f);
  preserv_fnsig: fn_sig f = fn_sig f';
  preserv_fnparams: fn_params f = fn_params f';
  preserv_fnstacksize: fn_stacksize f = fn_stacksize f'
}.

Inductive match_fundef: RTL.fundef -> RTL.fundef -> Prop :=
  | match_Internal dupmap f f': match_function dupmap f f' -> match_fundef (Internal f) (Internal f')
  | match_External ef: match_fundef (External ef) (External ef).

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframe_intro 
      dupmap res f sp pc rs f' pc'
      (TRANSF: match_function dupmap f f')
      (DUPLIC: dupmap!pc' = Some pc):
      match_stackframes (Stackframe res f sp pc rs) (Stackframe res f' sp pc' rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro 
      dupmap st f sp pc rs m st' f' pc'
      (STACKS: list_forall2 match_stackframes st st')
      (TRANSF: match_function dupmap f f')
      (DUPLIC: dupmap!pc' = Some pc):
      match_states (State st f sp pc rs m) (State st' f' sp pc' rs m)
  | match_states_call:
    forall st st' f f' args m
      (STACKS: list_forall2 match_stackframes st st')
      (TRANSF: match_fundef f f'),
      match_states (Callstate st f args m) (Callstate st' f' args m)
  | match_states_return:
    forall st st' v m
      (STACKS: list_forall2 match_stackframes st st'),
      match_states (Returnstate st v m) (Returnstate st' v m).

(** * Auxiliary properties *)


Theorem transf_function_preserves:
  forall f f',
  transf_function f = OK f' ->
     fn_sig f = fn_sig f' /\ fn_params f = fn_params f' /\ fn_stacksize f = fn_stacksize f'.
Proof.
  intros. unfold transf_function in H. destruct (duplicate_aux _) as (tcte & mp). destruct tcte as (tc & te). monadInv H.
  repeat (split; try reflexivity).
Qed.


Lemma verify_mapping_mn_rec_step:
  forall dupmap lb b f f',
  In b lb ->
  verify_mapping_mn_rec dupmap f f' lb = OK tt ->
  verify_mapping_mn dupmap f f' b = OK tt.
Proof.
  induction lb; intros.
  - monadInv H0. inversion H.
  - inversion H.
    + subst. monadInv H0. destruct x. assumption.
    + monadInv H0. destruct x0. eapply IHlb; assumption.
Qed.

Lemma verify_is_copy_correct:
  forall dupmap n n',
  verify_is_copy dupmap n n' = OK tt ->
  dupmap ! n' = Some n.
Proof.
  intros. unfold verify_is_copy in H. destruct (_ ! n') eqn:REVM; [|inversion H].
  destruct (n ?= p) eqn:NP; try (inversion H; fail).
  eapply Pos.compare_eq in NP. subst.
  reflexivity.
Qed.

Lemma verify_is_copy_list_correct:
  forall dupmap ln ln',
  verify_is_copy_list dupmap ln ln' = OK tt ->
  list_forall2 (fun n n' => dupmap ! n' = Some n) ln ln'.
Proof.
  induction ln.
  - intros. destruct ln'; monadInv H. constructor.
  - intros. destruct ln'; monadInv H. destruct x. apply verify_is_copy_correct in EQ.
    eapply IHln in EQ0. constructor; assumption.
Qed.

Lemma verify_match_inst_correct:
  forall dupmap i i',
  verify_match_inst dupmap i i' = OK tt ->
  match_inst dupmap i i'.
Proof.
  intros. unfold verify_match_inst in H.
  destruct i; try (inversion H; fail).
(* Inop *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_correct in EQ.
    constructor; eauto.
(* Iop *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_correct in EQ.
    destruct (eq_operation _ _); try discriminate.
    destruct (list_eq_dec _ _ _); try discriminate.
    destruct (Pos.eq_dec _ _); try discriminate. clear EQ0. subst.
    constructor. assumption.
(* Iload *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_correct in EQ.
    destruct (trapping_mode_eq _ _); try discriminate.
    destruct (chunk_eq _ _); try discriminate.
    destruct (eq_addressing _ _); try discriminate.
    destruct (list_eq_dec _ _ _); try discriminate.
    destruct (Pos.eq_dec _ _); try discriminate. clear EQ0. subst.
    constructor. assumption.
(* Istore *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_correct in EQ.
    destruct (chunk_eq _ _); try discriminate.
    destruct (eq_addressing _ _); try discriminate.
    destruct (list_eq_dec _ _ _); try discriminate.
    destruct (Pos.eq_dec _ _); try discriminate. clear EQ0. subst.
    constructor. assumption.
(* Icall *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_correct in EQ.
    destruct (signature_eq _ _); try discriminate.
    destruct (product_eq _ _ _ _); try discriminate.
    destruct (list_eq_dec _ _ _); try discriminate.
    destruct (Pos.eq_dec _ _); try discriminate. subst.
    constructor. assumption.
(* Itailcall *)
  - destruct i'; try (inversion H; fail).
    destruct (signature_eq _ _); try discriminate.
    destruct (product_eq _ _ _ _); try discriminate.
    destruct (list_eq_dec _ _ _); try discriminate. subst. clear H.
    constructor.
(* Ibuiltin *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_correct in EQ.
    destruct (external_function_eq _ _); try discriminate.
    destruct (list_eq_dec _ _ _); try discriminate.
    destruct (builtin_res_eq_pos _ _); try discriminate. subst.
    constructor. assumption.
(* Icond *)
  - destruct i'; try (inversion H; fail).
    destruct (list_eq_dec _ _ _); try discriminate. subst.
    destruct (eq_condition _ _); try discriminate.
    + monadInv H. destruct x. eapply verify_is_copy_correct in EQ.
      destruct x0. eapply verify_is_copy_correct in EQ1.
      constructor; assumption.
    + destruct (eq_condition _ _); try discriminate.
      monadInv H. destruct x. eapply verify_is_copy_correct in EQ.
      destruct x0. eapply verify_is_copy_correct in EQ1.
      constructor; assumption.
(* Ijumptable *)
  - destruct i'; try (inversion H; fail). monadInv H.
    destruct x. eapply verify_is_copy_list_correct in EQ.
    destruct (Pos.eq_dec _ _); try discriminate. subst.
    constructor. assumption.
(* Ireturn *)
  - destruct i'; try (inversion H; fail).
    destruct (option_eq _ _ _); try discriminate. subst. clear H.
    constructor.
Qed.


Lemma verify_mapping_mn_correct mp n n' i f f' tc:
  mp ! n' = Some n ->
  (fn_code f) ! n = Some i ->
  (fn_code f') = tc ->
  verify_mapping_mn mp f f' (n', n) = OK tt ->
  exists i',
     tc ! n' = Some i'
  /\ match_inst mp i i'.
Proof.
  unfold verify_mapping_mn; intros H H0 H1 H2. rewrite H0 in H2. clear H0. rewrite H1 in H2. clear H1.
  destruct (tc ! n') eqn:TCN; [| inversion H2].
  exists i0. split; auto.
  eapply verify_match_inst_correct. assumption.
Qed.


Lemma verify_mapping_mn_rec_correct:
  forall mp n n' i f f' tc,
  mp ! n' = Some n ->
  (fn_code f) ! n = Some i ->
  (fn_code f') = tc ->
  verify_mapping_mn_rec mp f f' (PTree.elements mp) = OK tt ->
  exists i',
     tc ! n' = Some i'
  /\ match_inst mp i i'.
Proof.
  intros. exploit PTree.elements_correct. eapply H. intros IN.
  eapply verify_mapping_mn_rec_step in H2; eauto.
  eapply verify_mapping_mn_correct; eauto.
Qed.

Theorem transf_function_correct f f':
    transf_function f = OK f' -> exists dupmap, match_function dupmap f f'.
Proof.
  unfold transf_function.
  intros TRANSF.
  destruct (duplicate_aux _) as (tcte & mp). destruct tcte as (tc & te).
  monadInv TRANSF.
  unfold verify_mapping in EQ. monadInv EQ.
  exists mp; constructor 1; simpl; auto.
  + (* correct *) 
  intros until n'. intros REVM i FNC.
  unfold verify_mapping_match_nodes in EQ. simpl in EQ. destruct x1.
  eapply verify_mapping_mn_rec_correct; eauto.
  simpl; eauto.
  + (* entrypoint *)
  intros. unfold verify_mapping_entrypoint in EQ0. simpl in EQ0.
  eapply verify_is_copy_correct; eauto.
  destruct x0; auto.
Qed.

Lemma transf_fundef_correct f f':
  transf_fundef f = OK f' -> match_fundef f f'.
Proof.
  intros TRANSF; destruct f; simpl; monadInv TRANSF.
  + exploit transf_function_correct; eauto.
    intros (dupmap & MATCH_F).
    eapply match_Internal; eauto.
  + eapply match_External.
Qed.

(** * Preservation proof *)

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

Lemma symbols_preserved s: Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  rewrite <- (Genv.find_symbol_match TRANSL). reflexivity.
Qed.

(* UNUSED LEMMA ?
Lemma senv_transitivity x y z: Senv.equiv x y -> Senv.equiv y z -> Senv.equiv x z.
Proof.
  unfold Senv.equiv. intuition congruence.
Qed.
*)

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  eapply (Genv.senv_match TRANSL).
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf cunit, transf_fundef f = OK tf /\ Genv.find_funct tge v = Some tf /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_match TRANSL); eauto.
  intros (cu & tf & A & B & C).
  repeat eexists; intuition eauto.
  + unfold incl; auto.
  + eapply linkorder_refl.
Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros.
  exploit (Genv.find_funct_ptr_transf_partial TRANSL); eauto.
Qed.

Lemma function_sig_translated:
  forall f tf, transf_fundef f = OK tf -> funsig tf = funsig f.
Proof.
  intros. destruct f.
  - simpl in H. monadInv H. simpl. symmetry. apply transf_function_preserves. assumption.
  - simpl in H. monadInv H. reflexivity.
Qed.

Lemma list_nth_z_dupmap:
  forall dupmap ln ln' (pc pc': node) val,
  list_nth_z ln val = Some pc ->
  list_forall2 (fun n n' => dupmap!n' = Some n) ln ln' ->
  exists pc',
     list_nth_z ln' val = Some pc'
  /\ dupmap!pc' = Some pc.
Proof.
  induction ln; intros until val; intros LNZ LFA.
  - inv LNZ.
  - inv LNZ. destruct (zeq val 0) eqn:ZEQ.
    + inv H0. destruct ln'; inv LFA.
      simpl. exists p. split; auto.
    + inv LFA. simpl. rewrite ZEQ. exploit IHln. 2: eapply H0. all: eauto.
      intros (pc'1 & LNZ & REV). exists pc'1. split; auto. congruence.
Qed.

Theorem transf_initial_states:
  forall s1, initial_state prog s1 ->
  exists s2, initial_state tprog s2 /\ match_states s1 s2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (tf & FIND & TRANSF).
  eexists. split.
  - econstructor; eauto.
    + eapply (Genv.init_mem_transf_partial TRANSL); eauto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved. eauto.
      symmetry. eapply match_program_main. eauto.
    + destruct f.
      * monadInv TRANSF. rewrite <- H3. symmetry; eapply transf_function_preserves. assumption.
      * monadInv TRANSF. assumption.
  - constructor; eauto.
    + constructor. 
    + apply transf_fundef_correct; auto.
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
  Local Hint Resolve transf_fundef_correct: core.
  induction 1; intros; inv MS.
(* Inop *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3).
    inv H3.
    eexists. split.
    + eapply exec_Inop; eauto.
    + econstructor; eauto.
(* Iop *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
    + econstructor; eauto.
(* Iload *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Iload; eauto; (* is the follow still needed?*) erewrite eval_addressing_preserved; eauto.
    + econstructor; eauto.
(* Iload notrap1 *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Iload_notrap1; eauto; erewrite eval_addressing_preserved; eauto. 
    + econstructor; eauto.
(* Iload notrap2 *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Iload_notrap2; eauto; erewrite eval_addressing_preserved; eauto.
    + econstructor; eauto.
      
(* Istore *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Istore; eauto; erewrite eval_addressing_preserved; eauto.
    + econstructor; eauto.
(* Icall *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    destruct ros.
    * simpl in H0. apply functions_translated in H0.
      destruct H0 as (tf & cunit & TFUN & GFIND & LO).
      eexists. split.
      + eapply exec_Icall. eassumption. simpl. eassumption.
        apply function_sig_translated. assumption.
      + repeat (econstructor; eauto).
    * simpl in H0. destruct (Genv.find_symbol _ _) eqn:GFS; try discriminate.
      apply function_ptr_translated in H0. destruct H0 as (tf & GFF & TF).
      eexists. split.
      + eapply exec_Icall. eassumption. simpl. rewrite symbols_preserved. rewrite GFS.
        eassumption. apply function_sig_translated. assumption.
      + repeat (econstructor; eauto).
(* Itailcall *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H10 & H11). inv H11.
    pose symbols_preserved as SYMPRES.
    destruct ros.
    * simpl in H0. apply functions_translated in H0.
      destruct H0 as (tf & cunit & TFUN & GFIND & LO).
      eexists. split.
      + eapply exec_Itailcall. eassumption. simpl. eassumption.
        apply function_sig_translated. assumption.
        erewrite <- preserv_fnstacksize; eauto.
      + repeat (constructor; auto).
    * simpl in H0. destruct (Genv.find_symbol _ _) eqn:GFS; try discriminate.
      apply function_ptr_translated in H0. destruct H0 as (tf & GFF & TF).
      eexists. split.
      + eapply exec_Itailcall. eassumption. simpl. rewrite symbols_preserved. rewrite GFS.
        eassumption. apply function_sig_translated. assumption.
        erewrite <- preserv_fnstacksize; eauto.
      + repeat (constructor; auto).
(* Ibuiltin *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Ibuiltin; eauto. eapply eval_builtin_args_preserved; eauto.
      eapply external_call_symbols_preserved; eauto. eapply senv_preserved.
    + econstructor; eauto.
(* Icond *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    * (* match_inst_cond *)
      pose symbols_preserved as SYMPRES.
      eexists. split.
      + eapply exec_Icond; eauto.
      + econstructor; eauto. destruct b; auto.
    * (* match_inst_revcond *)
      pose symbols_preserved as SYMPRES.
      eexists. split.
      + eapply exec_Icond; eauto. rewrite eval_negate_condition. rewrite H0. simpl. eauto.
      + econstructor; eauto. destruct b; auto.
(* Ijumptable *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    exploit list_nth_z_dupmap; eauto. intros (pc'1 & LNZ & REVM).
    eexists. split.
    + eapply exec_Ijumptable; eauto.
    + econstructor; eauto.
(* Ireturn *)
  - eapply dupmap_correct in DUPLIC; eauto.
    destruct DUPLIC as (i' & H2 & H3). inv H3.
    pose symbols_preserved as SYMPRES.
    eexists. split.
    + eapply exec_Ireturn; eauto. erewrite <- preserv_fnstacksize; eauto.
    + econstructor; eauto.
(* exec_function_internal *)
  - inversion TRANSF as [dupmap f0 f0' MATCHF|]; subst. eexists. split.
    + eapply exec_function_internal. erewrite <- preserv_fnstacksize; eauto.
    + erewrite preserv_fnparams; eauto.
      econstructor; eauto. apply dupmap_entrypoint. assumption.
(* exec_function_external *)
  - inversion TRANSF as [|]; subst. eexists. split.
    + econstructor. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + constructor. assumption.
(* exec_return *)
  - inv STACKS. destruct b1 as [res' f' sp' pc' rs']. eexists. split.
    + constructor.
    + inv H1. econstructor; eauto.
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
