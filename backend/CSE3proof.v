(*
Replace available expressions by the register containing their value.

Proofs.

David Monniaux, CNRS, VERIMAG
 *)

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE3 CSE3analysis CSE3analysisproof.
Require Import RTLtyping.

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.
End SOUNDNESS.


Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
    Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  apply (Genv.find_funct_transf_partial TRANSF).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof.
  apply (Genv.find_funct_ptr_transf_partial TRANSF).
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  apply (Genv.find_symbol_match TRANSF).
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  apply (Genv.senv_match TRANSF).
Qed.

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> funsig tf = funsig f.
Proof.
  destruct f; simpl; intros.
  - monadInv H.
    monadInv EQ.
    destruct preanalysis as [invariants hints].
    destruct check_inductiveness.
    2: discriminate.
    inv EQ1.
    reflexivity.
  - monadInv H.
    reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
    find_function ge ros rs = Some fd ->
    exists tfd,
      find_function tge ros rs = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Inductive match_stackframes: list stackframe -> list stackframe -> signature -> Prop :=
  | match_stackframes_nil: forall sg,
      sg.(sig_res) = Tint ->
      match_stackframes nil nil sg
  | match_stackframes_cons:
      forall res f sp pc rs s tf bb ls ts sg tenv
        (STACKS: match_stackframes s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (WTF: wt_function f tenv)
        (WTRS: wt_regset tenv rs)
        (WTRES: tenv res = proj_sig_res sg),
      match_stackframes
        (Stackframe res f sp pc rs :: s)
        (Stackframe res tf sp ls bb :: ts)
        sg.

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc rs m ts tf tenv
        (STACKS: match_stackframes s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (WTF: wt_function f tenv)
        (WTRS: wt_regset tenv rs),
      match_states (State s f sp pc rs m)
                   (State ts tf sp pc rs m)
  | match_states_call:
      forall s f args m ts tf
        (STACKS: match_stackframes s ts (funsig tf))
        (FUN: transf_fundef f = OK tf)
        (WTARGS: Val.has_type_list args (sig_args (funsig tf))),
      match_states (Callstate s f args m)
                   (Callstate ts tf args m)
  | match_states_return:
      forall s res m ts sg
        (STACKS: match_stackframes s ts sg)
        (WTRES: Val.has_type res (proj_sig_res sg)),
      match_states (Returnstate s res m)
                   (Returnstate ts res m).

Lemma match_stackframes_change_sig:
  forall s ts sg sg',
  match_stackframes s ts sg ->
  sg'.(sig_res) = sg.(sig_res) ->
  match_stackframes s ts sg'.
Proof.
  intros. inv H.
  constructor. congruence.
  econstructor; eauto.
  unfold proj_sig_res in *. rewrite H0; auto.
Qed.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
              exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
Admitted.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto.
  intros (tf & A & B).
  exists (Callstate nil tf nil m0); split.
  - econstructor; eauto.
    + eapply (Genv.init_mem_match TRANSF); eauto.
    + replace (prog_main tprog) with (prog_main prog).
      rewrite symbols_preserved. eauto.
      symmetry. eapply match_program_main; eauto.
    + rewrite <- H3. eapply sig_preserved; eauto.
  - constructor; trivial.
    + constructor. rewrite sig_preserved with (f:=f) by assumption.
      rewrite H3. reflexivity.
    + rewrite sig_preserved with (f:=f) by assumption.
      rewrite H3. reflexivity.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
