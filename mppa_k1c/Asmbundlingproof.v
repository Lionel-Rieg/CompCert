
Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Conventions Asmblock.
Require Import Asmbundle Asmbundling.

Definition match_prog (p: program) (tp: program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Asmblock.program.
Variable tprog: Asmblock.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. inv H0; auto.
Qed.

(* Aargh: harder to prove than expected ! *)
Lemma stepi_simulation obi s1 t s2: stepin ge obi s1 t s2 -> stepin tge obi s1 t s2.
Admitted.


(* FIXME: generalize to forward_simulation_plus *)
Theorem step_simulation s1 t s2: step ge s1 t s2 -> bundle_step tge s1 t s2.
Proof.
  intros (obi & H).
  exists obi. constructor 1. 
  - apply stepi_simulation; auto.
  - unfold is_bundle; auto.
Qed.


Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ st1 = st2.
Proof.
  intros st1 H.
  inversion H. unfold ge0 in *.
  econstructor 1; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Genv.symbol_address (Genv.globalenv prog) (prog_main prog) Ptrofs.zero).
  econstructor; eauto.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite! symbols_preserved.
  auto.
Qed.

Local Hint Resolve step_simulation.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (bundle_semantics tprog).
Proof.
  (* FIXME: in general forward_simulation_plus *)
  eapply forward_simulation_step. 
  - apply senv_preserved.
  - eexact transf_initial_states.
  - intros; subst; simpl; auto.
  - intros; subst; simpl in * |- *; eauto.
Qed.

End PRESERVATION.
