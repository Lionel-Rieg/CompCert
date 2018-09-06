(***

Variante de Forward Simulation pour les blocks.

***)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.


Local Open Scope nat_scope.


Section ForwardSimuBlock.

Variable L1 L2: semantics.

Local Hint Resolve starN_refl starN_step.

Lemma starN_last_step n s t1 s': 
  starN (step L1) (globalenv L1) n s t1 s' ->
  forall (t t2:trace) s'',
     Step L1 s' t2 s'' -> t = t1 ** t2 -> starN (step L1) (globalenv L1) (S n) s t s''.
Proof.
  induction 1; simpl. 
  + intros t t1 s0; autorewrite with trace_rewrite.
    intros; subst; eapply starN_step; eauto.
    autorewrite with trace_rewrite; auto.
  + intros. eapply  starN_step; eauto.
    intros; subst; autorewrite with trace_rewrite; auto.
Qed.

(** Hypothèses de la preuve *)

Variable dist_end_block: state L1 -> nat.

Hypothesis simu_mid_block:
  forall s1 t s1', Step L1 s1 t s1' -> (dist_end_block s1)<>0 -> t = E0 /\ dist_end_block s1=S (dist_end_block s1').

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 -> exists s2, match_states s1 s2 /\ initial_state L2 s2.

Hypothesis match_final_states:
  forall s1 s2 r, final_state L1 s1 r -> match_states s1 s2 -> final_state L2 s2 r.

Hypothesis final_states_end_block:
  forall s1 t s1' r, Step L1 s1 t s1' -> final_state L1 s1' r -> dist_end_block s1 = 0.

Hypothesis simu_end_block:
  forall s1 t s1' s2, starN (step L1) (globalenv L1) (S (dist_end_block s1)) s1 t s1' -> match_states s1 s2 -> exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.


(** Introduction d'une sémantique par bloc sur L1 appelée "memoL1" *)

Definition star_in_block (head current: state L1): Prop :=
  dist_end_block head >= dist_end_block current 
  /\ starN (step L1) (globalenv L1) (minus (dist_end_block head) (dist_end_block current)) head E0 current. 

Lemma star_in_block_step (head previous next: state L1):
  forall t, star_in_block head previous -> Step L1 previous t next -> (dist_end_block previous)<>0 -> star_in_block head next.
Proof.
  intros t [H1 H2] H3 H4.
  destruct (simu_mid_block _ _ _ H3 H4) as [H5 H6]; subst. 
  constructor 1.
  + omega.
  + cutrewrite (dist_end_block head - dist_end_block next = S (dist_end_block head - dist_end_block previous)).
    - eapply starN_last_step; eauto.
    - omega.
Qed.

Lemma star_in_block_init (head current: state L1):
  forall t, Step L1 head t current -> (dist_end_block head)<>0 -> star_in_block head current.
Proof.
  intros t H3 H4.
  destruct (simu_mid_block _ _ _ H3 H4) as [H5 H6]; subst. 
  constructor 1.
  + omega.
  + cutrewrite (dist_end_block head - dist_end_block current = 1).
    - eapply starN_last_step; eauto.
    - omega.
Qed.


Record memostate := {
    real: state L1; 
    memorized: option (state L1);
    memo_star: forall head, memorized = Some head -> star_in_block head real;
    memo_final: forall r, final_state L1 real r -> memorized = None
}.

Definition head (s: memostate): state L1 :=
    match memorized s with
    | None => real s
    | Some s' => s'
    end.

Lemma head_star (s: memostate): star_in_block (head s) (real s).
Proof.
  destruct s as [rs ms Hs]. simpl.
  destruct ms as [ms|]; unfold head; simpl; auto.
  constructor 1.
  omega.
  cutrewrite ((dist_end_block rs - dist_end_block rs)%nat=O).
  + apply starN_refl; auto.
  + omega.
Qed.

Inductive is_well_memorized (s s': memostate): Prop :=
  | StartBloc:
    dist_end_block (real s) <> O  ->
    memorized s = None ->
    memorized s' = Some (real s) ->
    is_well_memorized s s'
  | MidBloc:
    dist_end_block (real s) <> O ->
    memorized s <> None ->
    memorized s' = memorized s ->
    is_well_memorized s s'
  | ExitBloc:
    dist_end_block (real s) = O ->
    memorized s' = None ->
    is_well_memorized s s'.

Local Hint Resolve StartBloc MidBloc ExitBloc.

Definition memoL1 := {| 
  state := memostate;
  genvtype := genvtype L1;
  step := fun ge s t s' => 
    step L1 ge (real s) t (real s') 
    /\ is_well_memorized s s' ;
  initial_state := fun s => initial_state L1 (real s) /\ memorized s = None;
  final_state := fun s r => final_state L1 (real s) r;
  globalenv:= globalenv L1;
  symbolenv:= symbolenv L1
|}.


(** Preuve des 2 forward simulations: L1 -> memoL1  et  memoL1 -> L2 *)

Lemma discr_dist_end s:
  {dist_end_block s = O} + {dist_end_block s <> O}.
Proof.
  destruct (dist_end_block s); simpl; intuition.
Qed.

Lemma memo_simulation_step:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, s1 = (real s2) -> exists s2', Step memoL1 s2 t s2' /\ s1' = (real s2').
Proof.
  intros s1 t s1' H1 [rs2 ms2 Hmoi] H2. simpl in H2; subst.
  destruct (discr_dist_end rs2) as [H3 | H3].
  + refine (ex_intro _ {|real:=s1'; memorized:=None |} _); simpl.
    intuition.
  + destruct ms2 as [s|].
    - refine (ex_intro _ {|real:=s1'; memorized:=Some s |} _); simpl.
      intuition.
    - refine (ex_intro _ {|real:=s1'; memorized:=Some rs2 |} _); simpl.
      intuition.
  Unshelve.
  * intros; discriminate.
  * intros; auto.
  * intros head X; injection X; clear X; intros; subst.
    eapply star_in_block_step; eauto.
  * intros r X; erewrite final_states_end_block in H3; intuition eauto.
  * intros head X; injection X; clear X; intros; subst.
    eapply star_in_block_init; eauto.
  * intros r X; erewrite final_states_end_block in H3; intuition eauto.
Qed.

Lemma forward_memo_simulation_1: forward_simulation L1 memoL1.
Proof.
  apply forward_simulation_step with (match_states:=fun s1 s2 => s1 = (real s2)); auto.
  + intros s1 H; eapply ex_intro with (x:={|real:=s1; memorized:=None |}); simpl.
    intuition.
  + intros; subst; auto.
  + intros; exploit memo_simulation_step; eauto.
  Unshelve.
  * intros; discriminate.
  * auto.
Qed.

Lemma forward_memo_simulation_2: forward_simulation memoL1 L2.
Proof.
  unfold memoL1; simpl.
  apply forward_simulation_opt with (measure:=fun s => dist_end_block (real s)) (match_states:=fun s1 s2 => match_states (head s1) s2); simpl; auto.
  + intros s1 [H0 H1]; destruct (match_initial_states (real s1) H0).
    unfold head; rewrite H1.
    intuition eauto.
  + intros s1 s2 r X H0;  unfold head in X. 
    erewrite memo_final in X; eauto.
  + intros s1 t s1' [H1 H2] s2 H; subst.
    destruct H2 as [ H0 H2 H3 | H0 H2 H3 | H0 H2].
    - (* StartBloc *)
      constructor 2. destruct (simu_mid_block (real s1) t (real s1')) as [H5 H4]; auto.
      unfold head in * |- *. rewrite H2 in H. rewrite H3. rewrite H4. intuition.
    - (* MidBloc *)
      constructor 2. destruct (simu_mid_block (real s1) t (real s1')) as [H5 H4]; auto.
      unfold head in * |- *. rewrite H3. rewrite H4. intuition.
      destruct (memorized s1); simpl; auto. tauto.
    - (* EndBloc *)
      constructor 1.
      destruct (simu_end_block (head s1) t (real s1') s2) as (s2' & H3 & H4); auto.
      * destruct (head_star s1) as [H4 H3].
        cutrewrite (dist_end_block (head s1) - dist_end_block (real s1) = dist_end_block (head s1)) in H3; try omega.
        eapply starN_last_step; eauto.
      * unfold head; rewrite H2; simpl. intuition eauto. 
Qed.

Lemma forward_simulation_block: forward_simulation L1 L2.
Proof.
  eapply compose_forward_simulations.
  eapply forward_memo_simulation_1.
  apply forward_memo_simulation_2.
Qed.


End ForwardSimuBlock.