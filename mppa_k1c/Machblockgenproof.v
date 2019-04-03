Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.
Require Import Mach.
Require Import Linking.
Require Import Machblock.
Require Import Machblockgen.
Require Import ForwardSimulationBlock.

Definition inv_trans_rao (rao: function -> code -> ptrofs -> Prop) (f: Mach.function) (c: Mach.code) :=
  rao (transf_function f) (trans_code c).

Definition match_prog (p: Mach.program) (tp: Machblock.program) :=
  match_program (fun _ f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match: forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. rewrite <- H. eapply match_transform_program; eauto.
Qed.

Definition trans_stackframe (msf: Mach.stackframe) : stackframe :=
  match msf with
  | Mach.Stackframe f sp retaddr c => Stackframe f sp retaddr (trans_code c)
  end.

Fixpoint trans_stack (mst: list Mach.stackframe) : list stackframe :=
  match mst with
  | nil => nil
  | msf :: mst0 => (trans_stackframe msf) :: (trans_stack mst0)
  end.

Definition trans_state (ms: Mach.state): state :=
  match ms with
  | Mach.State        s f sp c rs m => State        (trans_stack s) f sp (trans_code c) rs m
  | Mach.Callstate    s f rs m      => Callstate    (trans_stack s) f rs m
  | Mach.Returnstate  s rs m        => Returnstate  (trans_stack s) rs m
  end.

Section PRESERVATION.

Local Open Scope nat_scope.

Variable prog: Mach.program.
Variable tprog: Machblock.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Variable rao: function -> code -> ptrofs -> Prop.

Definition match_states: Mach.state -> state -> Prop 
  := ForwardSimulationBlock.match_states (Mach.semantics (inv_trans_rao rao) prog) (Machblock.semantics rao tprog) trans_state.

Lemma match_states_trans_state s1: match_states s1 (trans_state s1).
Proof.
  apply match_states_trans_state.
Qed.

Local Hint Resolve match_states_trans_state.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma init_mem_preserved:
  forall m,
  Genv.init_mem prog = Some m ->
  Genv.init_mem tprog = Some m.
Proof (Genv.init_mem_transf TRANSF).

Lemma prog_main_preserved:
  prog_main tprog = prog_main prog.
Proof (match_program_main TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = tf.
Proof.
  intros.
  exploit (Genv.find_funct_ptr_match TRANSF); eauto. intro.
  destruct H0 as (cunit & tf & A & B & C).
  eapply ex_intro. intuition; eauto. subst. eapply A.
Qed.

Lemma find_function_ptr_same:
  forall s rs,
  Mach.find_function_ptr ge s rs = find_function_ptr tge s rs.
Proof.
  intros. unfold Mach.find_function_ptr. unfold find_function_ptr.
  destruct s; auto.
  rewrite symbols_preserved; auto.
Qed.

Lemma find_funct_ptr_same:
  forall f f0,
  Genv.find_funct_ptr ge f = Some (Internal f0) ->
  Genv.find_funct_ptr tge f = Some (Internal (transf_function f0)).
Proof.
  intros. exploit (Genv.find_funct_ptr_transf TRANSF); eauto.
Qed.

Lemma find_funct_ptr_same_external:
  forall f f0,
  Genv.find_funct_ptr ge f = Some (External f0) ->
  Genv.find_funct_ptr tge f = Some (External f0).
Proof.
  intros. exploit (Genv.find_funct_ptr_transf TRANSF); eauto.
Qed.

Lemma parent_sp_preserved:
  forall s,
  Mach.parent_sp s = parent_sp (trans_stack s).
Proof.
  unfold parent_sp. unfold Mach.parent_sp. destruct s; simpl; auto.
  unfold trans_stackframe. destruct s; simpl; auto.
Qed.

Lemma parent_ra_preserved:
  forall s,
  Mach.parent_ra s = parent_ra (trans_stack s).
Proof.
  unfold parent_ra. unfold Mach.parent_ra. destruct s; simpl; auto.
  unfold trans_stackframe. destruct s; simpl; auto.
Qed.

Lemma external_call_preserved:
  forall ef args m t res m',
  external_call ef ge args m t res m' ->
  external_call ef tge args m t res m'.
Proof.
  intros. eapply external_call_symbols_preserved; eauto.
  apply senv_preserved.
Qed.

Lemma Mach_find_label_split l i c c':
  Mach.find_label l (i :: c) = Some c' ->
   (i=Mlabel l /\ c' = c) \/ (i <> Mlabel l /\ Mach.find_label l c = Some c').
Proof.
  intros H.
  destruct i; try (constructor 2; split; auto; discriminate ).
  destruct (peq l0 l) as [P|P].
  - constructor. subst l0; split; auto.
    revert H. unfold Mach.find_label. simpl. rewrite peq_true.
    intros H; injection H; auto.
  - constructor 2. split.
    + intro F. injection F. intros. contradict P; auto.
    + revert H. unfold Mach.find_label. simpl. rewrite peq_false; auto.
Qed.

Lemma find_label_is_end_block_not_label i l c bl:
      is_end_block (trans_inst i) bl ->
      is_trans_code c bl ->
      i <> Mlabel l -> find_label l (add_to_new_bblock (trans_inst i) :: bl) = find_label l bl.  
Proof.
  intros H H0 H1.
  unfold find_label.
  remember (is_label l _) as b.
  cutrewrite (b = false); auto.
  subst; unfold is_label.
  destruct i; simpl in * |- *; try (destruct (in_dec l nil); intuition).
  inversion H.
  destruct (in_dec l (l0::nil)) as [H6|H6]; auto.
  simpl in H6; intuition try congruence.
Qed.

Lemma find_label_at_begin l bh bl:
  In l (header bh)
  -> find_label l (bh :: bl) = Some (bh::bl).
Proof.
  unfold find_label; rewrite is_label_correct_true; intro H; rewrite H; simpl; auto.
Qed.

Lemma find_label_add_label_diff l bh bl:
      ~(In l (header bh)) -> 
      find_label l (bh::bl) = find_label l bl.
Proof.
  unfold find_label; rewrite is_label_correct_false; intro H; rewrite H; simpl; auto.
Qed.

Definition concat (h: list label) (c: code): code :=
  match c with
  | nil =>  empty_bblock::nil
  | b::c' => {| header := h ++ (header b); body := body b; exit := exit b |}::c'
  end.

Ltac subst_is_trans_code H :=
  rewrite is_trans_code_inv in H;
  rewrite <- H in * |- *;
  rewrite <- is_trans_code_inv in H.

Lemma find_label_transcode_preserved:
  forall l c c',
  Mach.find_label l c = Some c' ->
  exists h, In l h /\ find_label l (trans_code c) = Some (concat h (trans_code c')).
Proof.
  intros l c. remember (trans_code _) as bl.
  rewrite <- is_trans_code_inv in * |-.
  induction Heqbl. 
  + (* Tr_nil *) 
    intros; exists (l::nil); simpl in * |- *; intuition.
    discriminate.
  + (* Tr_end_block *)
    intros.
    exploit Mach_find_label_split; eauto.
    clear H0; destruct 1 as [(H0&H2)|(H0&H2)].
    - subst. rewrite find_label_at_begin; simpl; auto.
      inversion H as [mbi H1 H2| | ].
      subst.
      inversion Heqbl.
      subst.
      exists (l :: nil); simpl; eauto.
    - exploit IHHeqbl; eauto.
      destruct 1 as (h & H3 & H4).
      exists h.
      split; auto.
      erewrite find_label_is_end_block_not_label;eauto.
  + (* Tr_add_label *)
    intros.
    exploit Mach_find_label_split; eauto.
    clear H0; destruct 1 as [(H0&H2)|(H0&H2)].
    - subst.
      inversion H0 as [H1].
      clear H0.
      erewrite find_label_at_begin; simpl; eauto.
      subst_is_trans_code Heqbl.
      exists (l :: nil); simpl; eauto.
    - subst; assert (H: l0 <> l); try congruence; clear H0.
      exploit IHHeqbl; eauto.
      clear IHHeqbl Heqbl.
      intros (h & H3 & H4).
      simpl; unfold is_label, add_label; simpl.
      destruct (in_dec l (l0::header bh)) as [H5|H5]; simpl in H5.
      * destruct H5; try congruence.
        exists (l0::h); simpl; intuition.
        rewrite find_label_at_begin in H4; auto.
        apply f_equal. inversion H4 as [H5]. clear H4.
        destruct (trans_code c'); simpl in * |- *;
        inversion H5; subst; simpl; auto.
      * exists h. intuition.
        erewrite <- find_label_add_label_diff; eauto.
  + (* Tr_add_basic *)
    intros.
    exploit Mach_find_label_split; eauto.
    destruct 1 as [(H2&H3)|(H2&H3)].
    rewrite H2 in H. unfold trans_inst in H. congruence.
    exploit IHHeqbl; eauto.
    clear IHHeqbl Heqbl.
    intros (h & H4 & H5).
    rewrite find_label_add_label_diff; auto.
    rewrite find_label_add_label_diff in H5; eauto.
    rewrite H0; auto.
Qed.

Lemma find_label_preserved:
  forall l f c,
  Mach.find_label l (Mach.fn_code f) = Some c ->
  exists h, In l h /\ find_label l (fn_code (transf_function f)) = Some (concat h (trans_code c)).
Proof.
  intros. cutrewrite ((fn_code (transf_function f)) = trans_code (Mach.fn_code f)); eauto.
  apply find_label_transcode_preserved; auto.
Qed.

Lemma mem_free_preserved:
  forall m stk f,
  Mem.free m stk 0 (Mach.fn_stacksize f) = Mem.free m stk 0 (fn_stacksize (transf_function f)).
Proof.
  intros. auto.
Qed.

Local Hint Resolve symbols_preserved senv_preserved init_mem_preserved prog_main_preserved functions_translated
                   parent_sp_preserved.


Definition dist_end_block_code (c: Mach.code) := 
 match trans_code c with
 | nil => 0
 | bh::_ => (size bh-1)%nat
 end.

Definition dist_end_block (s: Mach.state): nat :=
  match s with
  | Mach.State _ _ _ c _ _ => dist_end_block_code c
  | _ => 0
  end.

Local Hint Resolve exec_nil_body exec_cons_body.
Local Hint Resolve exec_MBgetstack exec_MBsetstack exec_MBgetparam exec_MBop exec_MBload exec_MBstore.

Lemma size_add_label l bh: size (add_label l bh) = size bh + 1.
Proof.
  unfold add_label, size; simpl; omega.
Qed.

Lemma size_add_to_newblock i: size (add_to_new_bblock i) = 1.
Proof.
  destruct i; auto.
Qed.

Lemma dist_end_block_code_simu_mid_block i c:
  dist_end_block_code (i::c) <> 0 ->
  (dist_end_block_code (i::c) = Datatypes.S (dist_end_block_code c)).
Proof.
  unfold dist_end_block_code.
  remember (trans_code (i::c)) as bl.
  rewrite <- is_trans_code_inv in Heqbl.
  inversion Heqbl as [|bl0 H| |]; subst; clear Heqbl.
  - rewrite size_add_to_newblock; omega.
  - rewrite size_add_label;
    subst_is_trans_code H.
    omega.
Admitted. (* A FINIR *)


Lemma size_nonzero c b bl:
  is_trans_code c (b :: bl) -> size b <> 0.
Proof.
   intros H; inversion H; subst.
Admitted. (* A FINIR *)

Axiom TODO: False. (* a éliminer *)

Local Hint Resolve dist_end_block_code_simu_mid_block.

Lemma step_simu_basic_step (i: Mach.instruction) (bi: basic_inst) (c: Mach.code) s f sp rs m (t:trace) (s':Mach.state):
  trans_inst i = MB_basic bi ->
  Mach.step (inv_trans_rao rao) ge (Mach.State s f sp (i::c) rs m) t s' ->
  exists rs' m', s'=Mach.State s f sp c rs' m' /\ t=E0 /\ basic_step tge (trans_stack s) f sp rs m bi rs' m'.
Proof.
  destruct i; simpl in * |-;
   (discriminate
    || (intro H; inversion_clear H; intro X; inversion_clear X; eapply ex_intro; eapply ex_intro; intuition eauto)).
  - eapply exec_MBgetparam; eauto. exploit (functions_translated); eauto. intro.
    destruct H3 as (tf & A & B). subst. eapply A.
    all: simpl; rewrite <- parent_sp_preserved; auto.
  - eapply exec_MBop; eauto. rewrite <- H. destruct o; simpl; auto. destruct (rs ## l); simpl; auto.
    unfold Genv.symbol_address; rewrite symbols_preserved; auto.
  - eapply exec_MBload; eauto; rewrite <- H; destruct a; simpl; auto; destruct (rs ## l); simpl; auto;
    unfold Genv.symbol_address; rewrite symbols_preserved; auto.
  - eapply exec_MBstore; eauto; rewrite <- H; destruct a; simpl; auto; destruct (rs ## l); simpl; auto;
    unfold Genv.symbol_address; rewrite symbols_preserved; auto.
Qed.

Inductive is_first_bblock b c blc: Prop :=
  | Tr_dummy_nil: b = empty_bblock -> c=nil -> blc = nil -> is_first_bblock b c blc
  | Tr_trans_code: is_trans_code c (b::blc) -> is_first_bblock b c blc
  .

Lemma star_step_simu_body_step s f sp c bl:
  is_trans_code c bl -> forall b blc rs m t s',
  bl=b::blc ->
  (header b)=nil ->
  starN (Mach.step (inv_trans_rao rao)) ge (length (body b)) (Mach.State s f sp c rs m) t s' ->
  exists c' rs' m', s'=Mach.State s f sp c' rs' m' /\ t=E0 /\ body_step tge (trans_stack s) f sp (body b) rs m rs' m' /\ is_first_bblock {| header := nil; body:=nil; exit := exit b |} c' blc.
Proof.
  induction 1; intros b blc rs m t s' X; inversion X; subst; clear X.
Admitted. (* A FINIR *)

(* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
  induction c as [ | i0 c0 Hc0]; simpl; intros p c' rs m t s' H.
  * (* nil *)
    inversion_clear H; simpl; intros X; inversion_clear X.
    eapply ex_intro; eapply ex_intro; intuition eauto.
  * (* cons *)
    remember (to_basic_inst i0) as o eqn:Ho.
    destruct o as [bi |].
    + (* to_basic_inst i0 = Some bi *)
      remember (to_bblock_body c0) as r eqn:Hr.
      destruct r as [p1 c1]; inversion H; simpl; subst; clear H.
      intros X; inversion_clear X.
      exploit step_simu_basic_step; eauto.
      intros [rs' [m' [H2 [H3 H4]]]]; subst.
      exploit Hc0; eauto.
      intros [rs'' [m'' [H5 [H6 H7]]]]; subst.
      refine (ex_intro _ rs'' (ex_intro _ m'' _)); intuition eauto.
   + (* to_basic_inst i0 = None *)
     inversion_clear H; simpl.
     intros X; inversion_clear X. intuition eauto.
Qed.
*)

Local Hint Resolve exec_MBcall exec_MBtailcall exec_MBbuiltin exec_MBgoto exec_MBcond_true exec_MBcond_false exec_MBjumptable exec_MBreturn exec_Some_exit exec_None_exit.
Local Hint Resolve eval_builtin_args_preserved external_call_symbols_preserved find_funct_ptr_same.

Lemma match_states_concat_trans_code st f sp c rs m h: 
  match_states (Mach.State st f sp c rs m) (State (trans_stack st) f sp (concat h (trans_code c)) rs m).
Proof.
  intros; remember (trans_code _) as bl.
  rewrite <- is_trans_code_inv in * |-.
  constructor 1; simpl.
  + intros (t0 & s1' & H0) t s'. 
    inversion Heqbl as [| | |]; subst; simpl;  (* inversion vs induction ?? *)
    elim TODO. (* A FAIRE *)
  + intros H r; constructor 1; intro X; inversion X.
Qed.
(* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
  constructor 1; simpl.
  + intros (t0 & s1' & H0) t s'. 
    rewrite! trans_code_equation.
    destruct c as [| i c]. { inversion H0. }
    remember (to_bblock (i :: c)) as bic. destruct bic as [b c0].
    simpl.
    constructor 1; intros H; inversion H; subst; simpl in * |- *;
    eapply exec_bblock; eauto.
    - inversion H11; subst; eauto.
      inversion H2; subst; eauto.
    - inversion H11; subst; simpl; eauto.
      inversion H2; subst; simpl; eauto.
  + intros H r; constructor 1; intro X; inversion X.
Qed.
*)

(* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
Lemma step_simu_cfi_step:
  forall c e c' stk f sp rs m t s' b lb',
  to_bblock_exit c = (Some e, c') ->
  trans_code c' = lb' ->
  Mach.step (inv_trans_rao rao) ge (Mach.State stk f sp c rs m) t s' ->
  exists s2, cfi_step rao tge e (State (trans_stack stk) f sp (b::lb') rs m) t s2 /\ match_states s' s2.
Proof.
  intros c e c' stk f sp rs m t s' b lb'.
  intros Hexit Htc Hstep.
  destruct c as [|ei c]; try (contradict Hexit; discriminate).
  destruct ei; (contradict Hexit; discriminate) || (
    inversion Hexit; subst; inversion Hstep; subst; simpl
  ).
  * eapply ex_intro; constructor 1; [ idtac | eapply match_states_trans_state ]; eauto.
    apply exec_MBcall with (f := (transf_function f0)); auto.
    rewrite find_function_ptr_same in H9; auto.
  * eapply ex_intro; constructor 1; [ idtac | eapply match_states_trans_state ]; eauto.
    apply exec_MBtailcall with (f := (transf_function f0)); auto.
    rewrite find_function_ptr_same in H9; auto.
    rewrite parent_sp_preserved in H11; subst; auto.
    rewrite parent_ra_preserved in H12; subst; auto.
  * eapply ex_intro; constructor 1; [ idtac | eapply match_states_trans_state ]; eauto.
    eapply exec_MBbuiltin; eauto.
  * exploit find_label_transcode_preserved; eauto. intros (h & X1 & X2).
    eapply ex_intro; constructor 1; [ idtac | eapply match_states_concat_trans_code ]; eauto.
  * exploit find_label_transcode_preserved; eauto. intros (h & X1 & X2).
    eapply ex_intro; constructor 1; [ idtac | eapply match_states_concat_trans_code ]; eauto.
  * eapply ex_intro; constructor 1; [ idtac | eapply match_states_trans_state ]; eauto.
    eapply exec_MBcond_false; eauto.
  * exploit find_label_transcode_preserved; eauto. intros (h & X1 & X2).
    eapply ex_intro; constructor 1; [ idtac | eapply match_states_concat_trans_code ]; eauto.
  * eapply ex_intro; constructor 1; [ idtac | eapply match_states_trans_state ]; eauto.
    eapply exec_MBreturn; eauto.
    rewrite parent_sp_preserved in H8; subst; auto.
    rewrite parent_ra_preserved in H9; subst; auto.
Qed.
*)

Lemma step_simu_exit_step c stk f sp rs m t s1 b blc b':
  is_trans_code c (b::blc) ->
  (header b)=nil ->
  (body b)=nil ->
  starN (Mach.step (inv_trans_rao rao)) (Genv.globalenv prog) (length_opt (exit b)) (Mach.State stk f sp c rs m) t s1 ->
  exists c' s2, exit_step rao tge (exit b) (State (trans_stack stk) f sp (b'::blc) rs m) t s2 /\ match_states s1 s2 /\ is_trans_code c' blc.
Proof.
  inversion_clear 1. (* A FINIR *)
Admitted.
(* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
Proof.
  intros H1 H2; destruct e as [ e |]; inversion_clear H2. 
  + (* Some *) inversion H0; clear H0; subst. autorewrite with trace_rewrite.
    exploit step_simu_cfi_step; eauto.
    intros (s2' & H2 & H3); eapply ex_intro; intuition eauto.
  + (* None *) 
     destruct c as [ |i c]; simpl in H1; inversion H1.
     - eapply ex_intro; intuition eauto; try eapply match_states_trans_state.
     - remember to_cfi as o. destruct o; try discriminate.
       inversion_clear H1.
       eapply ex_intro; intuition eauto; try eapply match_states_trans_state.
Qed.
*)

Lemma step_simu_header st f sp rs m s c bl: 
 is_trans_code c bl -> forall b blc t, bl=b::blc ->
 starN (Mach.step (inv_trans_rao rao)) (Genv.globalenv prog) (length (header b)) (Mach.State st f sp c rs m) t s -> 
 exists c', s = Mach.State st f sp c' rs m /\ t = E0 /\ is_first_bblock {| header := nil; body:=body b; exit := exit b |} c' blc.
Proof.
  induction 1; intros b blc t X; inversion X; subst; clear X.
Admitted.

(* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
   induction c as [ | i c]; simpl; intros h c' t H.
   - inversion_clear H. simpl; intros H; inversion H; auto.
   - destruct i; try (injection H; clear H; intros H H2; subst; simpl; intros H; inversion H; subst; auto).
     remember (to_bblock_header c) as bhc. destruct bhc as [h0 c0].
     injection H; clear H; intros H H2; subst; simpl; intros H; inversion H; subst.
     inversion H1; clear H1; subst; auto. autorewrite with trace_rewrite.
     exploit IHc; eauto.
Qed.
*)

Lemma simu_end_block:
  forall s1 t s1',
  starN (Mach.step (inv_trans_rao rao)) ge (Datatypes.S (dist_end_block s1)) s1 t s1' ->
  exists s2', step rao tge (trans_state s1) t s2' /\ match_states s1' s2'.
Proof.
  destruct s1; simpl.
  + (* State *)
    remember (trans_code _) as tc.
    rewrite <- is_trans_code_inv in Heqtc.
    intros t s1 H.
    destruct tc as [|b bl].
    { (* nil => absurd *) 
      inversion Heqtc. subst. 
      unfold dist_end_block_code; simpl.
      inversion_clear H;
      inversion_clear H0. 
    }
    assert (X: Datatypes.S (dist_end_block_code c) = (size b)).
    {
      unfold dist_end_block_code. 
      subst_is_trans_code Heqtc.
      lapply (size_nonzero c b bl); auto.
      omega.
    }
    rewrite X in H; unfold size in H.
    destruct b as [bh bb be]; simpl in * |- *.
    (* decomposition of starN in 3 parts: header + body + exit *)
    destruct (starN_split (Mach.semantics (inv_trans_rao rao) prog) _ _ _ _ H _ _ refl_equal) as [t3 [t4 [s1' [H0 [H3 H4]]]]].
    subst t; clear X H.
    destruct (starN_split (Mach.semantics (inv_trans_rao rao) prog) _ _ _ _ H0 _ _ refl_equal) as [t1 [t2 [s1'' [H [H1 H2]]]]].
    subst t3; clear H0.
    (* header steps *)
    exploit step_simu_header; eauto.
    clear c Heqtc H; simpl; intros (c & X1 & X2 & X3); subst.
    destruct X3 as [H|Heqtc]. 
    { subst. inversion H. subst. simpl in * |-.
      inversion H1. subst.
      inversion H3. subst.
      autorewrite with trace_rewrite.
      eapply ex_intro; intuition eauto.
      eapply exec_bblock; simpl; eauto.
    }
    autorewrite with trace_rewrite.
    (* body steps *)
    exploit (star_step_simu_body_step); eauto.
    clear H1; simpl; intros (rs' & m' & X1 & X2 & X3 & X4 & X5); subst.
    elim TODO. (* A FAIRE *) 
   (* VIELLE PREUVE -- UTILE POUR S'INSPIRER !!!

    (* header steps *)
    exploit step_simu_header; eauto.
    intros [X1 X2]; subst s0 t1.
    (* body steps *)
    exploit (star_step_simu_body_step); eauto.
    clear H1; intros [rs' [m' [H0 [H1 H2]]]].
    subst s1 t2. autorewrite with trace_rewrite.
    (* exit step *)
    subst tc0.
    exploit step_simu_exit_step; eauto. clear H3.
    intros (s2' & H3 & H4).
    eapply ex_intro; intuition eauto.
    eapply exec_bblock; eauto.
*)
  + (* Callstate *)
    intros t s1' H; inversion_clear H.
    eapply ex_intro; constructor 1; eauto.
    inversion H1; subst; clear H1.
    inversion_clear H0; simpl.
    - (* function_internal*)
      cutrewrite (trans_code (Mach.fn_code f0) = fn_code (transf_function f0)); eauto.
      eapply exec_function_internal; eauto.
      rewrite <- parent_sp_preserved; eauto.
      rewrite <- parent_ra_preserved; eauto.
    - (* function_external *)
      autorewrite with trace_rewrite.
      eapply exec_function_external; eauto.
      apply find_funct_ptr_same_external; auto.
      rewrite <- parent_sp_preserved; eauto.
  +  (* Returnstate *)
    intros t s1' H; inversion_clear H.
    eapply ex_intro; constructor 1; eauto.
    inversion H1; subst; clear H1.
    inversion_clear H0; simpl.
    eapply exec_return.
Qed.

Theorem transf_program_correct: 
    forward_simulation (Mach.semantics (inv_trans_rao rao) prog) (Machblock.semantics rao tprog).
Proof.
  apply forward_simulation_block_trans with (dist_end_block := dist_end_block) (trans_state := trans_state).
(* simu_mid_block *)
  - intros s1 t s1' H1. elim TODO. (* A FAIRE *)
    (* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
    destruct H1; simpl; omega || (intuition auto).
    *)
(* public_preserved *)
  - apply senv_preserved.
(* match_initial_states *)
  - intros. simpl.
    eapply ex_intro; constructor 1.
    eapply match_states_trans_state.
    destruct H. split.
    apply init_mem_preserved; auto.
    rewrite prog_main_preserved. rewrite <- H0. apply symbols_preserved.
(* match_final_states *)
  - intros. simpl. destruct H. split with (r := r); auto.
(* final_states_end_block *)
  - intros. simpl in H0. elim TODO.
  (* VIELLE PREUVE -- UTILE POUR S'INSPIRER ??? 
    inversion H0.
    inversion H; simpl; auto. 
    (* the remaining instructions cannot lead to a Returnstate *)
    all: subst; discriminate.
  *)
(* simu_end_block *)
  - apply simu_end_block.
Qed.

End PRESERVATION.
