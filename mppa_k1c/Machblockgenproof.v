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

Definition trans_state (ms: Mach.state) : state :=
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


Definition concat (h: list label) (c: code): code :=
  match c with
  | nil =>  {| header := h; body := nil; exit := None |}::nil
  | b::c' => {| header := h ++ (header b); body := body b; exit := exit b |}::c'
  end.

Lemma to_bblock_start_label i c l b c0: 
  (b, c0) = to_bblock (i :: c)
  -> In l (header b)
  -> i <> Mlabel l
  -> exists l2, i=Mlabel l2.
Proof.
   unfold to_bblock.
   remember (to_bblock_header _) as bh; destruct bh as [h c1].
   remember (to_bblock_body _) as bb; destruct bb as [bdy c2].
   remember (to_bblock_exit _) as be; destruct be as [ext c3].
   intros H; inversion H; subst; clear H; simpl.
   destruct i; try (simpl in Heqbh; inversion Heqbh; subst; clear Heqbh; simpl; intuition eauto).
Qed.

Lemma find_label_stop c:
 forall l b c0 c',
   (b, c0) = to_bblock c
 -> Mach.find_label l c = Some c'
 -> In l (header b)
 -> exists h, In l h /\ Some (b :: trans_code c0) = Some (concat h (trans_code c')).
Proof.
  induction c as [ |i c].
  - simpl; intros; discriminate.
  - intros l b c0 c' H H1 H2.
    exploit Mach_find_label_split; eauto; clear H1.
    intros [(X1 & X2) | (X1 & X2)].
    * subst. exploit to_bblock_label; eauto. clear H.
      intros (H3 & H4). constructor 1 with (x:=l::nil); simpl; intuition auto.
      symmetry.
      rewrite trans_code_equation.
      destruct c as [ |i c].
      + unfold to_bblock in H4; simpl in H4.
        injection H4. clear H4; intros H4 H H0 H1; subst. simpl.
        rewrite trans_code_equation; simpl.
        rewrite <- H1 in H3; clear H1.
        destruct b as [h b e]; simpl in * |- *; subst; auto.
      + rewrite H4; clear H4; simpl. rewrite <- H3; clear H3.
        destruct b; simpl; auto.
    * exploit to_bblock_start_label; eauto.
      intros (l' & H'). subst.
      assert (X: l' <> l). { intro Z; subst; destruct X1; auto. }
      clear X1.
      exploit to_bblock_label; eauto. clear H.
      intros (H3 & H4).
      exploit IHc; eauto. { simpl. rewrite H3 in H2; simpl in H2. destruct H2; subst; tauto. }
      intros (h' & H5 & H6).
      constructor 1 with (x:=l'::h'); simpl; intuition auto.
      destruct b as [h b e]; simpl in * |- *; subst.
      remember (tl h) as th. subst h.
      remember (trans_code c') as tcc'.
      rewrite trans_code_equation in Heqtcc'.
      destruct c'; subst; simpl in * |- *. 
      + inversion H6; subst; auto.
      + destruct (to_bblock (i :: c')) as [b1 c1]. simpl in * |- *.
        inversion H6; subst; auto.
Qed.

Lemma to_bblock_header_find_label c l: forall c1 h c',
  to_bblock_header c = (h, c1)
  -> Mach.find_label l c = Some c'
  -> ~ In l h
  -> Mach.find_label l c = Mach.find_label l c1.
Proof.
  induction c as [|i  c]; simpl; auto.
  - intros; discriminate.
  - destruct i;
    try (simpl; intros c1 h c' H1 H2; inversion H1; subst; clear H1; intros; apply refl_equal).
    remember (to_bblock_header c) as tbhc. destruct tbhc as [h2 c2].
    intros h c1 c' H1; inversion H1; subst; clear H1.
    simpl. destruct (peq _ _).
    + subst; tauto.
    + intros H1 H2; erewrite IHc; eauto.
Qed.

Lemma to_bblock_body_find_label c1 l: forall c2 bdy,
  (bdy, c2) = to_bblock_body c1 ->
  Mach.find_label l c1 = Mach.find_label l c2.
Proof.
  induction c1 as [|i c1].
  - intros bdy0 c0 H. simpl in H. inversion H; subst; clear H. auto.
  - intros bdy' c2' H. simpl in H. destruct i; try (
      simpl in H; remember (to_bblock_body c1) as tbb; destruct tbb as [p c''];
      inversion H; subst; clear H; simpl; erewrite IHc1; eauto; fail).
Qed.

Lemma to_bblock_exit_find_label c1 l c2 ext:
 (ext, c2) = to_bblock_exit c1
 -> Mach.find_label l c1 = Mach.find_label l c2.
Proof.
  intros H. destruct c1 as [|i c1].
  - simpl in H. inversion H; subst; clear H. auto.
  - destruct i; try (
      simpl in H; inversion H; subst; clear H; auto; fail).
Qed.

Lemma find_label_transcode_preserved:
  forall l c c',
  Mach.find_label l c = Some c' ->
  exists h, In l h /\ find_label l (trans_code c) = Some (concat h (trans_code c')).
Proof.
  intros l c; induction c, (trans_code c) using trans_code_ind.
  - intros c' H; inversion H.
  - intros c' H. subst _x. destruct c as [| i c]; try tauto.
   unfold to_bblock in * |-.
   remember (to_bblock_header _) as bh; destruct bh as [h c1].
   remember (to_bblock_body _) as bb; destruct bb as [bdy c2].
   remember (to_bblock_exit _) as be; destruct be as [ext c3].
   simpl; injection e0; intros; subst; clear e0.
   unfold is_label; simpl; destruct (in_dec l h) as [Y|Y].
   + clear IHc0.
     eapply find_label_stop; eauto.
     unfold to_bblock.
     rewrite <- Heqbh, <- Heqbb, <- Heqbe. 
     auto.
   + exploit IHc0; eauto. clear IHc0.
     rewrite <- H.
     erewrite (to_bblock_header_find_label (i::c) l c1); eauto.
     erewrite (to_bblock_body_find_label c1 l c2); eauto.
     erewrite (to_bblock_exit_find_label c2 l c0); eauto.
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

Definition dist_end_block_code (c: Mach.code) := (size (fst (to_bblock c))-1)%nat.


Definition dist_end_block (s: Mach.state): nat :=
  match s with
  | Mach.State _ _ _ c _ _ => dist_end_block_code c
  | _ => 0
  end.

Local Hint Resolve exec_nil_body exec_cons_body.
Local Hint Resolve exec_MBgetstack exec_MBsetstack exec_MBgetparam exec_MBop exec_MBload exec_MBstore.

Ltac ExploitDistEndBlockCode :=
  match goal with
  | [ H : dist_end_block_code (Mlabel ?l :: ?c) <> 0%nat |- _ ] =>
      exploit (to_bblock_size_single_label c (Mlabel l)); eauto
  | [ H : dist_end_block_code (?i0 :: ?c) <> 0%nat |- _ ] =>
      exploit (to_bblock_size_single_basic c i0); eauto
  | _ => idtac
  end.

Ltac totologize H :=
  match type of H with
  | ( ?id = _ ) =>
    let Hassert := fresh "Htoto" in (
    assert (id = id) as Hassert; auto; rewrite H in Hassert at 2; simpl in Hassert; rewrite H in Hassert)
  end.

Lemma dist_end_block_code_simu_mid_block i c:
  dist_end_block_code (i::c) <> 0 ->
  (dist_end_block_code (i::c) = Datatypes.S (dist_end_block_code c)).
Proof.
  intros H.
  unfold dist_end_block_code.
  destruct (get_code_nature (i::c)) eqn:GCNIC.
  - apply get_code_nature_empty in GCNIC. discriminate.
  - rewrite to_bblock_size_single_label; auto.
    destruct c as [|i' c].
    + contradict H. destruct i; simpl; auto.
    + assert (size (fst (to_bblock (i'::c))) <> 0). apply to_bblock_nonil. omega. 
  - destruct (get_code_nature c) eqn:GCNC.
    + apply get_code_nature_empty in GCNC. subst. contradict H. destruct i; simpl; auto.
    + contradict H. destruct c as [|i' c]; try discriminate.
      destruct i'; try discriminate.
      destruct i; try discriminate. all: simpl; auto.
    + destruct (to_basic_inst i) eqn:TBI; [| destruct i; discriminate].
      erewrite to_bblock_basic; eauto; [| rewrite GCNC; discriminate ].
      simpl. destruct c as [|i' c]; try discriminate.
      assert (size (fst (to_bblock (i'::c))) <> 0). apply to_bblock_nonil.
      cutrewrite (Datatypes.S (size (fst (to_bblock (i'::c))) - 1) = size (fst (to_bblock (i'::c)))).
      unfold size. cutrewrite (length (header (fst (to_bblock (i' :: c)))) = 0). simpl. omega.
      rewrite to_bblock_noLabel. simpl; auto.
      rewrite GCNC. discriminate.
      omega.
    + destruct (to_basic_inst i) eqn:TBI; [| destruct i; discriminate].
      erewrite to_bblock_basic; eauto; [| rewrite GCNC; discriminate ].
      simpl. destruct c as [|i' c]; try discriminate.
      assert (size (fst (to_bblock (i'::c))) <> 0). apply to_bblock_nonil.
      cutrewrite (Datatypes.S (size (fst (to_bblock (i'::c))) - 1) = size (fst (to_bblock (i'::c)))).
      unfold size. cutrewrite (length (header (fst (to_bblock (i' :: c)))) = 0). simpl. omega.
      rewrite to_bblock_noLabel. simpl; auto.
      rewrite GCNC. discriminate.
      omega.
  - contradict H. destruct i; try discriminate.
    all: unfold dist_end_block_code; erewrite to_bblock_CFI; eauto; simpl; eauto.
Qed.

Local Hint Resolve dist_end_block_code_simu_mid_block.

Lemma step_simu_basic_step (i: Mach.instruction) (bi: basic_inst) (c: Mach.code) s f sp rs m (t:trace) (s':Mach.state):
  to_basic_inst i = Some bi ->
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


Lemma star_step_simu_body_step s f sp c:
 forall (p:bblock_body) c' rs m t s',
  to_bblock_body c = (p, c') ->
  starN (Mach.step (inv_trans_rao rao)) ge (length p) (Mach.State s f sp c rs m) t s' ->
  exists rs' m', s'=Mach.State s f sp c' rs' m' /\ t=E0 /\ body_step tge (trans_stack s) f sp p rs m rs' m'.
Proof.
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

Local Hint Resolve exec_MBcall exec_MBtailcall exec_MBbuiltin exec_MBgoto exec_MBcond_true exec_MBcond_false exec_MBjumptable exec_MBreturn exec_Some_exit exec_None_exit.
Local Hint Resolve eval_builtin_args_preserved external_call_symbols_preserved find_funct_ptr_same.

Lemma match_states_concat_trans_code st f sp c rs m h: 
  match_states (Mach.State st f sp c rs m) (State (trans_stack st) f sp (concat h (trans_code c)) rs m).
Proof.
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



Lemma step_simu_exit_step c e c' stk f sp rs m t s' b:
  to_bblock_exit c = (e, c') ->
  starN (Mach.step (inv_trans_rao rao)) (Genv.globalenv prog) (length_opt e) (Mach.State stk f sp c rs m) t s' ->
  exists s2, exit_step rao tge e (State (trans_stack stk) f sp (b::trans_code c') rs m) t s2 /\ match_states s' s2.
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

Lemma step_simu_header st f sp rs m s c: forall h c' t, 
 (h, c') = to_bblock_header c ->
 starN (Mach.step (inv_trans_rao rao)) (Genv.globalenv prog) (length h) (Mach.State st f sp c rs m) t s -> s = Mach.State st f sp c' rs m /\ t = E0.
Proof.
   induction c as [ | i c]; simpl; intros h c' t H.
   - inversion_clear H. simpl; intros H; inversion H; auto.
   - destruct i; try (injection H; clear H; intros H H2; subst; simpl; intros H; inversion H; subst; auto).
     remember (to_bblock_header c) as bhc. destruct bhc as [h0 c0].
     injection H; clear H; intros H H2; subst; simpl; intros H; inversion H; subst.
     inversion H1; clear H1; subst; auto. autorewrite with trace_rewrite.
     exploit IHc; eauto.
Qed. 

Lemma simu_end_block:
  forall s1 t s1',
  starN (Mach.step (inv_trans_rao rao)) ge (Datatypes.S (dist_end_block s1)) s1 t s1' ->
  exists s2', step rao tge (trans_state s1) t s2' /\ match_states s1' s2'.
Proof.
  destruct s1; simpl.
  + (* State *)
    (* c cannot be nil *)
    destruct c as [|i c]; simpl; try ( (* nil => absurd *)
      unfold dist_end_block_code; simpl;
      intros t s1' H; inversion_clear H;
      inversion_clear H0; fail
    ).

    intros t s1' H.
    remember (_::_) as c0. remember (trans_code c0) as tc0.

    (* tc0 cannot be nil *)
    destruct tc0; try
    ( exploit (trans_code_nonil c0); subst; auto; try discriminate; intro H0; contradict H0 ).

    assert (X: Datatypes.S (dist_end_block_code c0) = (size (fst (to_bblock c0)))).
    {
      unfold dist_end_block_code. remember (size _) as siz.
      assert (siz <> 0%nat). rewrite Heqsiz; subst; apply to_bblock_nonil with (c0 := c) (i := i); auto.
      omega.
    }

    (* decomposition of starN in 3 parts: header + body + exit *)
    rewrite X in H; unfold size in H.
    destruct (starN_split (Mach.semantics (inv_trans_rao rao) prog) _ _ _ _ H _ _ refl_equal) as [t3 [t4 [s1 [H0 [H3 H4]]]]].
    subst t; clear X H.
    destruct (starN_split (Mach.semantics (inv_trans_rao rao) prog) _ _ _ _ H0 _ _ refl_equal) as [t1 [t2 [s0 [H [H1 H2]]]]].
    subst t3; clear H0.

    unfold to_bblock in * |- *.
    (* naming parts of block "b" *)
    remember (to_bblock_header c0) as hd. destruct hd as [hb c1].
    remember (to_bblock_body c1) as bb. destruct bb as [bb c2].
    remember (to_bblock_exit c2) as exb. destruct exb as [exb c3].
    simpl in * |- *.

    exploit trans_code_step; eauto. intro EQ. destruct EQ as (EQH & EQB & EQE & EQTB0).
    subst hb bb exb.

    (* header opt step *)
    exploit step_simu_header; eauto.
    intros [X1 X2]; subst s0 t1.
    autorewrite with trace_rewrite.
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
  - intros s1 t s1' H1.
    destruct H1; simpl; omega || (intuition auto).
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
  - intros. simpl in H0. inversion H0.
    inversion H; simpl; auto.
    (* the remaining instructions cannot lead to a Returnstate *)
    all: subst; discriminate.
(* simu_end_block *)
  - apply simu_end_block.
Qed.

End PRESERVATION.
