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

(* FIXME: put this section somewhere else. 
   In "Smallstep" ? 

TODO: also move "starN_last_step" in the same section ?

*)

Section starN_lemma.
(* Auxiliary Lemma on starN *)

Import Smallstep.
Local Open Scope nat_scope.


Variable L: semantics.

Local Hint Resolve starN_refl starN_step Eapp_assoc.

Lemma starN_split n s t s': 
  starN (step L) (globalenv L) n s t s' ->
  forall m k, n=m+k -> 
  exists (t1 t2:trace) s0, starN (step L) (globalenv L) m s t1 s0 /\ starN (step L) (globalenv L) k s0 t2 s' /\ t=t1**t2.
Proof.
  induction 1; simpl.
  + intros m k H; assert (X: m=0); try omega.
    assert (X0: k=0); try omega.
    subst; repeat (eapply ex_intro); intuition eauto.
  + intros m; destruct m as [| m']; simpl. 
    - intros k H2; subst; repeat (eapply ex_intro); intuition eauto.
    - intros k H2. inversion H2.
      exploit (IHstarN m' k); eauto. intro.
      destruct H3 as (t5 & t6 & s0 & H5 & H6 & H7).
      repeat (eapply ex_intro).
      instantiate (1 := t6); instantiate (1 := t1 ** t5); instantiate (1 := s0).
      intuition eauto. subst. auto.
Qed.

End starN_lemma.


Definition inv_trans_rao (rao: function -> code -> ptrofs -> Prop) (f: Mach.function) (c: Mach.code) :=
  rao (trans_function f) (trans_code c).

Definition match_prog (p: Mach.program) (tp: Machblock.program) :=
  match_program (fun _ f tf => tf = trans_fundef f) eq p tp.

Lemma trans_program_match: forall p, match_prog p (trans_prog p).
Proof.
  intros. eapply match_transform_program; eauto.
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

Variable prog: Mach.program.
Variable tprog: Machblock.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

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
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ trans_fundef f = tf.
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
  Genv.find_funct_ptr tge f = Some (Internal (trans_function f0)).
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

Lemma find_label_stop l b c c0:
 to_bblock (Mlabel l :: c) = (b, c0) -> find_label l (b :: trans_code c0) = Some (trans_code c).
Proof.
  intros H.
  unfold find_label.
  assert (X: b=(fst (to_bblock (Mlabel l :: c)))).
  { rewrite H; simpl; auto. }
  subst b; rewrite to_bblock_islabel.
  remember ({| header := None; body := _ ; exit := _ |}) as b'.
  remember (fst (to_bblock _)) as b.
  destruct (size b') eqn:SIZE.
  - destruct (size_null b') as (Hh & Hb & He); auto.
    subst b'; simpl in *. clear Hh SIZE.
    erewrite <- (to_bblock_label_then_nil b l c c0); eauto.
  - assert (X: exists b0 lb0, trans_code c = b0::lb0 /\ c <> nil).
    { induction c, (trans_code c) using trans_code_ind.
      + subst. simpl in * |-. inversion SIZE.
      + (repeat econstructor 1).  intro; subst; try tauto.
    }
    destruct X as (b0 & lb0 & X0 & X1).
    unfold to_bblock in * |-.
    remember (to_bblock_header _) as bh; destruct bh as [h c1].
    remember (to_bblock_body _) as bb; destruct bb as [bdy c2].
    remember (to_bblock_exit _) as be; destruct be as [ext c3].
    unfold size in SIZE; subst b b'; simpl in * |-.
    injection H; clear H; intro; subst c3.
    injection Heqbh; clear Heqbh; intros; subst.
    cut (to_bblock_header c = (None, c)).
    * intros X2; exploit trans_code_step; eauto.
      simpl; rewrite X0; clear X0.
      intros (Y1 & Y2 & Y3 & Y4). subst.
      rewrite Y1; clear X1; destruct b0; simpl; auto.
    * destruct (cn_eqdec (get_code_nature c) IsLabel) as [ Y | Y ].
      + destruct c; simpl; try discriminate.
        destruct i; simpl; try discriminate.
        simpl in * |-.
        inversion Heqbb; subst. simpl in * |-.
        inversion Heqbe; subst; simpl in * |-.
        discriminate.
      + destruct c; simpl; discriminate || auto.
        destruct i; simpl; auto.
        destruct Y. simpl; auto.
Qed.

Lemma find_label_next l i b c c':
 to_bblock (i :: c) = (b, c') -> i <> Mlabel l -> find_label l (b :: trans_code c') = find_label l (trans_code c').
Proof.
  intros H H1.
  destruct b as [hd bd ex].
  destruct (cn_eqdec (get_code_nature (i::c)) IsLabel) as [ X | X ].
  - destruct i; try discriminate.
    exploit to_bblock_label; eauto.
    intros (bdy & c1 & Y1 & Y2 & Y3 & Y4).
    simpl in *|-. subst. clear X.
    simpl. unfold is_label; simpl.
    assert (l0 <> l); [ intro; subst; contradict H1; auto |].
    rewrite peq_false; auto.
  - exploit to_bblock_no_label; eauto.
    intro Y. apply (f_equal fst) in H as Y1. simpl in Y1. rewrite Y in Y1. clear Y.
    inversion Y1; subst; clear Y1.
    simpl. auto.
Qed.

Lemma to_bblock_header_split i c h c1:
  to_bblock_header (i::c)=(h, c1)
  -> (exists l, i=Mlabel l /\ h=Some l /\ c1=c) \/ (forall l, i<>Mlabel l /\ h=None /\ c1=(i::c)).
Proof.
  destruct i; simpl; intros H; inversion H; try (constructor 2; intuition auto; discriminate).
  constructor 1; eapply ex_intro; intuition eauto.
Qed.

Lemma to_bblock_header_find_label i c1 l c h:
  i <> Mlabel l
  -> to_bblock_header (i :: c) = (h, c1) -> Mach.find_label l c = Mach.find_label l c1.
Proof.
  intros H1 H2; exploit to_bblock_header_split; eauto.
  intros [ ( l0 & X1 & X2 & X3 ) | X ].
  - subst. auto.
  - destruct (X l) as (X1 & X2 & X3). subst. clear X X1.
    symmetry. destruct i; try (simpl; auto).
    assert (l0 <> l); [ intro; subst; contradict H1; auto |].
    rewrite peq_false; auto.
Qed. 

Lemma to_bblock_body_find_label c2 bdy l c1:
  (bdy, c2) = to_bblock_body c1 ->
  Mach.find_label l c1 = Mach.find_label l c2.
Proof.
  generalize bdy c2.
  induction c1 as [|i c1].
  - intros bdy0 c0 H. simpl in H. inversion H; subst; clear H. auto.
  - intros bdy' c2' H. simpl in H. destruct i; try (
      simpl in H; remember (to_bblock_body c1) as tbb; destruct tbb as [p c''];
      inversion H; subst; clear H; simpl; erewrite IHc1; eauto; fail).
Qed.

Lemma to_bblock_exit_find_label c2 ext l c1:
 (ext, c2) = to_bblock_exit c1
 -> Mach.find_label l c1 = Mach.find_label l c2.
Proof.
  intros H. destruct c1 as [|i c1].
  - simpl in H. inversion H; subst; clear H. auto.
  - destruct i; try (
      simpl in H; inversion H; subst; clear H; auto; fail).
Qed.

Lemma Mach_find_label_to_bblock i c l b c0:
 i <> Mlabel l
 -> to_bblock (i :: c) = (b, c0)
 -> Mach.find_label l c = Mach.find_label l c0.
Proof.
  intro H.
  unfold to_bblock.
  remember (to_bblock_header _) as bh; destruct bh as [h c1].
  remember (to_bblock_body _) as bb; destruct bb as [bdy c2].
  remember (to_bblock_exit _) as be; destruct be as [ext c3].
  intros X; injection X. clear X; intros; subst.
  erewrite (to_bblock_header_find_label i c1); eauto.
  erewrite (to_bblock_body_find_label c2); eauto.
  erewrite to_bblock_exit_find_label; eauto.
Qed.

Local Hint Resolve find_label_next.

Lemma find_label_transcode_preserved:
  forall l c c',
  Mach.find_label l c = Some c' ->
  find_label l (trans_code c) = Some (trans_code c').
Proof.
  intros l c; induction c, (trans_code c) using trans_code_ind.
  - intros c' H; inversion H.
  - intros c' H. subst _x. destruct c as [| i c]; try tauto.
    exploit Mach_find_label_split; eauto. clear H.
    intros [  [H1 H2] | [H1 H2] ].
    + subst. erewrite find_label_stop; eauto.
    + rewrite <- IHc0. eauto.
      erewrite <- (Mach_find_label_to_bblock i c); eauto.
Qed.

Lemma find_label_preserved:
  forall l f c,
  Mach.find_label l (Mach.fn_code f) = Some c ->
  find_label l (fn_code (trans_function f)) = Some (trans_code c).
Proof.
  intros. cutrewrite ((fn_code (trans_function f)) = trans_code (Mach.fn_code f)); eauto.
  apply find_label_transcode_preserved; auto.
Qed.

Lemma mem_free_preserved:
  forall m stk f,
  Mem.free m stk 0 (Mach.fn_stacksize f) = Mem.free m stk 0 (fn_stacksize (trans_function f)).
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

Variable rao: function -> code -> ptrofs -> Prop.

(*
Lemma minus_diff_0 n: (n-1<>0)%nat -> (n >= 2)%nat.
Proof.
  omega.
Qed.
*)

Ltac ExploitDistEndBlockCode :=
  match goal with
  | [ H : dist_end_block_code (Mlabel ?l :: ?c) <> 0%nat |- _ ] =>
      exploit (to_bblock_size_single_label c (Mlabel l)); eauto
  | [ H : dist_end_block_code (?i0 :: ?c) <> 0%nat |- _ ] =>
      exploit (to_bblock_size_single_basicinst c i0); eauto
  | _ => idtac
  end.

(* FIXME - refactoriser avec get_code_nature pour que ce soit plus joli *)
Lemma dist_end_block_code_simu_mid_block i c:
  dist_end_block_code (i::c) <> 0%nat ->
  (dist_end_block_code (i::c) = Datatypes.S (dist_end_block_code c))%nat.
Proof.
  intros.
  remember (get_code_nature c) as gcnc; destruct gcnc.
  (* when c is nil *)
  - contradict H. rewrite get_code_nature_nil_contra with (c := c); auto. destruct i; simpl; auto.
  (* when c is IsLabel *)
  - remember i as i0; remember (to_basic_inst i) as sbi; remember (to_cfi i) as scfi;
    remember (get_code_nature (i::c)) as gcnic;
    destruct i.
    (* when i is a basic instruction *)
    1-6: try (( contradict H; unfold dist_end_block_code; exploit to_bblock_basic_inst_then_label; eauto;
       [ totologize Heqgcnic; eapply Htoto
       | totologize Heqsbi; try eapply Htoto
       | intro; subst; rewrite H; simpl; auto
       ] ); fail).
    (* when i is a control flow instruction *)
    1-8: try (( contradict H; unfold dist_end_block_code; exploit to_bblock_cf_inst_then_label; eauto;
       [ totologize Heqgcnic; eapply Htoto
       | totologize Heqscfi; try eapply Htoto
       | intro; subst; rewrite H; simpl; auto
       ] ); fail).
    (* when i is a label *)
    contradict H. unfold dist_end_block_code. exploit to_bblock_double_label; eauto.
    intro. subst. rewrite H. simpl. auto.
  (* when c is IsBasicInst or IsCFI *)
  - destruct i; try (contradict H; auto; fail); (* getting rid of the non basic inst *)
       ( ExploitDistEndBlockCode; [ rewrite <- Heqgcnc; discriminate |
         unfold dist_end_block_code in *; intro; rewrite H0 in *; omega ] ).
  - destruct i; try (contradict H; auto; fail); (* getting rid of the non basic inst *)
       ( ExploitDistEndBlockCode; [ rewrite <- Heqgcnc; discriminate |
         unfold dist_end_block_code in *; intro; rewrite H0 in *; omega ] ).
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

Lemma step_simu_cfi_step:
  forall c e c' stk f sp rs m t s' b lb',
  to_bblock_exit c = (Some e, c') ->
  trans_code c' = lb' ->
  Mach.step (inv_trans_rao rao) ge (Mach.State stk f sp c rs m) t s' ->
  cfi_step rao tge e (State (trans_stack stk) f sp (b::lb') rs m) t (trans_state s').
Proof.
  intros c e c' stk f sp rs m t s' b lb'.
  intros Hexit Htc Hstep.
  destruct c as [|ei c]; try (contradict Hexit; discriminate).
  destruct ei; (contradict Hexit; discriminate) || (
    inversion Hexit; subst; inversion Hstep; subst; simpl
  ).
  * unfold inv_trans_rao in H11.
    apply exec_MBcall with (f := (trans_function f0)); auto.
    rewrite find_function_ptr_same in H9; auto.
    apply find_funct_ptr_same. auto.
  * apply exec_MBtailcall with (f := (trans_function f0)); auto.
    rewrite find_function_ptr_same in H9; auto.
    apply find_funct_ptr_same; auto.
    rewrite parent_sp_preserved in H11; subst; auto.
    rewrite parent_ra_preserved in H12; subst; auto.
  * eapply exec_MBbuiltin; eauto.
    eapply eval_builtin_args_preserved; eauto.
    eapply external_call_symbols_preserved; eauto.
  * eapply exec_MBgoto; eauto.
    apply find_funct_ptr_same; eauto.
    apply find_label_preserved; auto.
  * eapply exec_MBcond_true; eauto.
    erewrite find_funct_ptr_same; eauto.
    apply find_label_preserved; auto.
  * eapply exec_MBcond_false; eauto.
  * eapply exec_MBjumptable; eauto.
    erewrite find_funct_ptr_same; eauto.
    apply find_label_preserved; auto.
  * eapply exec_MBreturn; eauto.
    apply find_funct_ptr_same; eauto.
    rewrite parent_sp_preserved in H8; subst; auto.
    rewrite parent_ra_preserved in H9; subst; auto.
    rewrite mem_free_preserved in H10; subst; auto.
Qed.

Lemma simu_end_block:
  forall s1 t s1',
  starN (Mach.step (inv_trans_rao rao)) ge (Datatypes.S (dist_end_block s1)) s1 t s1' ->
  step rao tge (trans_state s1) t (trans_state s1').
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
      assert (siz <> 0%nat). rewrite Heqsiz; apply to_bblock_nonil with (c0 := c) (i := i) (c := c0); auto.
      omega.
    }

    (* decomposition of starN in 3 parts: header + body + exit *)
    rewrite X in H; unfold size in H.
    destruct (starN_split (Mach.semantics (inv_trans_rao rao) prog) _ _ _ _ H _ _ refl_equal) as [t3 [t4 [s1 [H0 [H3 H4]]]]].
    subst t; clear X H.
    destruct (starN_split (Mach.semantics (inv_trans_rao rao) prog) _ _ _ _ H0 _ _ refl_equal) as [t1 [t2 [s0 [H [H1 H2]]]]].
    subst t3; clear H0.

    (* Making the hypothesis more readable *)
    remember (Smallstep.step _) as Machstep. remember (globalenv _) as mge.
    remember (Mach.State _ _ _ _ _ _) as si.

    unfold to_bblock in * |- *.
    (* naming parts of block "b" *)
    remember (to_bblock_header c0) as hd. destruct hd as [hb c1].
    remember (to_bblock_body c1) as bb. destruct bb as [bb c2].
    remember (to_bblock_exit c2) as exb. destruct exb as [exb c3].
    simpl in * |- *.

    exploit trans_code_step; eauto. intro EQ. destruct EQ as (EQH & EQB & EQE & EQTB0).
    subst hb bb exb.

    (* header opt step *)
    assert (X: s0 = (Mach.State stack f sp c1 rs m) /\ t1 = E0).
    {
      destruct (header b) eqn:EQHB.
      - inversion_clear H. inversion H2. subst.
        destruct i; try (contradict EQHB; inversion Heqhd; fail).
        inversion H0. subst. inversion Heqhd. auto.
      - simpl in H. inversion H. subst.
        destruct i; try (inversion Heqhd; auto; fail).
    }
    clear H; destruct X as [X1 X2]; subst s0 t1.
    autorewrite with trace_rewrite.

    (* body steps *)
    subst mge Machstep.
    exploit (star_step_simu_body_step); eauto.
    clear H1; intros [rs' [m' [H0 [H1 H2]]]].
    subst s1 t2. autorewrite with trace_rewrite.
    (* preparing exit step *)
    eapply exec_bblock; eauto.
    clear H2.

    (* exit step *)
    destruct (exit b) as [e|] eqn:EQEB.
    - constructor.
      simpl in H3. inversion H3. subst. clear H3.
      inversion H1. subst. clear H1.
      destruct c2 as [|ei c2']; try (contradict Heqexb; discriminate).
      rewrite E0_right.
      destruct ei; try (contradict Heqexb; discriminate).
      all: eapply step_simu_cfi_step; eauto.
    - simpl in H3. inversion H3; subst. simpl.
      destruct c2 as [|ei c2']; inversion Heqexb; subst; try eapply exec_None_exit.
      clear H3. destruct (to_cfi ei) as [cfi|] eqn:TOCFI; inversion H0.
      subst. eapply exec_None_exit. 

  + (* Callstate *)
    intros t s1' H; inversion_clear H.
    inversion H1; subst; clear H1.
    inversion_clear H0; simpl.
    - (* function_internal*)
      cutrewrite (trans_code (Mach.fn_code f0) = fn_code (trans_function f0)); eauto.
      eapply exec_function_internal; eauto.
      apply find_funct_ptr_same; auto.
      rewrite <- parent_sp_preserved; eauto.
      rewrite <- parent_ra_preserved; eauto.
    - (* function_external *)
      autorewrite with trace_rewrite.
      eapply exec_function_external; eauto.
      apply find_funct_ptr_same_external; auto.
      rewrite <- parent_sp_preserved; eauto.
      apply external_call_preserved; auto.
  +  (* Returnstate *)
    intros t s1' H; inversion_clear H.
    inversion H1; subst; clear H1.
    inversion_clear H0; simpl.
    eapply exec_return.
Qed.

Theorem simulation: forward_simulation (Mach.semantics (inv_trans_rao rao) prog) (Machblock.semantics rao tprog).
Proof.
  apply forward_simulation_block with (dist_end_block := dist_end_block) (build_block := trans_state).
(* simu_mid_block *)
  - intros s1 t s1' H1.
    destruct H1; simpl; omega || (intuition auto).
(* public_preserved *)
  - apply senv_preserved.
(* match_initial_states *)
  - intros. simpl. destruct H. split.
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
