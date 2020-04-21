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

Section SOUNDNESS.
Variable sp : val.
Variable ctx : eq_context.

Definition sem_rel_b (rel : RB.t) (rs : regset) (m : mem) :=
  match rel with
  | None => False
  | Some rel => sem_rel (ctx:=ctx) (genv:=ge) (sp:=sp) rel rs m
  end.

Lemma forward_move_b_sound :
  forall rel rs m x,
    (sem_rel_b rel rs m) ->
    rs # (forward_move_b (ctx := ctx) rel x) = rs # x.
Proof.
    destruct rel as [rel | ]; simpl; intros.
    2: contradiction.
    eapply forward_move_sound; eauto.
  Qed.

  Lemma forward_move_l_b_sound :
    forall rel rs m x,
      (sem_rel_b rel rs m) ->
      rs ## (forward_move_l_b (ctx := ctx) rel x) = rs ## x.
  Proof.
    destruct rel as [rel | ]; simpl; intros.
    2: contradiction.
    eapply forward_move_l_sound; eauto.
  Qed.

  Definition fmap_sem (fmap : PMap.t RB.t) (pc : node) (rs : regset) (m : mem) :=
    sem_rel_b (PMap.get pc fmap) rs m.
  
  Lemma subst_arg_ok:
    forall invariants,
    forall pc,
    forall rs,
    forall m,
    forall arg,
    forall (SEM : fmap_sem invariants pc rs m),
      rs # (subst_arg (ctx:=ctx) invariants pc arg) = rs # arg.
  Proof.
    intros.
    apply forward_move_b_sound with (m:=m).
    assumption.
  Qed.
  
  Lemma subst_args_ok:
    forall invariants,
    forall pc,
    forall rs,
    forall m,
    forall args,
    forall (SEM : fmap_sem invariants pc rs m),
      rs ## (subst_args (ctx:=ctx) invariants pc args) = rs ## args.
  Proof.
    intros.
    apply forward_move_l_b_sound with (m:=m).
    assumption.
  Qed.
End SOUNDNESS.

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

Lemma stacksize_preserved:
  forall f tf, transf_function f = OK tf -> fn_stacksize tf = fn_stacksize f.
Proof.
  unfold transf_function; destruct f; simpl; intros.
  monadInv H.
  destruct preanalysis as [invariants hints].
  destruct check_inductiveness.
  2: discriminate.
  inv EQ0.
  reflexivity.
Qed.

Lemma params_preserved:
  forall f tf, transf_function f = OK tf -> fn_params tf = fn_params f.
Proof.
  unfold transf_function; destruct f; simpl; intros.
  monadInv H.
  destruct preanalysis as [invariants hints].
  destruct check_inductiveness.
  2: discriminate.
  inv EQ0.
  reflexivity.
Qed.

Lemma entrypoint_preserved:
  forall f tf, transf_function f = OK tf -> fn_entrypoint tf = fn_entrypoint f.
Proof.
  unfold transf_function; destruct f; simpl; intros.
  monadInv H.
  destruct preanalysis as [invariants hints].
  destruct check_inductiveness.
  2: discriminate.
  inv EQ0.
  reflexivity.
Qed.

Lemma sig_preserved2:
  forall f tf, transf_function f = OK tf -> fn_sig tf = fn_sig f.
Proof.
  unfold transf_function; destruct f; simpl; intros.
  monadInv H.
  destruct preanalysis as [invariants hints].
  destruct check_inductiveness.
  2: discriminate.
  inv EQ0.
  reflexivity.
Qed.

Lemma transf_function_is_typable:
  forall f tf, transf_function f = OK tf ->
               exists tenv, type_function f = OK tenv.
Proof.
  unfold transf_function; destruct f; simpl; intros.
  monadInv H.
  exists x.
  assumption.
Qed.
Lemma transf_function_invariants_inductive:
  forall f tf tenv, transf_function f = OK tf ->
    type_function f = OK tenv ->
    check_inductiveness (ctx:=(context_from_hints (snd (preanalysis tenv f))))
                        f tenv (fst (preanalysis tenv f)) = true.
Proof.
  unfold transf_function; destruct f; simpl; intros.
  monadInv H.
  replace x with tenv in * by congruence.
  clear x.
  destruct preanalysis as [invariants hints].
  destruct check_inductiveness; trivial; discriminate.
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
      forall res f sp pc rs s tf ts sg tenv
        (STACKS: match_stackframes s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (WTF: type_function f = OK tenv)
        (WTRS: wt_regset tenv rs)
        (WTRES: tenv res = proj_sig_res sg)
        (REL: forall m vres,
            sem_rel_b sp (context_from_hints (snd (preanalysis tenv f)))
                      ((fst (preanalysis tenv f))#pc) (rs#res <- vres) m),

      match_stackframes
        (Stackframe res f sp pc rs :: s)
        (Stackframe res tf sp pc rs :: ts)
        sg.

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc rs m ts tf tenv
        (STACKS: match_stackframes s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (WTF: type_function f = OK tenv)
        (WTRS: wt_regset tenv rs)
        (REL: sem_rel_b sp (context_from_hints (snd (preanalysis tenv f))) ((fst (preanalysis tenv f))#pc) rs m),
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

Lemma transf_function_at:
  forall f tf pc tenv instr
    (TF : transf_function f = OK tf)
    (TYPE : type_function f = OK tenv)
    (PC : (fn_code f) ! pc = Some instr),
    (fn_code tf) ! pc = Some (transf_instr
       (ctx := (context_from_hints (snd (preanalysis tenv f))))
       (fst (preanalysis tenv f))
       pc instr).
Proof.
  intros.
  unfold transf_function in TF.
  monadInv TF.
  replace x with tenv in * by congruence.
  clear EQ.
  destruct (preanalysis tenv f) as [invariants hints].
  destruct check_inductiveness.
  2: discriminate.
  inv EQ0.
  simpl.
  rewrite PTree.gmap.
  rewrite PC.
  reflexivity.
Qed.

Ltac TR_AT := erewrite transf_function_at by eauto.

Hint Resolve wt_instrs type_function_correct : wt.

Lemma wt_undef :
  forall tenv rs dst,
    wt_regset tenv rs ->
    wt_regset tenv rs # dst <- Vundef.
Proof.
  unfold wt_regset.
  intros.
  destruct (peq r dst).
  { subst dst.
    rewrite Regmap.gss.
    constructor.
  }
  rewrite Regmap.gso by congruence.
  auto.
Qed.

Lemma rel_ge:
  forall inv inv'
         (GE : RELATION.ge inv' inv)
         ctx sp rs m
         (REL: sem_rel (genv:=ge) (sp:=sp) (ctx:=ctx) inv rs m),
  sem_rel (genv:=ge) (sp:=sp) (ctx:=ctx) inv' rs m.
Proof.
  unfold sem_rel, RELATION.ge.
  intros.
  apply (REL i); trivial.
  eapply HashedSet.PSet.is_subset_spec1; eassumption.
Qed.

Hint Resolve rel_ge : cse3.

Lemma sem_rhs_sop :
  forall sp op rs args m v,
  eval_operation ge sp op rs ## args m = Some v ->
  sem_rhs (genv:=ge) (sp:=sp) (SOp op) args rs m v.
Proof.
  intros. simpl.
  rewrite H.
  reflexivity.
Qed.

Hint Resolve sem_rhs_sop : cse3.

Lemma sem_rhs_sload :
  forall sp chunk addr rs args m a v,
  eval_addressing ge sp addr rs ## args = Some a ->
  Mem.loadv chunk m a = Some v ->
  sem_rhs (genv:=ge) (sp:=sp) (SLoad chunk addr) args rs m v.
Proof.
  intros. simpl.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Hint Resolve sem_rhs_sload : cse3.

Lemma sem_rhs_sload_notrap1 :
  forall sp chunk addr rs args m,
  eval_addressing ge sp addr rs ## args = None ->
  sem_rhs (genv:=ge) (sp:=sp) (SLoad chunk addr) args rs m Vundef.
Proof.
  intros. simpl.
  rewrite H.
  reflexivity.
Qed.

Hint Resolve sem_rhs_sload_notrap1 : cse3.

Lemma sem_rhs_sload_notrap2 :
  forall sp chunk addr rs args m a,
  eval_addressing ge sp addr rs ## args = Some a ->
  Mem.loadv chunk m a = None ->
  sem_rhs (genv:=ge) (sp:=sp) (SLoad chunk addr) args rs m Vundef.
Proof.
  intros. simpl.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Hint Resolve sem_rhs_sload_notrap2 : cse3.

Lemma sem_rel_top:
  forall ctx sp rs m, sem_rel (genv:=ge) (sp:=sp) (ctx:=ctx) RELATION.top rs m.
Proof.
  unfold sem_rel, RELATION.top.
  intros.
  rewrite HashedSet.PSet.gempty in *.
  discriminate.
Qed.

Hint Resolve sem_rel_top : cse3.

Lemma sem_rel_b_top:
  forall ctx sp rs m, sem_rel_b sp ctx (Some RELATION.top) rs m.
Proof.
  intros. simpl.
  apply sem_rel_top.
Qed.

Hint Resolve sem_rel_b_top : cse3.

Ltac IND_STEP :=
        match goal with
        REW: (fn_code ?fn) ! ?mpc = Some ?minstr
      |-
        sem_rel_b ?sp (context_from_hints (snd (preanalysis ?tenv ?fn))) ((fst (preanalysis ?tenv ?fn)) # ?mpc') ?rs ?m =>
        assert (is_inductive_allstep (ctx:= (context_from_hints (snd (preanalysis tenv fn)))) fn tenv (fst  (preanalysis tenv fn))) as IND by
        (apply checked_is_inductive_allstep;
          eapply transf_function_invariants_inductive; eassumption);
        unfold is_inductive_allstep, is_inductive_step, apply_instr' in IND;
        specialize IND with (pc:=mpc) (pc':=mpc') (instr:=minstr);
        simpl in IND;
        rewrite REW in IND;
        simpl in IND;
        destruct ((fst (preanalysis tenv fn)) # mpc') as [zinv' | ];
        destruct ((fst (preanalysis tenv fn)) # mpc) as [zinv | ];
        simpl in *;
        intuition;
        eapply rel_ge; eauto with cse3 (* ; for printing
        idtac mpc mpc' fn minstr *)
      end.

Lemma if_same : forall {T : Type} (b : bool) (x : T),
    (if b then x else x) = x.
Proof.
  destruct b; trivial.
Qed.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 -> 
  forall S1', match_states S1 S1' ->
              exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS.
  - (* Inop *)
    exists (State ts tf sp pc' rs m). split.
    + apply exec_Inop; auto.
      TR_AT. reflexivity.
    + econstructor; eauto.
      IND_STEP.
  - (* Iop *)
    exists (State ts tf sp pc' (rs # res <- v) m). split.
    + pose (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iop op args res pc')) as instr'.
      assert (instr' = (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iop op args res pc'))) by reflexivity.
      unfold transf_instr, find_op_in_fmap in instr'.
      destruct (@PMap.get (option RELATION.t) pc) eqn:INV_PC.
      pose proof (rhs_find_sound (sp:=sp) (genv:=ge) (ctx:=(context_from_hints (snd (preanalysis tenv f)))) pc (SOp op)
                (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args) t) as FIND_SOUND.
      * destruct (if is_trivial_op op
               then None
               else
                rhs_find pc (SOp op)
                  (subst_args (fst (preanalysis tenv f)) pc args) t) eqn:FIND.
        ** destruct (is_trivial_op op). discriminate.
           apply exec_Iop with (op := Omove) (args := r :: nil).
           TR_AT.
           subst instr'.
           congruence.
           simpl.
           specialize FIND_SOUND with (src := r) (rs := rs) (m := m).
           simpl in FIND_SOUND.
           rewrite subst_args_ok with (sp:=sp) (m:=m) in FIND_SOUND.
           rewrite H0 in FIND_SOUND.
           rewrite FIND_SOUND; auto.
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
        ** apply exec_Iop with (op := op) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)).
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_operation_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
      * apply exec_Iop with (op := op) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)).
        TR_AT.
        { subst instr'.
          rewrite if_same in H1.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_operation_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
    + econstructor; eauto.
      * eapply wt_exec_Iop with (f:=f); try eassumption.
        eauto with wt.
      * IND_STEP.
        apply oper_sound; eauto with cse3.

  - (* Iload *)
    exists (State ts tf sp pc' (rs # dst <- v) m). split.
    + pose (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iload trap chunk addr args dst pc')) as instr'.
      assert (instr' = (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iload trap chunk addr args dst pc'))) by reflexivity.
      unfold transf_instr, find_load_in_fmap in instr'.
      destruct (@PMap.get (option RELATION.t) pc) eqn:INV_PC.
      pose proof (rhs_find_sound (sp:=sp) (genv:=ge) (ctx:=(context_from_hints (snd (preanalysis tenv f)))) pc (SLoad chunk addr)
                (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args) t) as FIND_SOUND.
      * destruct rhs_find eqn:FIND.
        ** apply exec_Iop with (op := Omove) (args := r :: nil).
           TR_AT.
           subst instr'.
           congruence.
           simpl.
           specialize FIND_SOUND with (src := r) (rs := rs) (m := m).
           simpl in FIND_SOUND.
           rewrite subst_args_ok with (sp:=sp) (m:=m) in FIND_SOUND.
           rewrite H0 in FIND_SOUND. (* ADDR *)
           rewrite H1 in FIND_SOUND. (* LOAD *)
           rewrite FIND_SOUND; auto.
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
        ** apply exec_Iload with (trap := trap) (chunk := chunk) (a := a) (addr := addr) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); trivial.
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_addressing_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
      * apply exec_Iload with (chunk := chunk) (trap := trap) (addr := addr) (a := a) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); trivial.
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_addressing_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
    + econstructor; eauto.
      * eapply wt_exec_Iload with (f:=f); try eassumption.
        eauto with wt.
      * IND_STEP.
        apply oper_sound; eauto with cse3.
        
  - (* Iload notrap1 *)
    exists (State ts tf sp pc' (rs # dst <- Vundef) m). split.
    + pose (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iload NOTRAP chunk addr args dst pc')) as instr'.
      assert (instr' = (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iload NOTRAP chunk addr args dst pc'))) by reflexivity.
      unfold transf_instr, find_load_in_fmap in instr'.
      destruct (@PMap.get (option RELATION.t) pc) eqn:INV_PC.
      pose proof (rhs_find_sound (sp:=sp) (genv:=ge) (ctx:=(context_from_hints (snd (preanalysis tenv f)))) pc (SLoad chunk addr)
                (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args) t) as FIND_SOUND.
      * destruct rhs_find eqn:FIND.
        ** apply exec_Iop with (op := Omove) (args := r :: nil).
           TR_AT.
           subst instr'.
           congruence.
           simpl.
           specialize FIND_SOUND with (src := r) (rs := rs) (m := m).
           simpl in FIND_SOUND.
           rewrite subst_args_ok with (sp:=sp) (m:=m) in FIND_SOUND.
           rewrite H0 in FIND_SOUND. (* ADDR *)
           rewrite FIND_SOUND; auto.
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
        ** apply exec_Iload_notrap1 with (chunk := chunk) (addr := addr) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); trivial.
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_addressing_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
      * apply exec_Iload_notrap1 with (chunk := chunk) (addr := addr) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); trivial.
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_addressing_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
    + econstructor; eauto.
      * apply wt_undef; assumption.
      * IND_STEP.
        apply oper_sound; eauto with cse3.
        
  - (* Iload notrap2 *)
    exists (State ts tf sp pc' (rs # dst <- Vundef) m). split.
    + pose (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iload NOTRAP chunk addr args dst pc')) as instr'.
      assert (instr' = (transf_instr (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc (Iload NOTRAP chunk addr args dst pc'))) by reflexivity.
      unfold transf_instr, find_load_in_fmap in instr'.
      destruct (@PMap.get (option RELATION.t) pc) eqn:INV_PC.
      pose proof (rhs_find_sound (sp:=sp) (genv:=ge) (ctx:=(context_from_hints (snd (preanalysis tenv f)))) pc (SLoad chunk addr)
                (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args) t) as FIND_SOUND.
      * destruct rhs_find eqn:FIND.
        ** apply exec_Iop with (op := Omove) (args := r :: nil).
           TR_AT.
           subst instr'.
           congruence.
           simpl.
           specialize FIND_SOUND with (src := r) (rs := rs) (m := m).
           simpl in FIND_SOUND.
           rewrite subst_args_ok with (sp:=sp) (m:=m) in FIND_SOUND.
           rewrite H0 in FIND_SOUND. (* ADDR *)
           rewrite H1 in FIND_SOUND. (* LOAD *)
           rewrite FIND_SOUND; auto.
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
        ** apply exec_Iload_notrap2 with (chunk := chunk) (a := a) (addr := addr) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); trivial.
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_addressing_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
      * apply exec_Iload_notrap2 with (chunk := chunk) (addr := addr) (a := a) (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); trivial.
           TR_AT.
           { subst instr'.
           congruence. }
           rewrite subst_args_ok with (sp:=sp) (m:=m).
           {
           rewrite eval_addressing_preserved with (ge1:=ge) by exact symbols_preserved.
           assumption.
           }
           unfold fmap_sem.
           change ((fst (preanalysis tenv f)) # pc)
                  with (@PMap.get (option RELATION.t) pc (@fst invariants analysis_hints (preanalysis tenv f))).
           rewrite INV_PC.
           assumption.
    + econstructor; eauto.
      * apply wt_undef; assumption.
      * IND_STEP.
        apply oper_sound; eauto with cse3.

  - (* Istore *)
    exists (State ts tf sp pc' rs m'). split.
    + eapply exec_Istore with (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args))
      (src := (subst_arg (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc src)) ; try eassumption.
      * TR_AT. reflexivity.
      * rewrite subst_args_ok with (sp:=sp) (m:=m) by trivial.
        rewrite eval_addressing_preserved with (ge1 := ge) by exact symbols_preserved.
        eassumption.
      * rewrite subst_arg_ok with (sp:=sp) (m:=m) by trivial.
        assumption.
    + econstructor; eauto.
      IND_STEP.
      apply store_sound with (a0:=a) (m0:=m); eauto with cse3.
      
  - (* Icall *)
    destruct (find_function_translated ros rs fd H0) as [tfd [HTFD1 HTFD2]].
    econstructor. split.
    + eapply exec_Icall; try eassumption.
      * TR_AT. reflexivity.
      * apply sig_preserved; auto.
    + rewrite subst_args_ok with (sp:=sp) (m:=m) by trivial.
      assert (wt_instr f tenv (Icall (funsig fd) ros args res pc')) as WTcall by eauto with wt.
      inv WTcall.
      constructor; trivial.
      * econstructor; eauto.
        ** rewrite sig_preserved with (f:=fd); assumption.
        ** intros.
           IND_STEP.
           apply kill_reg_sound; eauto with cse3.
           eapply kill_mem_sound; eauto with cse3.
      * rewrite sig_preserved with (f:=fd) by trivial.
        rewrite <- H7.
        apply wt_regset_list; auto.
  - (* Itailcall *)
    destruct (find_function_translated ros rs fd H0) as [tfd [HTFD1 HTFD2]].
    econstructor. split.
    + eapply exec_Itailcall; try eassumption.
      * TR_AT. reflexivity.
      * apply sig_preserved; auto.
      * rewrite stacksize_preserved with (f:=f); eauto.
    + rewrite subst_args_ok with (m:=m) (sp := (Vptr stk Ptrofs.zero)) by trivial.
      assert (wt_instr f tenv (Itailcall (funsig fd) ros args)) as WTcall by eauto with wt.
      inv WTcall.
      constructor; trivial.
      * rewrite sig_preserved with (f:=fd) by trivial.
        inv STACKS.
        ** econstructor; eauto.
           rewrite H7.
           rewrite <- sig_preserved2 with (tf:=tf) by trivial.
           assumption.
        ** econstructor; eauto.
           unfold proj_sig_res in *.
           rewrite H7.
           rewrite WTRES.
           rewrite sig_preserved2 with (f:=f) by trivial.
           reflexivity.
      * rewrite sig_preserved with (f:=fd) by trivial.
        rewrite <- H6.
        apply wt_regset_list; auto.
  - (* Ibuiltin *)
    econstructor. split.
    + eapply exec_Ibuiltin; try eassumption.
      * TR_AT. reflexivity.
      * eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
      * eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + econstructor; eauto.
      * eapply wt_exec_Ibuiltin with (f:=f); eauto with wt.
      * IND_STEP.
        apply kill_builtin_res_sound; eauto with cse3.
        eapply external_call_sound; eauto with cse3.
        
  - (* Icond *)
    econstructor. split.
    + eapply exec_Icond with (args := (subst_args (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc args)); try eassumption.
      * TR_AT. reflexivity.
      * rewrite subst_args_ok with (sp:=sp) (m:=m) by trivial.
        eassumption.
      * reflexivity.
    + econstructor; eauto.
      destruct b; IND_STEP.
      
  - (* Ijumptable *)
    econstructor. split.
    + eapply exec_Ijumptable with (arg := (subst_arg (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc arg)); try eassumption.
      * TR_AT. reflexivity.
      * rewrite subst_arg_ok with (sp:=sp) (m:=m) by trivial.
        assumption.
    + econstructor; eauto.
      assert (In pc' tbl) as IN_LIST by (eapply list_nth_z_in; eassumption).
      IND_STEP.

  - (* Ireturn *)
    destruct or as [arg | ].
    -- econstructor. split.
       + eapply exec_Ireturn with (or := Some (subst_arg (ctx:=(context_from_hints (snd (preanalysis tenv f)))) (fst (preanalysis tenv f)) pc arg)).
         * TR_AT. reflexivity.
         * rewrite stacksize_preserved with (f:=f); eauto.
       + simpl.
         rewrite subst_arg_ok with (sp:=(Vptr stk Ptrofs.zero)) (m:=m) by trivial.
         econstructor; eauto.
         apply type_function_correct in WTF.
         apply wt_instrs with (pc:=pc) (instr:=(Ireturn (Some arg))) in WTF.
         2: assumption.
         inv WTF.
         rewrite sig_preserved2 with (f:=f) by assumption.
         rewrite <- H3.
         unfold wt_regset in WTRS.
         apply WTRS.
    -- econstructor. split.
       + eapply exec_Ireturn; try eassumption.
         * TR_AT; reflexivity.
         * rewrite stacksize_preserved with (f:=f); eauto.
       + econstructor; eauto.
         simpl. trivial.
  - (* Callstate internal *)
    monadInv FUN.
    rename x into tf.
    destruct (transf_function_is_typable f tf EQ) as [tenv TENV].
    econstructor; split.
    + apply exec_function_internal.
      rewrite stacksize_preserved with (f:=f); eauto.
    + rewrite params_preserved with (tf:=tf) (f:=f) by assumption.
      rewrite entrypoint_preserved with (tf:=tf) (f:=f) by assumption.
      econstructor; eauto.
      * apply type_function_correct in TENV.
        inv TENV.
        simpl in WTARGS.
        rewrite sig_preserved2 with (f:=f) in WTARGS by assumption.
        apply wt_init_regs.
        rewrite <- wt_params in WTARGS.
        assumption.
      * rewrite @checked_is_inductive_entry with (tenv:=tenv) (ctx:=(context_from_hints (snd (preanalysis tenv f)))).
        ** apply sem_rel_b_top.
        ** apply transf_function_invariants_inductive with (tf:=tf); auto.
           
  - (* external *)
    simpl in FUN.
    inv FUN.
    econstructor. split.
    + eapply exec_function_external.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + econstructor; eauto.
      eapply external_call_well_typed; eauto.
  - (* return *)
    inv STACKS.
    econstructor. split.
    + eapply exec_return.
    + econstructor; eauto.
      apply wt_regset_assign; trivial.
      rewrite WTRES0.
      exact WTRES.
Qed.

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
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - intros. eapply step_simulation; eauto.
Qed.

End PRESERVATION.
