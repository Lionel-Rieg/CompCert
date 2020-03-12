
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE3analysis CSE2deps CSE2depsproof HashedSet.
Require Import RTLtyping.
Require Import Lia.

Theorem loadv_storev_really_same:
  forall chunk: memory_chunk,
  forall m1: mem,
  forall addr v: val,
  forall m2: mem,
  forall ty : typ,
  forall TYPE: Val.has_type v ty,
  forall STORE: Mem.storev chunk m1 addr v = Some m2,
  forall COMPATIBLE: loadv_storev_compatible_type chunk ty = true,
    Mem.loadv chunk m2 addr = Some v.
Proof.
  intros.
  rewrite Mem.loadv_storev_same with (m1:=m1) (v:=v) by assumption.
  f_equal.
  destruct chunk; destruct ty; try discriminate.
  all: destruct v; trivial; try contradiction.
  all: unfold Val.load_result, Val.has_type in *.
  all: destruct Archi.ptr64; trivial; discriminate.
Qed.

Lemma subst_args_notin :
  forall (rs : regset) dst v args,
    ~ In dst args ->
    (rs # dst <- v) ## args = rs ## args.
Proof.
  induction args; simpl; trivial.
  intro NOTIN.
  destruct (peq a dst).
  {
    subst a.
    intuition congruence.
  }
  rewrite Regmap.gso by congruence.
  f_equal.
  apply IHargs.
  intuition congruence.
Qed.

Lemma add_i_j_adds : forall i j m,
    PSet.contains (Regmap.get i (add_i_j i j m)) j = true.
Proof.
  intros.
  unfold add_i_j.
  rewrite Regmap.gss.
  auto with pset.
Qed.
Hint Resolve add_i_j_adds: cse3.

Lemma add_i_j_monotone : forall i j i' j' m,
    PSet.contains (Regmap.get i' m) j' = true ->
    PSet.contains (Regmap.get i' (add_i_j i j m)) j' = true.
Proof.
  intros.
  unfold add_i_j.
  destruct (peq i i').
  - subst i'.
    rewrite Regmap.gss.
    destruct (peq j j').
    + subst j'.
      apply PSet.gadds.
    + eauto with pset.
  - rewrite Regmap.gso.
    assumption.
    congruence.
Qed.

Hint Resolve add_i_j_monotone: cse3.

Lemma add_ilist_j_monotone : forall ilist j i' j' m,
    PSet.contains (Regmap.get i' m) j' = true ->
    PSet.contains (Regmap.get i' (add_ilist_j ilist j m)) j' = true.
Proof.
  induction ilist; simpl; intros until m; intro CONTAINS; auto with cse3.
Qed.
Hint Resolve add_ilist_j_monotone: cse3.

Lemma add_ilist_j_adds : forall ilist j m,
    forall i, In i ilist ->
              PSet.contains (Regmap.get i (add_ilist_j ilist j m)) j = true.
Proof.
  induction ilist; simpl; intros until i; intro IN.
  contradiction.
  destruct IN as [HEAD | TAIL]; subst; auto with cse3.
Qed.
Hint Resolve add_ilist_j_adds: cse3.

Definition xlget_kills (eqs : list (eq_id * equation)) (m :  Regmap.t PSet.t) :
  Regmap.t PSet.t :=
  List.fold_left (fun already (item : eq_id * equation) =>
    add_i_j (eq_lhs (snd item)) (fst item)
            (add_ilist_j (eq_args (snd item)) (fst item) already)) eqs m. 

Lemma xlget_kills_monotone :
  forall eqs m i j,
    PSet.contains (Regmap.get i m) j = true ->
    PSet.contains (Regmap.get i (xlget_kills eqs m)) j = true.
Proof.
  induction eqs; simpl; trivial.
  intros.
  auto with cse3.
Qed.

Hint Resolve xlget_kills_monotone : cse3.

Lemma xlget_kills_has_lhs :
  forall eqs m lhs sop args j,
    In (j, {| eq_lhs := lhs;
              eq_op  := sop;
              eq_args:= args |}) eqs ->
    PSet.contains (Regmap.get lhs (xlget_kills eqs m)) j = true.
Proof.
  induction eqs; simpl.
  contradiction.
  intros until j.
  intro HEAD_TAIL.
  destruct HEAD_TAIL as [HEAD | TAIL]; subst; simpl.
  - auto with cse3.
  - eapply IHeqs. eassumption.
Qed.
Hint Resolve xlget_kills_has_lhs : cse3.

Lemma xlget_kills_has_arg :
  forall eqs m lhs sop arg args j,
    In (j, {| eq_lhs := lhs;
              eq_op  := sop;
              eq_args:= args |}) eqs ->
    In arg args ->
    PSet.contains (Regmap.get arg (xlget_kills eqs m)) j = true.
Proof.
  induction eqs; simpl.
  contradiction.
  intros until j.
  intros HEAD_TAIL ARG.
  destruct HEAD_TAIL as [HEAD | TAIL]; subst; simpl.
  - auto with cse3.
  - eapply IHeqs; eassumption.
Qed.

Hint Resolve xlget_kills_has_arg : cse3.

Lemma get_kills_has_lhs :
  forall eqs lhs sop args j,
    PTree.get j eqs = Some {| eq_lhs := lhs;
                              eq_op  := sop;
                              eq_args:= args |} ->
    PSet.contains (Regmap.get lhs (get_reg_kills eqs)) j = true.
Proof.
  unfold get_reg_kills.
  intros.
  rewrite PTree.fold_spec.
  change (fold_left
       (fun (a : Regmap.t PSet.t) (p : positive * equation) =>
        add_i_j (eq_lhs (snd p)) (fst p)
          (add_ilist_j (eq_args (snd p)) (fst p) a))) with xlget_kills.
  eapply xlget_kills_has_lhs.
  apply PTree.elements_correct.
  eassumption.
Qed.

Lemma get_kills_has_arg :
  forall eqs lhs sop arg args j,
    PTree.get j eqs = Some {| eq_lhs := lhs;
                              eq_op  := sop;
                              eq_args:= args |} ->
    In arg args ->
    PSet.contains (Regmap.get arg (get_reg_kills eqs)) j = true.
Proof.
  unfold get_reg_kills.
  intros.
  rewrite PTree.fold_spec.
  change (fold_left
       (fun (a : Regmap.t PSet.t) (p : positive * equation) =>
        add_i_j (eq_lhs (snd p)) (fst p)
          (add_ilist_j (eq_args (snd p)) (fst p) a))) with xlget_kills.
  eapply xlget_kills_has_arg.
  - apply PTree.elements_correct.
    eassumption.
  - assumption.
Qed.

Hint Resolve get_kills_has_arg : cse3.

Definition eq_involves (eq : equation) (i : reg) :=
  i = (eq_lhs eq) \/ In i (eq_args eq).

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

  Context {ctx : eq_context}.

  Definition sem_rhs (sop : sym_op) (args : list reg)
             (rs : regset) (m : mem) (v' : val) :=
    match sop with
    | SOp op =>
      match eval_operation genv sp op (rs ## args) m with
      | Some v => v' = v
      | None => False
      end
    | SLoad chunk addr =>
      match
        match eval_addressing genv sp addr (rs ## args) with
        | Some a => Mem.loadv chunk m a
        | None => None
        end
      with
      | Some dat => v' = dat
      | None => v' = default_notrap_load_value chunk
      end
    end.
    
  Definition sem_eq (eq : equation) (rs : regset) (m : mem) :=
    sem_rhs (eq_op eq) (eq_args eq) rs m (rs # (eq_lhs eq)).

  Definition sem_rel (rel : RELATION.t) (rs : regset) (m : mem) :=
    forall i eq,
      PSet.contains rel i = true ->
      eq_catalog ctx i = Some eq ->
      sem_eq eq rs m.

  Hypothesis ctx_kill_reg_has_lhs :
    forall lhs sop args j,
      eq_catalog ctx j = Some {| eq_lhs := lhs;
                                 eq_op  := sop;
                                 eq_args:= args |} ->
      PSet.contains (eq_kill_reg ctx lhs) j = true.

  Hypothesis ctx_kill_reg_has_arg :
    forall lhs sop args j,
      eq_catalog ctx j = Some {| eq_lhs := lhs;
                                 eq_op  := sop;
                                 eq_args:= args |} ->
      forall arg,
      In arg args ->
      PSet.contains (eq_kill_reg ctx arg) j = true.

  Hypothesis ctx_kill_mem_has_depends_on_mem :
    forall lhs op args j,
      eq_catalog ctx j = Some {| eq_lhs := lhs;
                                 eq_op  := SOp op;
                                 eq_args:= args |} ->
      op_depends_on_memory op = true ->
      PSet.contains (eq_kill_mem ctx tt) j = true.

  Hypothesis ctx_kill_mem_has_load :
    forall lhs chunk addr args j,
      eq_catalog ctx j = Some {| eq_lhs := lhs;
                                 eq_op  := SLoad chunk addr;
                                 eq_args:= args |} ->
      PSet.contains (eq_kill_mem ctx tt) j = true.

  Theorem kill_reg_sound :
    forall rel rs m dst v,
      (sem_rel rel rs m) ->
      (sem_rel (kill_reg (ctx:=ctx) dst rel) (rs#dst <- v) m).
  Proof.
    unfold sem_rel, sem_eq, sem_rhs, kill_reg.
    intros until v.
    intros REL i eq.
    specialize REL with (i := i) (eq0 := eq).
    destruct eq as [lhs sop args]; simpl.
    specialize ctx_kill_reg_has_lhs with (lhs := lhs) (sop := sop) (args := args) (j := i).
    specialize ctx_kill_reg_has_arg with (lhs := lhs) (sop := sop) (args := args) (j := i) (arg := dst).
    intuition.
    rewrite PSet.gsubtract in H.
    rewrite andb_true_iff in H.
    rewrite negb_true_iff in H.
    intuition.
    simpl in *.
    assert ({In dst args} + {~In dst args}) as IN_ARGS.
    {
      apply List.in_dec.
      apply peq.
    }
    destruct IN_ARGS as [IN_ARGS | NOTIN_ARGS].
    { intuition.
      congruence.
    }
    destruct (peq dst lhs).
    {
      congruence.
    }
    rewrite subst_args_notin by assumption.
    destruct sop.
    - destruct (eval_operation genv sp o rs ## args m) as [ev | ]; trivial.
      rewrite Regmap.gso by congruence.
      assumption.
    - rewrite Regmap.gso by congruence.
      assumption.
  Qed.

  Hint Resolve kill_reg_sound : cse3.

  Theorem kill_reg_sound2 :
    forall rel rs m dst,
      (sem_rel rel rs m) ->
      (sem_rel (kill_reg (ctx:=ctx) dst rel) rs m).
  Proof.
    unfold sem_rel, sem_eq, sem_rhs, kill_reg.
    intros until dst.
    intros REL i eq.
    specialize REL with (i := i) (eq0 := eq).
    destruct eq as [lhs sop args]; simpl.
    specialize ctx_kill_reg_has_lhs with (lhs := lhs) (sop := sop) (args := args) (j := i).
    specialize ctx_kill_reg_has_arg with (lhs := lhs) (sop := sop) (args := args) (j := i) (arg := dst).
    intuition.
    rewrite PSet.gsubtract in H.
    rewrite andb_true_iff in H.
    rewrite negb_true_iff in H.
    intuition.
  Qed.
    
  Lemma pick_source_sound :
    forall (l : list reg),
      match pick_source l with
      | Some x => In x l
      | None => True
      end.
  Proof.
    unfold pick_source.
    destruct l; simpl; trivial.
    left; trivial.
  Qed.
    
  Hint Resolve pick_source_sound : cse3.

  Theorem forward_move_sound :
    forall rel rs m x,
      (sem_rel rel rs m) ->
      rs # (forward_move (ctx := ctx) rel x) = rs # x.
  Proof.
    unfold sem_rel, forward_move.
    intros until x.
    intro REL.
    pose proof (pick_source_sound (PSet.elements (PSet.inter rel (eq_moves ctx x)))) as ELEMENT.
    destruct (pick_source (PSet.elements (PSet.inter rel (eq_moves ctx x)))).
    2: reflexivity.
    destruct (eq_catalog ctx r) as [eq | ] eqn:CATALOG.
    2: reflexivity.
    specialize REL with (i := r) (eq0 := eq).
    destruct (is_smove (eq_op eq)) as [MOVE | ].
    2: reflexivity.
    destruct (peq x (eq_lhs eq)).
    2: reflexivity.
    simpl.
    subst x.
    rewrite PSet.elements_spec in ELEMENT.
    rewrite PSet.ginter in ELEMENT.
    rewrite andb_true_iff in ELEMENT.
    unfold sem_eq in REL.
    rewrite MOVE in REL.
    simpl in REL.
    destruct (eq_args eq) as [ | h t].
    reflexivity.
    destruct t.
    2: reflexivity.
    simpl in REL.
    intuition congruence.
  Qed.

  Hint Resolve forward_move_sound : cse3.

  Theorem forward_move_l_sound :
    forall rel rs m l,
      (sem_rel rel rs m) ->
      rs ## (forward_move_l (ctx := ctx) rel l) = rs ## l.
  Proof.
    induction l; simpl; intros; trivial.
    erewrite forward_move_sound by eassumption.
    intuition congruence.
  Qed.
  
  Hint Resolve forward_move_l_sound : cse3.

  Theorem kill_mem_sound :
    forall rel rs m m',
      (sem_rel rel rs m) ->
      (sem_rel (kill_mem (ctx:=ctx) rel) rs m').
  Proof.
    unfold sem_rel, sem_eq, sem_rhs, kill_mem.
    intros until m'.
    intros REL i eq.
    specialize REL with (i := i) (eq0 := eq).
    intros SUBTRACT CATALOG.
    rewrite PSet.gsubtract in SUBTRACT.
    rewrite andb_true_iff in SUBTRACT.
    intuition.
    destruct (eq_op eq) as [op | chunk addr] eqn:OP.
    - specialize ctx_kill_mem_has_depends_on_mem with (lhs := eq_lhs eq) (op := op) (args := eq_args eq) (j := i).
      rewrite (op_depends_on_memory_correct genv sp op) with (m2 := m).
      assumption.
      destruct (op_depends_on_memory op) in *; trivial.
      rewrite ctx_kill_mem_has_depends_on_mem in H0; trivial.
      discriminate H0.
      rewrite <- OP.
      rewrite CATALOG.
      destruct eq; reflexivity.
    - specialize ctx_kill_mem_has_load with (lhs := eq_lhs eq) (chunk := chunk) (addr := addr) (args := eq_args eq) (j := i).
      destruct eq as [lhs op args]; simpl in *.
      rewrite negb_true_iff in H0.
      rewrite OP in CATALOG.
      intuition.
      congruence.
  Qed.

  Hint Resolve kill_mem_sound : cse3.

  Theorem eq_find_sound:
    forall no eq id,
      eq_find (ctx := ctx) no eq = Some id ->
      eq_catalog ctx id = Some eq.
  Proof.
    unfold eq_find.
    intros.
    destruct (eq_find_oracle ctx no eq) as [ id' | ].
    2: discriminate.
    destruct (eq_catalog ctx id') as [eq' |] eqn:CATALOG.
    2: discriminate.
    destruct (eq_dec_equation eq eq').
    2: discriminate.
    congruence.
  Qed.

  Hint Resolve eq_find_sound : cse3.

  Theorem rhs_find_sound:
    forall no sop args rel src rs m,
      sem_rel rel rs m ->
      rhs_find (ctx := ctx) no sop args rel = Some src ->
      sem_rhs sop args rs m (rs # src).
  Proof.
    unfold rhs_find, sem_rel, sem_eq.
    intros until m.
    intros REL FIND.
    pose proof (pick_source_sound (PSet.elements (PSet.inter (eq_rhs_oracle ctx no sop args) rel))) as SOURCE.
    destruct (pick_source (PSet.elements (PSet.inter (eq_rhs_oracle ctx no sop args) rel))) as [ src' | ].
    2: discriminate.
    rewrite PSet.elements_spec in SOURCE.
    rewrite PSet.ginter in SOURCE.
    rewrite andb_true_iff in SOURCE.
    destruct (eq_catalog ctx src') as [eq | ] eqn:CATALOG.
    2: discriminate.
    specialize REL with (i := src') (eq0 := eq).
    destruct (eq_dec_sym_op sop (eq_op eq)).
    2: discriminate.
    destruct (eq_dec_args args (eq_args eq)).
    2: discriminate.
    simpl in FIND.
    intuition congruence.
  Qed.

  Hint Resolve rhs_find_sound : cse3.
  
  Theorem forward_move_rhs_sound :
    forall sop args rel rs m v,
      (sem_rel rel rs m) ->
      (sem_rhs sop args rs m v) ->
      (sem_rhs sop (forward_move_l (ctx := ctx) rel args) rs m v).
  Proof.
    intros until v.
    intros REL RHS.
    destruct sop; simpl in *.
    all: erewrite forward_move_l_sound by eassumption; assumption.
  Qed.

  Hint Resolve forward_move_rhs_sound : cse3.

  Lemma arg_not_replaced:
    forall (rs : regset) dst v args,
      ~ In dst args ->
      (rs # dst <- v) ## args = rs ## args.
  Proof.
    induction args; simpl; trivial.
    intuition.
    f_equal; trivial.
    apply Regmap.gso; congruence.
  Qed.

  Lemma sem_rhs_depends_on_args_only:
    forall sop args rs dst m v,
      sem_rhs sop args rs m v ->
      ~ In dst args ->
      sem_rhs sop args (rs # dst <- v) m v.
  Proof.
    unfold sem_rhs.
    intros.
    rewrite arg_not_replaced by assumption.
    assumption.
  Qed.
  
  Lemma replace_sound:
    forall no eqno dst sop args rel rs m v,
    sem_rel rel rs m ->
    sem_rhs sop args rs m  v ->
    ~ In dst args ->
    eq_find (ctx := ctx) no
            {| eq_lhs := dst;
               eq_op  := sop;
               eq_args:= args |} = Some eqno ->
    sem_rel (PSet.add eqno (kill_reg (ctx := ctx) dst rel)) (rs # dst <- v) m.
  Proof.
    intros until v.
    intros REL RHS NOTIN FIND i eq CONTAINS CATALOG.
    destruct (peq i eqno).
    - subst i.
      rewrite eq_find_sound with (no := no) (eq0 := {| eq_lhs := dst; eq_op := sop; eq_args := args |}) in CATALOG by exact FIND.
      clear FIND.
      inv CATALOG.
      unfold sem_eq.
      simpl in *.
      rewrite Regmap.gss.
      apply sem_rhs_depends_on_args_only; auto.
    - rewrite PSet.gaddo in CONTAINS by congruence.
      eapply kill_reg_sound; eauto.
  Qed.

  Lemma sem_rhs_det:
    forall {sop} {args} {rs} {m} {v} {v'},
      sem_rhs sop args rs m v ->
      sem_rhs sop args rs m v' ->
      v = v'.
  Proof.
    intros until v'. intro SEMv.
    destruct sop; simpl in *.
    - destruct eval_operation.
      congruence.
      contradiction.
    - destruct eval_addressing.
      + destruct Mem.loadv; congruence.
      + congruence.
  Qed.

  Theorem oper2_sound:
    forall no dst sop args rel rs m v,
      sem_rel rel rs m ->
      not (In dst args) ->
      sem_rhs sop args rs m v ->
      sem_rel (oper2 (ctx := ctx) no dst sop args rel) (rs # dst <- v) m.
  Proof.
    unfold oper2.
    intros until v.
    intros REL NOTIN RHS.    
    pose proof (eq_find_sound no {| eq_lhs := dst; eq_op := sop; eq_args := args |}) as EQ_FIND_SOUND.
    destruct eq_find.
    2: auto with cse3; fail.
    specialize EQ_FIND_SOUND with (id := e).
    intuition.
    intros i eq CONTAINS.
    destruct (peq i e).
    { subst i.
      rewrite H.
      clear H.
      intro Z.
      inv Z.
      unfold sem_eq.
      simpl.
      rewrite Regmap.gss.
      apply sem_rhs_depends_on_args_only; auto.
    }
    rewrite PSet.gaddo in CONTAINS by congruence.
    apply (kill_reg_sound rel rs m dst v REL i eq); auto.
  Qed.

  Hint Resolve oper2_sound : cse3.
  
  Theorem oper1_sound:
    forall no dst sop args rel rs m v,
      sem_rel rel rs m ->
      sem_rhs sop args rs m v ->
      sem_rel (oper1 (ctx := ctx) no dst sop args rel) (rs # dst <- v) m.
  Proof.
    intros.
    unfold oper1.
    destruct in_dec; auto with cse3.
  Qed.

  Hint Resolve oper1_sound : cse3.

  Lemma move_sound :
    forall no : node,
    forall rel : RELATION.t,
    forall src dst : reg,
    forall rs m,
      sem_rel rel rs m ->
      sem_rel (move (ctx:=ctx) no src dst rel) (rs # dst <- (rs # src)) m.
  Proof.
    unfold move.
    intros until m.
    intro REL.
    pose proof (eq_find_sound no  {| eq_lhs := dst; eq_op := SOp Omove; eq_args := src :: nil |}) as EQ_FIND_SOUND.
    destruct eq_find.
    - intros i eq CONTAINS.
      destruct (peq i e).
      + subst i.
        rewrite (EQ_FIND_SOUND e) by trivial.
        intro Z.
        inv Z.
        unfold sem_eq.
        simpl.
        destruct (peq src dst).
        * subst dst.
          reflexivity.
        * rewrite Regmap.gss.
          rewrite Regmap.gso by congruence.
          reflexivity.
      + intros.
        rewrite PSet.gaddo in CONTAINS by congruence.
        apply (kill_reg_sound rel rs m dst (rs # src) REL i); auto.
    - apply kill_reg_sound; auto.
  Qed.

  Hint Resolve move_sound : cse3.
  
  Theorem oper_sound:
    forall no dst sop args rel rs m v,
      sem_rel rel rs m ->
      sem_rhs sop args rs m v ->
      sem_rel (oper (ctx := ctx) no dst sop args rel) (rs # dst <- v) m.
  Proof.
    intros until v.
    intros REL RHS.
    unfold oper.
    destruct rhs_find as [src |] eqn:RHS_FIND.
    - pose proof (rhs_find_sound no sop (forward_move_l (ctx:=ctx) rel args) rel src rs m REL RHS_FIND) as SOUND.
      eapply forward_move_rhs_sound in RHS.
      2: eassumption.
      rewrite <- (sem_rhs_det SOUND RHS).
      apply move_sound; auto.
    - apply oper1_sound; auto.
  Qed.

  Hint Resolve oper_sound : cse3.

  Theorem store2_sound:
    forall chunk addr args a src rel rs m m',
      sem_rel rel rs m ->
      eval_addressing genv sp addr (rs ## args) = Some a ->
      Mem.storev chunk m a (rs # src) = Some m' ->
      sem_rel (store2 (ctx:=ctx) chunk addr args src rel) rs m'.
  Proof.
    unfold store2.
    intros.
    apply kill_mem_sound with (m:=m); auto.
  Qed.
  
  Hint Resolve store2_sound : cse3.

  Theorem store1_sound:
    forall no chunk addr args a src rel tenv rs m m',
      sem_rel rel rs m ->
      wt_regset tenv rs ->
      eval_addressing genv sp addr (rs ## args) = Some a ->
      Mem.storev chunk m a (rs#src) = Some m' ->
      sem_rel (store1 (ctx:=ctx) no chunk addr args src (tenv src) rel) rs m'.
  Proof.
    unfold store1.
    intros until m'.
    intros REL WT ADDR STORE.
    assert (sem_rel (store2 (ctx:=ctx) chunk addr args src rel) rs m') as REL' by eauto with cse3.
    destruct loadv_storev_compatible_type eqn:COMPATIBLE.
    2: auto; fail.
    destruct eq_find as [eq_id | ] eqn:FIND.
    2: auto; fail.
    intros i eq CONTAINS CATALOG.
    destruct (peq i eq_id).
    { subst i.
      rewrite eq_find_sound with (no:=no) (eq0:={| eq_lhs := src; eq_op := SLoad chunk addr; eq_args := args |}) in CATALOG; trivial.
      inv CATALOG.
      unfold sem_eq.
      simpl.
      rewrite ADDR.
      rewrite loadv_storev_really_same with (m1:=m) (v:=rs#src) (ty:=(tenv src)); trivial.
    }
    unfold sem_rel in REL'.
    rewrite PSet.gaddo in CONTAINS by congruence.
    eauto.
  Qed.
  
  Hint Resolve store1_sound : cse3.

  Theorem store_sound:
    forall no chunk addr args a src rel tenv rs m m',
      sem_rel rel rs m ->
      wt_regset tenv rs ->
      eval_addressing genv sp addr (rs ## args) = Some a ->
      Mem.storev chunk m a (rs#src) = Some m' ->
      sem_rel (store (ctx:=ctx) no chunk addr args src (tenv src) rel) rs m'.
  Proof.
    unfold store.
    intros until m'.
    intros REL WT ADDR STORE.
    rewrite <- forward_move_l_sound with (rel:=rel) (m:=m) in ADDR by trivial.
    rewrite <- forward_move_sound with (rel:=rel) (m:=m) in STORE by trivial.
    apply store1_sound with (a := a) (m := m); trivial.
    rewrite forward_move_sound with (rel:=rel) (m:=m) in STORE by trivial.
    assumption.
  Qed.
End SOUNDNESS.
