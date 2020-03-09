
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE3analysis CSE2deps CSE2depsproof HashedSet.
Require Import Lia.

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
    PSet.contains (Regmap.get lhs (get_kills eqs)) j = true.
Proof.
  unfold get_kills.
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
    PSet.contains (Regmap.get arg (get_kills eqs)) j = true.
Proof.
  unfold get_kills.
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
  
  Definition sem_eq (eq : equation) (rs : regset) (m : mem) :=
    match eq_op eq with
    | SOp op =>
      match eval_operation genv sp op (rs ## (eq_args eq)) m with
      | Some v => rs # (eq_lhs eq) = v
      | None => False
      end
    | SLoad chunk addr =>
      match
        match eval_addressing genv sp addr rs##(eq_args eq) with
        | Some a => Mem.loadv chunk m a
        | None => None
        end
      with
      | Some dat => rs # (eq_lhs eq) = dat
      | None => rs # (eq_lhs eq) = default_notrap_load_value chunk
      end
    end.

  Definition sem_rel (rel : RELATION.t) (rs : regset) (m : mem) :=
    forall i eq,
      PSet.contains rel i = true ->
      eq_catalog ctx i = Some eq ->
      sem_eq eq rs m.

  Hypothesis ctx_kills_has_lhs :
    forall lhs sop args j,
      eq_catalog ctx j = Some {| eq_lhs := lhs;
                                 eq_op  := sop;
                                 eq_args:= args |} ->
      PSet.contains (eq_kills ctx lhs) j = true.

  Hypothesis ctx_kills_has_arg :
    forall lhs sop args j,
      eq_catalog ctx j = Some {| eq_lhs := lhs;
                                 eq_op  := sop;
                                 eq_args:= args |} ->
      forall arg,
      In arg args ->
      PSet.contains (eq_kills ctx arg) j = true.

  Theorem kill_reg_sound :
    forall rel rs m dst v,
      (sem_rel rel rs m) ->
      (sem_rel (kill_reg (ctx:=ctx) dst rel) (rs#dst <- v) m).
  Proof.
    unfold sem_rel, sem_eq, kill_reg.
    intros until v.
    intros REL i eq.
    specialize REL with (i := i) (eq0 := eq).
    destruct eq as [lhs sop args]; simpl.
    specialize ctx_kills_has_lhs with (lhs := lhs) (sop := sop) (args := args) (j := i).
    specialize ctx_kills_has_arg with (lhs := lhs) (sop := sop) (args := args) (j := i) (arg := dst).
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
End SOUNDNESS.
