Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Globalenvs Values Events.
Require Import Inject.
Require Import Lia.

Local Open Scope positive.

Lemma inject_list_preserves:
  forall l prog pc dst pc0,
    pc0 < pc ->
    PTree.get pc0 (snd (inject_list prog pc dst l)) = PTree.get pc0 prog.
Proof.
  induction l; intros; simpl.
  - apply PTree.gso. lia.
  - rewrite IHl by lia.
    apply PTree.gso. lia.
Qed.

Fixpoint pos_add_nat x n :=
  match n with
  | O => x
  | S n' => Pos.succ (pos_add_nat x n')
  end.

Lemma pos_add_nat_increases : forall x n, x <= (pos_add_nat x n).
Proof.
  induction n; simpl; lia.
Qed.

Lemma pos_add_nat_succ : forall n x,
    Pos.succ (pos_add_nat x n) = pos_add_nat (Pos.succ x) n.
Proof.
  induction n; simpl; intros; trivial.
  rewrite IHn.
  reflexivity.
Qed.

Lemma pos_add_nat_monotone : forall x n1 n2,
    (n1 < n2) % nat ->
    (pos_add_nat x n1) < (pos_add_nat x n2).
Proof.
  induction n1; destruct n2; intros.
  - lia.
  - simpl.
    pose proof (pos_add_nat_increases x n2).
    lia.
  - lia.
  - simpl.
    specialize IHn1 with n2.
    lia.
Qed.

Lemma inject_list_increases:
  forall l prog pc dst,
    (fst (inject_list prog pc dst l)) = pos_add_nat pc (S (List.length l)).
Proof.
  induction l; simpl; intros; trivial.
  rewrite IHl.
  simpl.
  rewrite <- pos_add_nat_succ.
  reflexivity.
Qed.

Program Fixpoint bounded_nth
  {T : Type} (k : nat) (l : list T) (BOUND : (k < List.length l)%nat) : T :=
  match k, l with
  | O, h::_ => h
  | (S k'), _::l' => bounded_nth k' l' _
  | _, nil => _
  end.
Obligation 1.
Proof.
  simpl in BOUND.
  lia.
Qed.
Obligation 2.
Proof.
  simpl in BOUND.
  lia.
Qed.

Program Definition bounded_nth_S_statement : Prop :=
  forall (T : Type) (k : nat) (h : T) (l : list T) (BOUND : (k < List.length l)%nat),
    bounded_nth (S k) (h::l) _ = bounded_nth k l BOUND.
Obligation 1.
lia.
Qed.

Lemma bounded_nth_proof_irr :
  forall {T : Type} (k : nat) (l : list T)
         (BOUND1 BOUND2 : (k < List.length l)%nat),
    (bounded_nth k l BOUND1) = (bounded_nth k l BOUND2).
Proof.
  induction k; destruct l; simpl; intros; trivial; lia.
Qed.

Lemma bounded_nth_S : bounded_nth_S_statement.
Proof.
  unfold bounded_nth_S_statement.
  induction k; destruct l; simpl; intros; trivial.
  1, 2: lia.
  apply bounded_nth_proof_irr.
Qed.

Lemma inject_list_injected:
  forall l prog pc dst k (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat pc k) (snd (inject_list prog pc dst l)) =
    Some (inject_instr (bounded_nth k l BOUND) (Pos.succ (pos_add_nat pc k))).
Proof.
  induction l; simpl; intros.
  - lia.
  - simpl.
    destruct k as [ | k]; simpl pos_add_nat.
    + simpl bounded_nth.
      rewrite inject_list_preserves by lia.
      apply PTree.gss.
    + rewrite pos_add_nat_succ.
      erewrite IHl.
      f_equal. f_equal.
      simpl.
      apply bounded_nth_proof_irr.
      Unshelve.
      lia.
Qed.

Lemma inject_list_injected_end:
  forall l prog pc dst,
    PTree.get (pos_add_nat pc (List.length l))
              (snd (inject_list prog pc dst l)) =
    Some (Inop dst).
Proof.
  induction l; simpl; intros.
  - apply PTree.gss.
  - rewrite pos_add_nat_succ.
    apply IHl.
Qed.
    
Lemma inject_at_preserves :
  forall prog pc extra_pc l pc0,
    pc0 < extra_pc ->
    pc0 <> pc ->
    PTree.get pc0 (snd (inject_at prog pc extra_pc l)) = PTree.get pc0 prog.
Proof.
  intros. unfold inject_at.
  destruct (PTree.get pc prog) eqn:GET.
  - rewrite inject_list_preserves; trivial.
    apply PTree.gso; lia.
  - apply inject_list_preserves; trivial.
Qed.

Lemma inject_at_redirects:
  forall prog pc extra_pc l i,
    pc < extra_pc ->
    PTree.get pc prog = Some i ->
    PTree.get pc (snd (inject_at prog pc extra_pc l)) =
    Some (alter_successor i extra_pc).
Proof.
  intros until i. intros BEFORE GET. unfold inject_at.
  rewrite GET.
  rewrite inject_list_preserves by trivial.
  apply PTree.gss.
Qed.

Lemma inject_at_redirects_none:
  forall prog pc extra_pc l,
    pc < extra_pc ->
    PTree.get pc prog = None ->
    PTree.get pc (snd (inject_at prog pc extra_pc l)) = None.
Proof.
  intros until l. intros BEFORE GET. unfold inject_at.
  rewrite GET.
  rewrite inject_list_preserves by trivial.
  assumption.
Qed.

Lemma inject_at_increases:
  forall prog pc extra_pc l,
    (fst (inject_at prog pc extra_pc l)) = pos_add_nat extra_pc (S (List.length l)).  
Proof.
  intros. unfold inject_at.
  destruct (PTree.get pc prog).
  all: apply inject_list_increases.
Qed.

Lemma inject_at_injected:
  forall l prog pc extra_pc k (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat extra_pc k) (snd (inject_at prog pc extra_pc l)) =
    Some (inject_instr (bounded_nth k l BOUND) (Pos.succ (pos_add_nat extra_pc k))).
Proof.
  intros. unfold inject_at.
  destruct (prog ! pc); apply inject_list_injected.
Qed.

Lemma inject_at_injected_end:
  forall l prog pc extra_pc i,
    PTree.get pc prog = Some i ->
    PTree.get (pos_add_nat extra_pc (List.length l))
              (snd (inject_at prog pc extra_pc l)) =
    Some (Inop (successor i)).
Proof.
  intros until i. intro REW. unfold inject_at.
  rewrite REW.
  apply inject_list_injected_end.
Qed.

Lemma pair_expand:
  forall { A B : Type } (p : A*B),
    p = ((fst p), (snd p)).
Proof.
  destruct p; simpl; trivial.
Qed.

Fixpoint inject_l_position extra_pc
         (injections : list (node * (list inj_instr)))
         (k : nat) {struct injections} : node :=
  match injections with
  | nil => extra_pc
  | (pc,l)::l' =>
    match k with
    | O => extra_pc
    | S k' =>
      inject_l_position
        (Pos.succ (pos_add_nat extra_pc (List.length l))) l' k'
    end
  end.

Lemma inject_l_position_increases : forall injections pc k,
    pc <= inject_l_position pc injections k.
Proof.
  induction injections; simpl; intros.
  lia.
  destruct a as [_ l].
  destruct k.
  lia.
  specialize IHinjections with (pc := (Pos.succ (pos_add_nat pc (Datatypes.length l)))) (k := k).
  assert (pc <= (pos_add_nat pc (Datatypes.length l))) by apply pos_add_nat_increases.
  lia.
Qed.
                    
Definition inject_l (prog : code) extra_pc injections :=
  List.fold_left (fun already (injection : node * (list inj_instr)) =>
                    inject_at' already (fst injection) (snd injection))
    injections
    (extra_pc, prog).

Lemma inject_l_preserves :
  forall injections prog extra_pc pc0,
    pc0 < extra_pc ->
    List.forallb (fun injection => if peq (fst injection) pc0 then false else true) injections = true ->
    PTree.get pc0 (snd (inject_l prog extra_pc injections)) = PTree.get pc0 prog.
Proof.
  induction injections;
    intros until pc0; intros BEFORE ALL; simpl; trivial.
  unfold inject_l.
  destruct a as [pc l]. simpl.
  simpl in ALL.
  rewrite andb_true_iff in ALL.
  destruct ALL as [NEQ ALL].
  rewrite pair_expand with (p := inject_at prog pc extra_pc l).
  fold (inject_l (snd (inject_at prog pc extra_pc l))
              (fst (inject_at prog pc extra_pc l))
              injections).
  rewrite IHinjections; trivial.
  - apply inject_at_preserves; trivial.
    destruct (peq pc pc0); congruence.
  - rewrite inject_at_increases.
    pose proof (pos_add_nat_increases extra_pc (S (Datatypes.length l))).
    lia.
Qed.

Lemma nth_error_nil : forall { T : Type} k,
    nth_error (@nil T) k = None.
Proof.
  destruct k; simpl; trivial.
Qed.

Lemma inject_l_injected:
  forall injections prog injnum pc l extra_pc k
         (BELOW : forallb (fun injection => (fst injection) <? extra_pc) injections = true)
         (NUMBER : nth_error injections injnum = Some (pc, l))
         (BOUND : (k < (List.length l))%nat),
    PTree.get (pos_add_nat (inject_l_position extra_pc injections injnum) k)
              (snd (inject_l prog extra_pc injections)) =
    Some (inject_instr (bounded_nth k l BOUND)
       (Pos.succ (pos_add_nat (inject_l_position extra_pc injections injnum) k))).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER.
  }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  destruct a as [pc' l'].
  simpl fold_left.
  rewrite pair_expand with (p := inject_at prog pc' extra_pc l').
  progress fold (inject_l (snd (inject_at prog pc' extra_pc l'))
              (fst (inject_at prog pc' extra_pc l'))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - apply inject_at_injected.
    - rewrite inject_at_increases.
      apply pos_add_nat_monotone.
      lia.
    - rewrite forallb_forall.
      rewrite forallb_forall in BELOW2.
      intros loc IN.
      specialize BELOW2 with loc.
      apply BELOW2 in IN.
      destruct peq as [EQ | ]; trivial.
      rewrite EQ in IN.
      rewrite Pos.ltb_lt in IN.
      pose proof (pos_add_nat_increases extra_pc k).
      lia.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (pc := pc); trivial.
  rewrite forallb_forall.
  rewrite forallb_forall in BELOW2.
  intros loc IN.
  specialize BELOW2 with loc.
  apply BELOW2 in IN.
  pose proof (pos_add_nat_increases extra_pc (Datatypes.length l')).
  rewrite Pos.ltb_lt.
  rewrite Pos.ltb_lt in IN.
  lia.
Qed.

Lemma inject_l_injected_end:
  forall injections prog injnum pc i l extra_pc
         (BEFORE : PTree.get pc prog = Some i)
         (DISTINCT : list_norepet (map fst injections))
         (BELOW : forallb (fun injection => (fst injection) <? extra_pc) injections = true)
         (NUMBER : nth_error injections injnum = Some (pc, l)),
    PTree.get (pos_add_nat (inject_l_position extra_pc injections injnum)
                           (List.length l))
              (snd (inject_l prog extra_pc injections)) =
    Some (Inop (successor i)).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER.
  }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  destruct a as [pc' l'].
  simpl fold_left.
  rewrite pair_expand with (p := inject_at prog pc' extra_pc l').
  progress fold (inject_l (snd (inject_at prog pc' extra_pc l'))
              (fst (inject_at prog pc' extra_pc l'))
              injections).
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - apply inject_at_injected_end; trivial.
    - rewrite inject_at_increases.
      apply pos_add_nat_monotone.
      lia.
    - rewrite forallb_forall.
      rewrite forallb_forall in BELOW2.
      intros loc IN.
      specialize BELOW2 with loc.
      apply BELOW2 in IN.
      destruct peq as [EQ | ]; trivial.
      rewrite EQ in IN.
      rewrite Pos.ltb_lt in IN.
      pose proof (pos_add_nat_increases extra_pc (Datatypes.length l)).
      lia.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (pc := pc); trivial.
  {
    rewrite <- BEFORE.
    apply inject_at_preserves.
    {
      apply nth_error_In in NUMBER.
      rewrite forallb_forall in BELOW2.
      specialize BELOW2 with (pc, l).
      apply BELOW2 in NUMBER.
      apply Pos.ltb_lt in NUMBER.
      simpl in NUMBER.
      assumption.
    }
    simpl in DISTINCT.
    inv DISTINCT.
    intro SAME.
    subst pc'.
    apply nth_error_in in NUMBER.
    assert (In (fst (pc, l)) (map fst injections)) as Z.
    { apply in_map. assumption.
    }
    simpl in Z.
    auto.
  }
  { inv DISTINCT.
    assumption.
  }
  {
    rewrite forallb_forall.
    rewrite forallb_forall in BELOW2.
    intros loc IN.
    specialize BELOW2 with loc.
    apply BELOW2 in IN.
    pose proof (pos_add_nat_increases extra_pc (Datatypes.length l')).
    rewrite Pos.ltb_lt.
    rewrite Pos.ltb_lt in IN.
    assert (pos_add_nat extra_pc (Datatypes.length l') <
            pos_add_nat extra_pc (S (Datatypes.length l'))).
    { apply pos_add_nat_monotone.
      lia.
    }
    lia.
  }
Qed.


Lemma inject_l_redirects:
  forall injections prog injnum pc i l extra_pc
         (BEFORE : PTree.get pc prog = Some i)
         (DISTINCT : list_norepet (map fst injections))
         (BELOW : forallb (fun injection => (fst injection) <? extra_pc) injections = true)
         (NUMBER : nth_error injections injnum = Some (pc, l)),
    PTree.get pc (snd (inject_l prog extra_pc injections)) =
    Some (alter_successor i (inject_l_position extra_pc injections injnum)).
Proof.
  induction injections; intros.
  { rewrite nth_error_nil in NUMBER.
    discriminate NUMBER.
  }
  simpl in BELOW.
  rewrite andb_true_iff in BELOW.
  destruct BELOW as [BELOW1 BELOW2].
  unfold inject_l.
  destruct a as [pc' l'].
  simpl fold_left.
  rewrite pair_expand with (p := inject_at prog pc' extra_pc l').
  progress fold (inject_l (snd (inject_at prog pc' extra_pc l'))
              (fst (inject_at prog pc' extra_pc l'))
              injections).
  simpl in BELOW1.
  apply Pos.ltb_lt in BELOW1.
  inv DISTINCT.
  destruct injnum as [ | injnum']; simpl in NUMBER.
  { inv NUMBER.
    rewrite inject_l_preserves; simpl.
    - apply inject_at_redirects; trivial.
    - rewrite inject_at_increases.
      pose proof (pos_add_nat_increases extra_pc (S (Datatypes.length l))).
      lia.
    - rewrite forallb_forall.
      intros loc IN.
      destruct loc as [pc' l'].
      simpl in *.
      destruct peq; trivial.
      subst pc'.
      apply in_map with (f := fst) in IN.
      simpl in IN.
      exfalso.
      auto.
  }
  simpl.
  rewrite inject_at_increases.
  apply IHinjections with (pc := pc) (l := l); trivial.
  {
    rewrite <- BEFORE.
    apply nth_error_In in NUMBER.
    rewrite forallb_forall in BELOW2.
    specialize BELOW2 with (pc, l).
    simpl in BELOW2.
    rewrite Pos.ltb_lt in BELOW2.
    apply inject_at_preserves; auto.
    assert (In (fst (pc, l)) (map fst injections)) as Z.
    { apply in_map. assumption.
    }
    simpl in Z.
    intro EQ.
    subst pc'.
    auto.
  }
  {
    rewrite forallb_forall.
    rewrite forallb_forall in BELOW2.
    intros loc IN.
    specialize BELOW2 with loc.
    apply BELOW2 in IN.
    pose proof (pos_add_nat_increases extra_pc (Datatypes.length l')).
    rewrite Pos.ltb_lt.
    rewrite Pos.ltb_lt in IN.
    assert (pos_add_nat extra_pc (Datatypes.length l') <
            pos_add_nat extra_pc (S (Datatypes.length l'))).
    { apply pos_add_nat_monotone.
      lia.
    }
    lia.
  }
Qed.

(*
Lemma inject'_preserves :
  forall injections prog extra_pc pc0,
    pc0 < extra_pc ->
    PTree.get pc0 injections = None ->
    PTree.get pc0 (snd (inject' prog extra_pc injections)) = PTree.get pc0 prog.
Proof.
  intros. unfold inject'.
  rewrite PTree.fold_spec.
  change (fold_left
        (fun (a : node * code) (p : positive * list inj_instr) =>
         inject_at' a (fst p) (snd p)) (PTree.elements injections)
        (extra_pc, prog)) with (inject_l prog extra_pc (PTree.elements injections)).
  apply inject_l_preserves; trivial.
  rewrite List.forallb_forall.
  intros injection IN.
  destruct injection as [pc l].
  simpl.
  apply PTree.elements_complete in IN.
  destruct (peq pc pc0); trivial.
  congruence.
Qed.

Lemma inject_preserves :
  forall injections prog extra_pc pc0,
    pc0 < extra_pc ->
    PTree.get pc0 injections = None ->
    PTree.get pc0 (inject prog extra_pc injections) = PTree.get pc0 prog.
Proof.
  unfold inject'.
  apply inject'_preserves.
Qed.
*)

Section INJECTOR.
  Variable gen_injections : function -> PTree.t (list inj_instr).

  Definition match_prog (p tp: RTL.program) :=
    match_program (fun ctx f tf => transf_fundef gen_injections f = OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transf_program gen_injections p = OK tp -> match_prog p tp.
  Proof.
    intros. eapply match_transform_partial_program; eauto.
  Qed.

  Section PRESERVATION.

    Variables prog tprog: program.
    Hypothesis TRANSF: match_prog prog tprog.
    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Definition match_regs (f : function) (rs rs' : regset) :=
      forall r, r <= max_reg_function f -> (rs'#r = rs#r).

    Lemma match_regs_refl : forall f rs, match_regs f rs rs.
    Proof.
      unfold match_regs. intros. trivial.
    Qed.

    Lemma match_regs_trans : forall f rs1 rs2 rs3,
        match_regs f rs1 rs2 -> match_regs f rs2 rs3 -> match_regs f rs1 rs3.
    Proof.
      unfold match_regs. intros until rs3. intros M12 M23 r.
      specialize M12 with r.
      specialize M23 with r.
      intuition congruence.
    Qed.
    
    Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
    | match_frames_intro: forall res f tf sp pc rs trs
        (FUN : transf_function gen_injections f = OK tf)
        (REGS : match_regs f rs trs),
        match_frames (Stackframe res f sp pc rs)
                     (Stackframe res tf sp pc trs).

    Inductive match_states: state -> state -> Prop :=
    | match_states_intro:
      forall s f tf sp pc rs trs m ts
        (FUN : transf_function gen_injections f = OK tf)
        (STACKS: list_forall2 match_frames s ts)
        (REGS: match_regs f rs trs),
      match_states (State s f sp pc rs m) (State ts tf sp pc trs m)
    | match_states_call:
        forall s fd tfd args m ts
        (FUN : transf_fundef gen_injections fd = OK tfd)
        (STACKS: list_forall2 match_frames s ts),
          match_states (Callstate s fd args m) (Callstate ts tfd args m)
    | match_states_return:
        forall s res m ts
               (STACKS: list_forall2 match_frames s ts),
          match_states (Returnstate s res m)
                       (Returnstate ts res m).

    Lemma functions_translated:
      forall (v: val) (f: RTL.fundef),
        Genv.find_funct ge v = Some f ->
        exists tf,
          Genv.find_funct tge v = Some tf /\
          transf_fundef gen_injections f = OK tf.
    Proof.
      apply (Genv.find_funct_transf_partial TRANSF).
    Qed.

    Lemma function_ptr_translated:
      forall (b: block) (f: RTL.fundef),
        Genv.find_funct_ptr ge b = Some f ->
        exists tf,
          Genv.find_funct_ptr tge b = Some tf /\
          transf_fundef gen_injections f = OK tf.
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
      forall f tf, transf_fundef gen_injections f = OK tf
                   -> funsig tf = funsig f.
    Proof.
      destruct f; simpl; intros; monadInv H; trivial.
      unfold transf_function in *.
      destruct valid_injections1 in EQ.
      2: discriminate.
      inv EQ.
      reflexivity.
    Qed.

    Lemma stacksize_preserved:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_stacksize tf = fn_stacksize f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma params_preserved:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_params tf = fn_params f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma entrypoint_preserved:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_entrypoint tf = fn_entrypoint f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
    Qed.

    Lemma sig_preserved2:
      forall f tf, transf_function gen_injections f = OK tf ->
                   fn_sig tf = fn_sig f.
    Proof.
      destruct f.
      unfold transf_function.
      intros.
      destruct valid_injections1 in H.
      2: discriminate.
      inv H.
      reflexivity.
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
        constructor.
    Qed.

    Lemma transf_final_states:
      forall S1 S2 r, match_states S1 S2 ->
                      final_state S1 r -> final_state S2 r.
    Proof.
      intros. inv H0. inv H. inv STACKS. constructor.
    Qed.

    Lemma assign_above:
      forall f trs res v,
        (max_reg_function f) < res ->
        match_regs f trs trs # res <- v.
    Proof.
      unfold match_regs.
      intros.
      apply Regmap.gso.
      lia.
    Qed.
    
    Lemma transf_function_inj_step:
      forall ts f tf sp pc trs m ii
        (FUN : transf_function gen_injections f = OK tf)
        (GET : (fn_code tf) ! pc = Some (inject_instr ii (Pos.succ pc)))
        (VALID : valid_injection_instr (max_reg_function f) ii = true),
      exists trs',
        RTL.step ge
              (State ts tf sp pc trs m) E0
              (State ts tf sp (Pos.succ pc) trs' m) /\
        match_regs (f : function) trs trs'.
    Proof.
      destruct ii as [op args res | chunk addr args res]; simpl; intros.
      - repeat rewrite andb_true_iff in VALID.
        rewrite negb_true_iff in VALID.
        destruct VALID as (MAX_REG & NOTRAP & LENGTH).
        rewrite Pos.ltb_lt in MAX_REG.
        rewrite Nat.eqb_eq in LENGTH.
        destruct (eval_operation ge sp op trs ## args m) as [v | ] eqn:EVAL.
        + exists (trs # res <- v).
          split.
          * apply exec_Iop with (op := op) (args := args) (res := res); assumption.
          * apply assign_above; auto.
        + exfalso.
          generalize EVAL.
          apply is_trapping_op_sound; trivial.
          rewrite map_length.
          assumption.
      - rewrite Pos.ltb_lt in VALID.
        destruct (eval_addressing ge sp addr trs ## args) as [a | ] eqn:ADDR.
        + destruct (Mem.loadv chunk m a) as [v | ] eqn:LOAD.
          * exists (trs # res <- v).
            split.
            ** apply exec_Iload with (trap := NOTRAP) (chunk := chunk) (addr := addr) (args := args) (dst := res) (a := a); assumption.
            ** apply assign_above; auto.
          * exists (trs # res <- Vundef).
            split.
            ** apply exec_Iload_notrap2 with (chunk := chunk) (addr := addr) (args := args) (dst := res) (a := a); assumption.
            ** apply assign_above; auto.
        + exists (trs # res <- Vundef).
          split.
          * apply exec_Iload_notrap1 with (chunk := chunk) (addr := addr) (args := args) (dst := res); assumption.
          * apply assign_above; auto.
    Qed.

    Lemma bounded_nth_In: forall {T : Type} (l : list T) k LESS,
        In (bounded_nth k l LESS) l.
    Proof.
      induction l; simpl; intros.
      lia.
      destruct k; simpl.
      - left; trivial.
      - right. apply IHl.
    Qed.

    Lemma transf_function_inj_starstep_rec :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f)) inj_n =
               Some (src_pc, inj_code))
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f)) inj_n = inj_pc)
        (k : nat)
        (CUR : (k <= (List.length inj_code))%nat)
        (trs : regset),
      exists trs',
        match_regs (f : function) trs trs' /\
        Smallstep.star RTL.step ge
              (State ts tf sp (pos_add_nat inj_pc
                                    ((List.length inj_code) - k)%nat) trs m) E0
              (State ts tf sp (pos_add_nat inj_pc (List.length inj_code)) trs' m).
    Proof.
      induction k; simpl; intros.
      { rewrite Nat.sub_0_r.
        exists trs.
        split.
        - apply match_regs_refl.
        - constructor.
      }
      assert (k <= Datatypes.length inj_code)%nat as KK by lia.
      pose proof (IHk KK) as IH.
      clear IHk KK.
      pose proof FUN as VALIDATE.
      unfold transf_function, valid_injections1 in VALIDATE.
      destruct forallb eqn:FORALL in VALIDATE.
      2: discriminate.
      injection VALIDATE.
      intro TF.
      symmetry in TF.
      pose proof (inject_l_injected (PTree.elements (gen_injections f)) (fn_code f) inj_n src_pc inj_code (Pos.succ (max_pc_function f)) ((List.length inj_code) - (S k))%nat) as INJECTED.
      lapply INJECTED.
      { clear INJECTED.
        intro INJECTED.
        assert ((Datatypes.length inj_code - S k <
                 Datatypes.length inj_code)%nat) as LESS by lia.
        pose proof (INJECTED INJ LESS) as INJ'.
        replace (snd
            (inject_l (fn_code f) (Pos.succ (max_pc_function f))
                      (PTree.elements (gen_injections f)))) with (fn_code tf) in INJ'.
        2: rewrite TF; simpl; reflexivity.                                              apply transf_function_inj_step with (f:=f) (ts:=ts) (sp:=sp) (trs:=trs) (m := m) in INJ'.
        2: assumption.
        {
          destruct INJ' as [trs'' [STEP STEPMATCH]].
          destruct (IH trs'') as [trs' [STARSTEPMATCH STARSTEP]].
          exists trs'.
          split.
          { apply match_regs_trans with (rs2 := trs''); assumption. }
          eapply Smallstep.star_step with (t1:=E0) (t2:=E0).
          {
            rewrite POSITION in STEP.
            exact STEP.
          }
          {
            replace (Datatypes.length inj_code - k)%nat
              with (S (Datatypes.length inj_code - (S k)))%nat in STARSTEP by lia.
            simpl pos_add_nat in STARSTEP.
            exact STARSTEP.
          }
          constructor.
        }
        rewrite forallb_forall in FORALL.
        specialize FORALL with  (src_pc, inj_code).
        lapply FORALL.
        {
          simpl.
          rewrite andb_true_iff.
          intros (SRC & ALL_VALID).
          rewrite forallb_forall in ALL_VALID.
          apply ALL_VALID.
          apply bounded_nth_In.
        }
        apply nth_error_In with (n := inj_n).
        assumption.
      }
      rewrite forallb_forall in FORALL.
      rewrite forallb_forall.
      intros x INx.
      rewrite Pos.ltb_lt.
      pose proof (FORALL x INx) as ALLx.
      rewrite andb_true_iff in ALLx.
      destruct ALLx as [ALLx1 ALLx2].
      rewrite Pos.leb_le in ALLx1.
      lia.
    Qed.
    
    Lemma transf_function_inj_starstep :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f)) inj_n =
               Some (src_pc, inj_code))
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f)) inj_n = inj_pc)
        (trs : regset),
      exists trs',
        match_regs (f : function) trs trs' /\
        Smallstep.star RTL.step ge
              (State ts tf sp inj_pc trs m) E0
              (State ts tf sp (pos_add_nat inj_pc (List.length inj_code)) trs' m).
    Proof.
      intros.
      replace (State ts tf sp inj_pc trs m) with (State ts tf sp (pos_add_nat inj_pc ((List.length inj_code) - (List.length inj_code))%nat) trs m).
      eapply transf_function_inj_starstep_rec; eauto.
      f_equal.
      rewrite <- minus_n_n.
      reflexivity.
    Qed.

    Lemma transf_function_inj_end :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code i
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f)) inj_n =
               Some (src_pc, inj_code))
        (SRC: (fn_code f) ! src_pc = Some i)
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f)) inj_n = inj_pc)
        (trs : regset),
        RTL.step ge
          (State ts tf sp (pos_add_nat inj_pc (List.length inj_code)) trs m) E0
          (State ts tf sp (successor i) trs m).
    Proof.
      intros.
      pose proof FUN as VALIDATE.
      unfold transf_function, valid_injections1 in VALIDATE.
      destruct forallb eqn:FORALL in VALIDATE.
      2: discriminate.
      injection VALIDATE.
      intro TF.
      symmetry in TF.
      Check inject_l_injected_end.
      pose proof (inject_l_injected_end (PTree.elements (gen_injections f)) (fn_code f) inj_n src_pc i inj_code (Pos.succ (max_pc_function f))) as INJECTED.
      lapply INJECTED.
      2: assumption.
      clear INJECTED.
      intro INJECTED.
      lapply INJECTED.
      2: apply (PTree.elements_keys_norepet (gen_injections f)); fail.
      clear INJECTED.
      intro INJECTED.
      lapply INJECTED.
      { clear INJECTED.
        intro INJECTED.
        pose proof (INJECTED INJ) as INJ'.
        clear INJECTED.
        replace (snd
                   (inject_l (fn_code f) (Pos.succ (max_pc_function f))
                             (PTree.elements (gen_injections f)))) with (fn_code tf) in INJ'.
        2: rewrite TF; simpl; reflexivity.
        rewrite POSITION in INJ'.
        apply exec_Inop.
        assumption.
      }
      clear INJECTED.
      rewrite forallb_forall in FORALL.
      rewrite forallb_forall.
      intros x INx.
      rewrite Pos.ltb_lt.
      pose proof (FORALL x INx) as ALLx.
      rewrite andb_true_iff in ALLx.
      destruct ALLx as [ALLx1 ALLx2].
      rewrite Pos.leb_le in ALLx1.
      lia.
    Qed.

    Lemma transf_function_inj_plusstep :
      forall ts f tf sp m inj_n src_pc inj_pc inj_code i
        (FUN : transf_function gen_injections f = OK tf)
        (INJ : nth_error (PTree.elements (gen_injections f)) inj_n =
               Some (src_pc, inj_code))
        (SRC: (fn_code f) ! src_pc = Some i)
        (POSITION : inject_l_position (Pos.succ (max_pc_function f))
                                      (PTree.elements (gen_injections f)) inj_n = inj_pc)
        (trs : regset),
      exists trs',
        match_regs (f : function) trs trs' /\
        Smallstep.plus RTL.step ge
              (State ts tf sp inj_pc trs m) E0
              (State ts tf sp (successor i) trs' m).
    Proof.
      intros.
      destruct (transf_function_inj_starstep ts f tf sp m inj_n src_pc inj_pc inj_code FUN INJ POSITION trs) as [trs' [MATCH PLUS]].
      exists trs'.
      split. assumption.
      eapply Smallstep.plus_right.
      exact PLUS.
      eapply transf_function_inj_end; eassumption.
      reflexivity.
    Qed.

End PRESERVATION.
End INJECTOR.
