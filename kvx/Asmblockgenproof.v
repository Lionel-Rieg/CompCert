(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           Xavier Leroy       INRIA Paris-Rocquencourt       *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** Correctness proof for kvx/Asmblock generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Machblock Conventions Asmblock.
Require Import Asmblockgen Asmblockgenproof0 Asmblockgenproof1 Asmblockprops.
Require Import Axioms.

Module MB := Machblock.
Module AB := Asmvliw.

Definition match_prog (p: Machblock.program) (tp: Asmvliw.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Machblock.program.
Variable tprog: Asmvliw.program.
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
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (size_blocks x.(fn_blocks))); inv EQ0.
  omega.
Qed.

Section TRANSL_LABEL. (* Lemmas on translation of MB.is_label into AB.is_label *)

Lemma gen_bblocks_label:
  forall hd bdy ex tbb tc,
  gen_bblocks hd bdy ex = tbb::tc ->
  header tbb = hd.
Proof.
  intros until tc. intros GENB. unfold gen_bblocks in GENB.
  destruct (extract_ctl ex); try destruct c; try destruct i; try destruct bdy.
  all: inv GENB; simpl; auto.
Qed.

Lemma gen_bblocks_label2:
  forall hd bdy ex tbb1 tbb2,
  gen_bblocks hd bdy ex = tbb1::tbb2::nil ->
  header tbb2 = nil.
Proof.
  intros until tbb2. intros GENB. unfold gen_bblocks in GENB.
  destruct (extract_ctl ex); try destruct c; try destruct i; try destruct bdy.
  all: inv GENB; simpl; auto.
Qed.

Remark in_dec_transl:
  forall lbl hd,
  (if in_dec lbl hd then true else false) = (if MB.in_dec lbl hd then true else false).
Proof.
  intros. destruct (in_dec lbl hd), (MB.in_dec lbl hd). all: tauto.
Qed.

Lemma transl_is_label:
  forall lbl bb tbb f ep tc,
  transl_block f bb ep = OK (tbb::tc) ->
  is_label lbl tbb = MB.is_label lbl bb.
Proof.
  intros until tc. intros TLB.
  destruct tbb as [thd tbdy tex]; simpl in *.
  monadInv TLB.
  unfold is_label. simpl.
  apply gen_bblocks_label in H0. simpl in H0. subst.
  rewrite in_dec_transl. auto.
Qed.

Lemma transl_is_label_false2:
  forall lbl bb f ep tbb1 tbb2,
  transl_block f bb ep = OK (tbb1::tbb2::nil) ->
  is_label lbl tbb2 = false.
Proof.
  intros until tbb2. intros TLB.
  destruct tbb2 as [thd tbdy tex]; simpl in *.
  monadInv TLB. apply gen_bblocks_label2 in H0. simpl in H0. subst.
  apply is_label_correct_false. simpl. auto.
Qed.

Lemma transl_is_label2:
  forall f bb ep tbb1 tbb2 lbl,
  transl_block f bb ep = OK (tbb1::tbb2::nil) ->
     is_label lbl tbb1 = MB.is_label lbl bb
  /\ is_label lbl tbb2 = false.
Proof.
  intros. split. eapply transl_is_label; eauto. eapply transl_is_label_false2; eauto.
Qed.

Lemma transl_block_nonil:
  forall f c ep tc,
  transl_block f c ep = OK tc ->
  tc <> nil.
Proof.
  intros. monadInv H. unfold gen_bblocks.
  destruct (extract_ctl x0); try destruct c0; try destruct x; try destruct i.
  all: discriminate.
Qed.

Lemma transl_block_limit: forall f bb ep tbb1 tbb2 tbb3 tc,
  ~transl_block f bb ep = OK (tbb1 :: tbb2 :: tbb3 :: tc).
Proof.
  intros. intro. monadInv H.
  unfold gen_bblocks in H0.
  destruct (extract_ctl x0); try destruct x; try destruct c; try destruct i.
  all: discriminate.
Qed.

Lemma find_label_transl_false:
  forall x f lbl bb ep x',
  transl_block f bb ep = OK x ->
  MB.is_label lbl bb = false ->
  find_label lbl (x++x') = find_label lbl x'.
Proof.
  intros until x'. intros TLB MBis; simpl; auto.
  destruct x as [|x0 x1]; simpl; auto.
  destruct x1 as [|x1 x2]; simpl; auto.
  - erewrite <- transl_is_label in MBis; eauto. rewrite MBis. auto.
  - destruct x2 as [|x2 x3]; simpl; auto.
    + erewrite <- transl_is_label in MBis; eauto. rewrite MBis.
      erewrite transl_is_label_false2; eauto.
    + apply transl_block_limit in TLB. destruct TLB.
Qed.

Lemma transl_blocks_label:
  forall lbl f c tc ep,
  transl_blocks f c ep = OK tc ->
  match MB.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_blocks f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H.
  destruct (MB.is_label lbl a) eqn:MBis.
  - destruct x as [|tbb tc]. { apply transl_block_nonil in EQ. contradiction. }
    simpl find_label. exploit transl_is_label; eauto. intros ABis. rewrite MBis in ABis.
    rewrite ABis.
    eexists. eexists. split; eauto. simpl transl_blocks.
    assert (MB.header a <> nil).
    { apply MB.is_label_correct_true in MBis.
      destruct (MB.header a). contradiction. discriminate. }
    destruct (MB.header a); try contradiction.
    rewrite EQ. simpl. rewrite EQ1. simpl. auto.
  - apply IHc in EQ1. destruct (MB.find_label lbl c).
    + destruct EQ1 as (tc' & FIND & TLBS). exists tc'; eexists; auto.
      erewrite find_label_transl_false; eauto.
    + erewrite find_label_transl_false; eauto.
Qed.

Lemma find_label_nil:
  forall bb lbl c,
  header bb = nil ->
  find_label lbl (bb::c) = find_label lbl c.
Proof.
  intros. destruct bb as [hd bdy ex]; simpl in *. subst.
  assert (is_label lbl {| AB.header := nil; AB.body := bdy; AB.exit := ex; AB.correct := correct |} = false).
  { erewrite <- is_label_correct_false. simpl. auto. }
  rewrite H. auto.
Qed.

Theorem transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match MB.find_label lbl f.(MB.fn_code) with
  | None => find_label lbl tf.(fn_blocks) = None
  | Some c => exists tc, find_label lbl tf.(fn_blocks) = Some tc /\ transl_blocks f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (size_blocks (fn_blocks x))); inv EQ0. clear g.
  monadInv EQ. unfold make_prologue. simpl fn_blocks. repeat (rewrite find_label_nil); simpl; auto.
  eapply transl_blocks_label; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Machblock code translates to a valid ``go to''
  transition in the generated Asmblock code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  MB.find_label lbl f.(MB.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros (tc & A & B).
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. unfold par_goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall b f c, is_tail (b :: c) f.(MB.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmblockgenproof0.return_address_exists; eauto.

- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (size_blocks x.(fn_blocks))); inv EQ0. monadInv EQ. simpl.
  exists x; exists true; split; auto.
  repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using a complex simulation diagram
  of the following form.
<<
                                     MB.step
                      ---------------------------------------->
                      header      body          exit
                  st1 -----> st2 -----> st3 ------------------> st4
                   |          |          |                       |
                   |   (A)    |   (B)    |         (C)           |
   match_codestate |          |          |                       |
                   |  header  |   body1  |  body2                |  match_states
                  cs1 -----> cs2 -----> cs3 ------> cs4          |
                   |                  /                \  exit   |
   match_asmstate  |   ---------------                  --->---  |
                   |  /   match_asmstate                       \ |
                  st'1 ---------------------------------------> st'2
                                     AB.step                  *
>>
  The invariant between each MB.step/AB.step is the [match_states] predicate below.
  However, we also need to introduce an intermediary state [Codestate] which allows
  us to reason on a finer grain, executing header, body and exit separately.

  This [Codestate] consists in a state like [Asmblock.State], except that the
  code is directly stored in the state, much like [Machblock.State]. It also features
  additional useful elements to keep track of while executing a bblock.
*)

Remark preg_of_not_FP: forall r, negb (mreg_eq r MFP) = true -> IR FP <> preg_of r.
Proof.
  intros. change (IR FP) with (preg_of MFP). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed.

Inductive match_states: Machblock.state -> Asmvliw.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#FP = parent_sp s),
      match_states (Machblock.State s fb sp c ms m)
                   (Asmvliw.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Machblock.Callstate s fb ms m)
                   (Asmvliw.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Machblock.Returnstate s ms m)
                   (Asmvliw.State rs m').

Record codestate :=
  Codestate {     pstate: state;        (**r projection to Asmblock.state *)
                  pheader: list label;
                  pbody1: list basic;   (**r list of basic instructions coming from the translation of the Machblock body *)
                  pbody2: list basic;   (**r list of basic instructions coming from the translation of the Machblock exit *)
                  pctl: option control; (**r exit instruction, coming from the translation of the Machblock exit *)
                  ep: bool;             (**r reflects the [ep] variable used in the translation *)
                  rem: list AB.bblock;  (**r remaining bblocks to execute *)
                  cur: bblock           (**r current bblock to execute - to keep track of its size when incrementing PC *)
            }.

(* The part that deals with Machblock <-> Codestate agreement
 * Note about DXP: the property of [ep] only matters if the current block doesn't have a header, hence the condition *)
Inductive match_codestate fb: Machblock.state -> codestate -> Prop :=
  | match_codestate_intro:
      forall s sp ms m rs0 m0 f tc ep c bb tbb tbc tbi
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m0)
        (TBC: transl_basic_code f (MB.body bb) (if MB.header bb then ep else false) = OK tbc)
        (TIC: transl_instr_control f (MB.exit bb) = OK tbi)
        (TBLS: transl_blocks f c false = OK tc)
        (AG: agree ms sp rs0)
        (DXP: (if MB.header bb then ep else false) = true -> rs0#FP = parent_sp s)
        ,
      match_codestate fb (Machblock.State s fb sp (bb::c) ms m)
        {|  pstate := (Asmvliw.State rs0 m0);
            pheader := (MB.header bb);
            pbody1 := tbc;
            pbody2 := extract_basic tbi;
            pctl := extract_ctl tbi;
            ep := ep;
            rem := tc;
            cur := tbb
        |}
.

(* The part ensuring that the code in Codestate actually resides at [rs PC] *)
Inductive match_asmstate fb: codestate -> Asmvliw.state -> Prop :=
  | match_asmstate_some:
      forall rs f tf tc m tbb ofs ep tbdy tex lhd
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (TRANSF: transf_function f = OK tf)
        (PCeq: rs PC = Vptr fb ofs)
        (TAIL: code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) (tbb::tc))
        ,
      match_asmstate fb 
        {|  pstate := (Asmvliw.State rs m);
            pheader := lhd;
            pbody1 := tbdy;
            pbody2 := extract_basic tex;
            pctl := extract_ctl tex;
            ep := ep;
            rem := tc;
            cur := tbb |}
        (Asmvliw.State rs m)
.

(* Useful for dealing with the many cases in some proofs *)
Ltac exploreInst :=
  repeat match goal with
  | [ H : match ?var with | _ => _ end = _ |- _ ] => destruct var
  | [ H : OK _ = OK _ |- _ ] => monadInv H
  | [ |- context[if ?b then _ else _] ] => destruct b
  | [ |- context[match ?m with | _ => _ end] ] => destruct m
  | [ |- context[match ?m as _ return _ with | _ => _ end]] => destruct m
  | [ H : bind _ _ = OK _ |- _ ] => monadInv H
  | [ H : Error _ = OK _ |- _ ] => inversion H
  end.

(** Some translation properties *)

Lemma transl_blocks_nonil:
  forall f bb c tc ep,
  transl_blocks f (bb::c) ep = OK tc ->
  exists tbb tc', tc = tbb :: tc'.
Proof.
  intros until ep0. intros TLBS. monadInv TLBS. monadInv EQ. unfold gen_bblocks.
  destruct (extract_ctl x2).
  - destruct c0; destruct i; simpl; eauto. destruct x1; simpl; eauto.
  - destruct x1; simpl; eauto.
Qed.

Lemma no_builtin_preserved:
  forall f ex x2,
  (forall ef args res, ex <> Some (MBbuiltin ef args res)) ->
  transl_instr_control f ex = OK x2 ->
  (exists i, extract_ctl x2 = Some (PCtlFlow i))
    \/ extract_ctl x2 = None.
Proof.
  intros until x2. intros Hbuiltin TIC.
  destruct ex.
  - destruct c.
    (* MBcall *)
    + simpl in TIC. exploreInst; simpl; eauto.
    (* MBtailcall *)
    + simpl in TIC. exploreInst; simpl; eauto.
    (* MBbuiltin *)
    + assert (H: Some (MBbuiltin e l b) <>  Some (MBbuiltin e l b)).
        apply Hbuiltin. contradict H; auto.
    (* MBgoto *)
    + simpl in TIC. exploreInst; simpl; eauto.
    (* MBcond *)
    + simpl in TIC. unfold transl_cbranch in TIC. exploreInst; simpl; eauto.
      * unfold transl_opt_compuimm. exploreInst; simpl; eauto.
      * unfold transl_opt_compluimm. exploreInst; simpl; eauto.
      * unfold transl_comp_float64. exploreInst; simpl; eauto.
      * unfold transl_comp_notfloat64. exploreInst; simpl; eauto.
      * unfold transl_comp_float32. exploreInst; simpl; eauto.
      * unfold transl_comp_notfloat32. exploreInst; simpl; eauto.
    (* MBjumptable *)
    + simpl in TIC. exploreInst; simpl; eauto.
    (* MBreturn *)
    + simpl in TIC. monadInv TIC. simpl. eauto.
  - monadInv TIC. simpl; auto.
Qed.

Lemma transl_blocks_distrib:
  forall c f bb tbb tc ep,
  transl_blocks f (bb::c) ep = OK (tbb::tc)
  -> (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res))
  -> transl_block f bb (if MB.header bb then ep else false) = OK (tbb :: nil)
  /\ transl_blocks f c false = OK tc.
Proof.
  intros until ep0. intros TLBS Hbuiltin.
  destruct bb as [hd bdy ex].
  monadInv TLBS. monadInv EQ.
  exploit no_builtin_preserved; eauto. intros Hectl. destruct Hectl.
  - destruct H as [i Hectl].
  unfold gen_bblocks in H0. rewrite Hectl in H0. inv H0.
  simpl in *. unfold transl_block; simpl. rewrite EQ0. rewrite EQ. simpl.
  unfold gen_bblocks. rewrite Hectl. auto.
  - unfold gen_bblocks in H0. rewrite H in H0.
    destruct x1 as [|bi x1].
    + simpl in H0. inv H0. simpl in *. unfold transl_block; simpl. rewrite EQ0. rewrite EQ. simpl.
      unfold gen_bblocks. rewrite H. auto.
    + simpl in H0. inv H0. simpl in *. unfold transl_block; simpl. rewrite EQ0. rewrite EQ. simpl.
      unfold gen_bblocks. rewrite H. auto.
Qed.

Lemma gen_bblocks_nobuiltin:
  forall thd tbdy tex tbb,
  (tbdy <> nil \/ extract_ctl tex <> None) ->
  (forall ef args res, extract_ctl tex <> Some (PExpand (Pbuiltin ef args res))) ->
  gen_bblocks thd tbdy tex = tbb :: nil ->
     header tbb = thd
  /\ body tbb = tbdy ++ extract_basic tex
  /\ exit tbb = extract_ctl tex.
Proof.
  intros until tbb. intros Hnonil Hnobuiltin GENB. unfold gen_bblocks in GENB.
  destruct (extract_ctl tex) eqn:ECTL.
  - destruct c.
    + destruct i; try (inv GENB; simpl; auto; fail).
      assert False. eapply Hnobuiltin. eauto. destruct H.
    + inv GENB. simpl. auto.
  - inversion Hnonil.
    + destruct tbdy as [|bi tbdy]; try (contradict H; simpl; auto; fail). inv GENB. auto.
    + contradict H; simpl; auto.
Qed.

Lemma transl_instr_basic_nonil:
  forall k f bi ep x,
  transl_instr_basic f bi ep k = OK x ->
  x <> nil.
Proof.
  intros until x. intros TIB.
  destruct bi.
  - simpl in TIB. unfold loadind in TIB. exploreInst; try discriminate.
  - simpl in TIB. unfold storeind in TIB. exploreInst; try discriminate.
  - simpl in TIB. monadInv TIB. unfold loadind in EQ. exploreInst; try discriminate.
  - simpl in TIB. unfold transl_op in TIB. exploreInst; try discriminate.
    unfold transl_cond_op in EQ0. exploreInst; try discriminate.
    unfold transl_cond_float64. exploreInst; try discriminate.
    unfold transl_cond_notfloat64. exploreInst; try discriminate.
    unfold transl_cond_float32. exploreInst; try discriminate.
    unfold transl_cond_notfloat32. exploreInst; try discriminate.
  - simpl in TIB. unfold transl_load in TIB. exploreInst; try discriminate.
    all: monadInv TIB; unfold transl_memory_access in EQ0; unfold transl_memory_access2 in EQ0; unfold transl_memory_access2XS in EQ0; exploreInst; try discriminate.
  - simpl in TIB. unfold transl_store in TIB. exploreInst; try discriminate.
    all: monadInv TIB; unfold transl_memory_access in EQ0; unfold transl_memory_access2 in EQ0; unfold transl_memory_access2XS in EQ0; exploreInst; try discriminate. 
Qed.

Lemma transl_basic_code_nonil:
  forall bdy f x ep,
  bdy <> nil ->
  transl_basic_code f bdy ep = OK x ->
  x <> nil.
Proof.
  induction bdy as [|bi bdy].
    intros. contradict H0; auto.
  destruct bdy as [|bi2 bdy].
  - clear IHbdy. intros f x b _ TBC. simpl in TBC. eapply transl_instr_basic_nonil; eauto.
  - intros f x b Hnonil TBC. remember (bi2 :: bdy) as bdy'.
    monadInv TBC. 
    assert (x0 <> nil).
      eapply IHbdy; eauto. subst bdy'. discriminate.
    eapply transl_instr_basic_nonil; eauto.
Qed.

Lemma transl_instr_control_nonil:
  forall ex f x,
  ex <> None ->
  transl_instr_control f ex = OK x ->
  extract_ctl x <> None.
Proof.
  intros ex f x Hnonil TIC.
  destruct ex as [ex|].
  - clear Hnonil. destruct ex.
    all: try (simpl in TIC; exploreInst; discriminate).
    + simpl in TIC. unfold transl_cbranch in TIC. exploreInst; try discriminate.
      * unfold transl_opt_compuimm. exploreInst; try discriminate.
      * unfold transl_opt_compluimm. exploreInst; try discriminate.
      * unfold transl_comp_float64. exploreInst; try discriminate.
      * unfold transl_comp_notfloat64. exploreInst; try discriminate.
      * unfold transl_comp_float32. exploreInst; try discriminate.
      * unfold transl_comp_notfloat32. exploreInst; try discriminate.
  - contradict Hnonil; auto.
Qed.

Lemma transl_instr_control_nobuiltin:
  forall f ex x,
  (forall ef args res, ex <> Some (MBbuiltin ef args res)) ->
  transl_instr_control f ex = OK x ->
  (forall ef args res, extract_ctl x <> Some (PExpand (Pbuiltin ef args res))).
Proof.
  intros until x. intros Hnobuiltin TIC. intros until res.
  unfold transl_instr_control in TIC. exploreInst.
  all: try discriminate.
  - assert False. eapply Hnobuiltin; eauto. destruct H.
  - unfold transl_cbranch in TIC. exploreInst.
    all: try discriminate.
    * unfold transl_opt_compuimm. exploreInst. all: try discriminate.
    * unfold transl_opt_compluimm. exploreInst. all: try discriminate.
    * unfold transl_comp_float64. exploreInst; try discriminate.
    * unfold transl_comp_notfloat64. exploreInst; try discriminate.
    * unfold transl_comp_float32. exploreInst; try discriminate.
    * unfold transl_comp_notfloat32. exploreInst; try discriminate.
Qed.

(* Proving that one can decompose a [match_state] relation into a [match_codestate]
   and a [match_asmstate], along with some helpful properties tying both relations together *)

Theorem match_state_codestate:
  forall mbs abs s fb sp bb c ms m,
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  (MB.body bb <> nil \/ MB.exit bb <> None) ->
  mbs = (Machblock.State s fb sp (bb::c) ms m) ->
  match_states mbs abs ->
  exists cs fb f tbb tc ep,
    match_codestate fb mbs cs /\ match_asmstate fb cs abs
    /\ Genv.find_funct_ptr ge fb = Some (Internal f)
    /\ transl_blocks f (bb::c) ep = OK (tbb::tc)
    /\ body tbb = pbody1 cs ++ pbody2 cs
    /\ exit tbb = pctl cs
    /\ cur cs = tbb /\ rem cs = tc
    /\ pstate cs = abs.
Proof.
  intros until m. intros Hnobuiltin Hnotempty Hmbs MS. subst. inv MS.
  inv AT. clear H0. exploit transl_blocks_nonil; eauto. intros (tbb & tc' & Htc). subst.
  exploit transl_blocks_distrib; eauto. intros (TLB & TLBS). clear H2.
  monadInv TLB. exploit gen_bblocks_nobuiltin; eauto.
    { inversion Hnotempty.
      - destruct (MB.body bb) as [|bi bdy]; try (contradict H0; simpl; auto; fail).
        left. eapply transl_basic_code_nonil; eauto.
      - destruct (MB.exit bb) as [ei|]; try (contradict H0; simpl; auto; fail).
        right. eapply transl_instr_control_nonil; eauto. }
    eapply transl_instr_control_nobuiltin; eauto.
  intros (Hth & Htbdy & Htexit).
  exists {| pstate := (State rs m'); pheader := (Machblock.header bb); pbody1 := x; pbody2 := extract_basic x0;
            pctl := extract_ctl x0; ep := ep0; rem := tc'; cur := tbb |}, fb, f, tbb, tc', ep0.
  repeat split. 1-2: econstructor; eauto.
  { destruct (MB.header bb). eauto. discriminate. } eauto.
  unfold transl_blocks. fold transl_blocks. unfold transl_block. rewrite EQ. simpl. rewrite EQ1; simpl.
  rewrite TLBS. simpl. rewrite H2.
  all: simpl; auto.
Qed.

Definition mb_remove_body (bb: MB.bblock) := 
  {| MB.header := MB.header bb; MB.body := nil; MB.exit := MB.exit bb |}.

Lemma exec_straight_pnil:
  forall c rs1 m1 rs2 m2,
  exec_straight tge c rs1 m1 (Pnop ::g nil) rs2 m2 ->
  exec_straight tge c rs1 m1 nil rs2 m2.
Proof.
  intros. eapply exec_straight_trans. eapply H. econstructor; eauto.
Qed.

Lemma transl_block_nobuiltin:
  forall f bb ep tbb,
  (MB.body bb <> nil \/ MB.exit bb <> None) ->
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  transl_block f bb ep = OK (tbb :: nil) ->
  exists c c',
     transl_basic_code f (MB.body bb) ep = OK c
  /\ transl_instr_control f (MB.exit bb) = OK c'
  /\ body tbb = c ++ extract_basic c'
  /\ exit tbb = extract_ctl c'.
Proof.
  intros until tbb. intros Hnonil Hnobuiltin TLB. monadInv TLB. destruct Hnonil.
  - eexists. eexists. split; eauto. split; eauto. eapply gen_bblocks_nobuiltin; eauto.
    left. eapply transl_basic_code_nonil; eauto. eapply transl_instr_control_nobuiltin; eauto.
  - eexists. eexists. split; eauto. split; eauto. eapply gen_bblocks_nobuiltin; eauto.
    right. eapply transl_instr_control_nonil; eauto. eapply transl_instr_control_nobuiltin; eauto.
Qed.

Lemma nextblock_preserves: 
  forall rs rs' bb r,
  rs' = nextblock bb rs ->
  data_preg r = true ->
  rs r = rs' r.
Proof.
  intros. destruct r; try discriminate.
  subst. Simpl.
Qed.

Remark cons3_app {A: Type}:
  forall a b c (l: list A),
  a :: b :: c :: l = (a :: b :: c :: nil) ++ l.
Proof.
  intros. simpl. auto.
Qed.

Lemma exec_straight_opt_body2:
  forall c rs1 m1 c' rs2 m2,
  exec_straight_opt tge c rs1 m1 c' rs2 m2 ->
  exists body,
     exec_body tge body rs1 m1 = Next rs2 m2
  /\ (basics_to_code body) ++g c' = c.
Proof.
  intros until m2. intros EXES.
  inv EXES.
  - exists nil. split; auto.
  - eapply exec_straight_body2. auto.
Qed.

Lemma extract_basics_to_code:
  forall lb c,
  extract_basic (basics_to_code lb ++ c) = lb ++ extract_basic c.
Proof.
  induction lb; intros; simpl; congruence.
Qed.

Lemma extract_ctl_basics_to_code:
  forall lb c,
  extract_ctl (basics_to_code lb ++ c) = extract_ctl c.
Proof.
  induction lb; intros; simpl; congruence.
Qed.

(* See (C) in the diagram. The proofs are mostly adapted from the previous Mach->Asm proofs, but are
   unfortunately quite cumbersome. To reproduce them, it's best to have a Coq IDE with you and see by
   yourself the steps *)
Theorem step_simu_control:
  forall bb' fb fn s sp c ms' m' rs2 m2 t S'' rs1 m1 tbb tbdy2 tex cs2,
  MB.body bb' = nil ->
  (forall ef args res, MB.exit bb' <> Some (MBbuiltin ef args res)) ->
  Genv.find_funct_ptr tge fb = Some (Internal fn) ->
  pstate cs2 = (Asmvliw.State rs2 m2) ->
  pbody1 cs2 = nil -> pbody2 cs2 = tbdy2 -> pctl cs2 = tex ->
  cur cs2 = tbb ->
  match_codestate fb (MB.State s fb sp (bb'::c) ms' m') cs2 ->
  match_asmstate fb cs2 (Asmvliw.State rs1 m1) ->
  exit_step return_address_offset ge (MB.exit bb') (MB.State s fb sp (bb'::c) ms' m') t S'' ->
  (exists rs3 m3 rs4 m4,
      exec_body tge tbdy2 rs2 m2 = Next rs3 m3
  /\  exec_control_rel tge fn tex tbb rs3 m3 rs4 m4
  /\  match_states S'' (State rs4 m4)).
Proof.
  intros until cs2. intros Hbody Hbuiltin FIND Hpstate Hpbody1 Hpbody2 Hpctl Hcur MCS MAS ESTEP.
  inv ESTEP.
  - inv MCS. inv MAS. simpl in *.
    inv Hpstate.
    destruct ctl.
    + (* MBcall *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      assert (f0 = f) by congruence. subst f0.
      assert (NOOV: size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned).
        eapply transf_function_no_overflow; eauto.
      destruct s1 as [rf|fid]; simpl in H7.
      * (* Indirect call *)
        monadInv H1.
        assert (ms' rf = Vptr f' Ptrofs.zero).
        { unfold find_function_ptr in H14. destruct (ms' rf); try discriminate.
          revert H14; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence. }
        assert (rs2 x = Vptr f' Ptrofs.zero).
        { exploit ireg_val; eauto. rewrite H; intros LD; inv LD; auto. }
        generalize (code_tail_next_int _ _ _ _ NOOV TAIL). intro CT1.
        remember (Ptrofs.add _ _) as ofs'.
        assert (TCA: transl_code_at_pc ge (Vptr fb ofs') fb f c false tf tc).
        { econstructor; eauto. }
        assert (f1 = f) by congruence. subst f1.
        exploit return_address_offset_correct; eauto. intros; subst ra.

        repeat eexists.
          rewrite H6. econstructor; eauto.
          rewrite H7. econstructor; eauto.
        econstructor; eauto.
          econstructor; eauto. eapply agree_sp_def; eauto. simpl. eapply agree_exten; eauto. intros. Simpl.
        simpl. Simpl. rewrite PCeq. rewrite Heqofs'. simpl. auto.

      * (* Direct call *)
        monadInv H1.
        generalize (code_tail_next_int _ _ _ _ NOOV TAIL). intro CT1.
        remember (Ptrofs.add _ _) as ofs'.
        assert (TCA: transl_code_at_pc ge (Vptr fb ofs') fb f c false tf tc).
          econstructor; eauto.
        assert (f1 = f) by congruence. subst f1.
        exploit return_address_offset_correct; eauto. intros; subst ra.
        repeat eexists.
          rewrite H6. econstructor; eauto.
          rewrite H7. econstructor; eauto.
        econstructor; eauto.
          econstructor; eauto. eapply agree_sp_def; eauto. simpl. eapply agree_exten; eauto. intros. Simpl.
        Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. simpl in H14. rewrite H14. auto.
        Simpl. simpl. subst. Simpl. simpl. unfold Val.offset_ptr. rewrite PCeq. auto.
    + (* MBtailcall *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      assert (f0 = f) by congruence.  subst f0.
      assert (NOOV: size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned).
        eapply transf_function_no_overflow; eauto.
      exploit Mem.loadv_extends. eauto. eexact H15. auto. simpl. intros [parent' [A B]].
      destruct s1 as [rf|fid]; simpl in H13. 
      * monadInv H1.
        assert (ms' rf = Vptr f' Ptrofs.zero).
          { destruct (ms' rf); try discriminate. revert H13. predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence. }
        assert (rs2 x = Vptr f' Ptrofs.zero).
          { exploit ireg_val; eauto. rewrite H; intros LD; inv LD; auto. }

        assert (f = f1) by congruence. subst f1. clear FIND1. clear H14.
        exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
        exploit exec_straight_body; eauto.
          { simpl. eauto. }
        intros EXEB.
        repeat eexists.
          rewrite H6. simpl extract_basic. eauto.
          rewrite H7. simpl extract_ctl. simpl. reflexivity.
        econstructor; eauto.
          { apply agree_set_other.
            - econstructor; auto with asmgen.
              + apply V.
              + intro r. destruct r; apply V; auto.
            - eauto with asmgen. }
        assert (IR x <> IR GPR12 /\ IR x <> IR GPR32 /\ IR x <> IR GPR16).
          { clear - EQ. destruct x; repeat split; try discriminate.
            all: unfold ireg_of in EQ; destruct rf; try discriminate. }
        Simpl. inv H1. inv H3. rewrite Z; auto; try discriminate.
      * monadInv H1. assert (f = f1) by congruence. subst f1. clear FIND1. clear H14.
        exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
        exploit exec_straight_body; eauto.
          simpl. eauto.
        intros EXEB.
        repeat eexists.
          rewrite H6. simpl extract_basic. eauto.
          rewrite H7. simpl extract_ctl. simpl. reflexivity.
        econstructor; eauto.
        { apply agree_set_other.
          - econstructor; auto with asmgen.
            + apply V.
            + intro r. destruct r; apply V; auto.
          - eauto with asmgen. }
        { Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H13. auto. }
    + (* MBbuiltin (contradiction) *)
      assert (MB.exit bb' <> Some (MBbuiltin e l b)) by (apply Hbuiltin).
      rewrite <- H in H1. contradict H1; auto.
    + (* MBgoto *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      assert (f0 = f) by congruence. subst f0. assert (f1 = f) by congruence. subst f1. clear H11.
      remember (nextblock tbb rs2) as rs2'.
      exploit functions_transl. eapply FIND0. eapply TRANSF0. intros FIND'.
      assert (tf = fn) by congruence. subst tf.
      exploit find_label_goto_label.
        eauto. eauto.
        instantiate (2 := rs2').
        { subst. unfold nextblock, incrPC. Simpl. unfold Val.offset_ptr. rewrite PCeq. eauto. }
        eauto.
      intros (tc' & rs' & GOTO & AT2 & INV).

      eexists. eexists. repeat eexists. repeat split.
        rewrite H6. simpl extract_basic. simpl. eauto.
        rewrite H7. simpl extract_ctl. simpl. rewrite <- Heqrs2'. eauto.
      econstructor; eauto.
        rewrite Heqrs2' in INV. unfold nextblock, incrPC in INV.
        eapply agree_exten; eauto with asmgen.
        assert (forall r : preg, r <> PC -> rs' r = rs2 r).
        { intros. destruct r.
          - destruct g. all: rewrite INV; Simpl; auto.
          - rewrite INV; Simpl; auto.
          - contradiction. }
        eauto with asmgen.
        congruence.
    + (* MBcond *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      * (* MBcond true *)
        assert (f0 = f) by congruence. subst f0.
        exploit eval_condition_lessdef.
          eapply preg_vals; eauto.
          all: eauto.
        intros EC.
        exploit transl_cbranch_correct_true; eauto. intros (rs' & jmp & A & B & C).
        exploit exec_straight_opt_body2. eauto. intros (bdy & EXEB & BTC).
        assert (PCeq': rs2 PC = rs' PC). { inv A; auto. erewrite <- exec_straight_pc. 2: eapply H. eauto. }
        rewrite PCeq' in PCeq.
        assert (f1 = f) by congruence. subst f1.
        exploit find_label_goto_label.
          4: eapply H16. 1-2: eauto. instantiate (2 := (nextblock tbb rs')). rewrite nextblock_pc.
          unfold Val.offset_ptr. rewrite PCeq. eauto.
        intros (tc' & rs3 & GOTOL & TLPC & Hrs3).
        exploit functions_transl. eapply FIND1. eapply TRANSF0. intros FIND'.
        assert (tf = fn) by congruence. subst tf.

        repeat eexists.
          rewrite H6. rewrite <- BTC. rewrite extract_basics_to_code. simpl. rewrite app_nil_r. eauto.
          rewrite H7. rewrite <- BTC. rewrite extract_ctl_basics_to_code. simpl extract_ctl. rewrite B. eauto.

        econstructor; eauto.
          eapply agree_exten with rs2; eauto with asmgen.
          { intros. destruct r; try destruct g; try discriminate.
            all: rewrite Hrs3; try discriminate; unfold nextblock, incrPC; Simpl. }
        intros. discriminate.

      * (* MBcond false *)
        assert (f0 = f) by congruence. subst f0.
        exploit eval_condition_lessdef.
          eapply preg_vals; eauto.
          all: eauto.
        intros EC.

        exploit transl_cbranch_correct_false; eauto. intros (rs' & jmp & A & B & C).
        exploit exec_straight_opt_body2. eauto. intros (bdy & EXEB & BTC).
        assert (PCeq': rs2 PC = rs' PC). { inv A; auto. erewrite <- exec_straight_pc. 2: eapply H. eauto. }
        rewrite PCeq' in PCeq.
        exploit functions_transl. eapply FIND1. eapply TRANSF0. intros FIND'.
        assert (tf = fn) by congruence. subst tf.

        assert (NOOV: size_blocks fn.(fn_blocks) <= Ptrofs.max_unsigned).
          eapply transf_function_no_overflow; eauto.
        generalize (code_tail_next_int _ _ _ _ NOOV TAIL). intro CT1.

        repeat eexists.
          rewrite H6. rewrite <- BTC. rewrite extract_basics_to_code. simpl. rewrite app_nil_r. eauto.
          rewrite H7. rewrite <- BTC. rewrite extract_ctl_basics_to_code. simpl extract_ctl. rewrite B. eauto.

        econstructor; eauto.
          unfold nextblock, incrPC. Simpl. unfold Val.offset_ptr. rewrite PCeq. econstructor; eauto.
          eapply agree_exten with rs2; eauto with asmgen.
          { intros. destruct r; try destruct g; try discriminate.
            all: rewrite <- C; try discriminate; unfold nextblock, incrPC; Simpl. }
        intros. discriminate.
    + (* MBjumptable *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      assert (f0 = f) by congruence. subst f0.
      monadInv H1.
      generalize (transf_function_no_overflow _ _ TRANSF0); intro NOOV.
      assert (f1 = f) by congruence. subst f1.
      exploit find_label_goto_label. 4: eapply H16. 1-2: eauto. instantiate (2 := (nextblock tbb rs2) # GPR62 <- Vundef # GPR63 <- Vundef).
        unfold nextblock, incrPC. Simpl. unfold Val.offset_ptr. rewrite PCeq. reflexivity.
      exploit functions_transl. eapply FIND0. eapply TRANSF0. intros FIND3. assert (fn = tf) by congruence. subst fn.

      intros [tc' [rs' [A [B C]]]].
      exploit ireg_val; eauto. rewrite H13. intros LD; inv LD.
      
      repeat eexists.
        rewrite H6. simpl extract_basic. simpl. eauto.
        rewrite H7. simpl extract_ctl. simpl. Simpl. rewrite <- H1. unfold Mach.label in H14. unfold label. rewrite H14. eapply A.
      econstructor; eauto.
        eapply agree_undef_regs; eauto. intros. rewrite C; auto with asmgen.
        { assert (destroyed_by_jumptable = R62 :: R63 :: nil) by auto. rewrite H2 in H0. simpl in H0. inv H0.
          destruct (preg_eq r' GPR63). subst. contradiction.
          destruct (preg_eq r' GPR62). subst. contradiction.
          destruct r'; Simpl. }
        discriminate.
    + (* MBreturn *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      assert (f0 = f) by congruence. subst f0.
      assert (NOOV: size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned).
        eapply transf_function_no_overflow; eauto.
      exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
      exploit exec_straight_body; eauto.
        simpl. eauto.
      intros EXEB.
      assert (f1 = f) by congruence. subst f1.
      
      repeat eexists.
        rewrite H6. simpl extract_basic. eauto.
        rewrite H7. simpl extract_ctl. simpl. reflexivity.
      econstructor; eauto.
        unfold nextblock, incrPC. repeat apply agree_set_other; auto with asmgen.

  - inv MCS. inv MAS. simpl in *. subst. inv Hpstate.
    destruct bb' as [hd' bdy' ex']; simpl in *. subst.
    monadInv TBC. monadInv TIC. simpl in *. rewrite H5. rewrite H6.
    simpl. repeat eexists.
    econstructor. 4: instantiate (3 := false). all:eauto.
      unfold nextblock, incrPC. Simpl. unfold Val.offset_ptr. rewrite PCeq.
      assert (NOOV: size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned).
        eapply transf_function_no_overflow; eauto.
      assert (f = f0) by congruence. subst f0. econstructor; eauto.
      generalize (code_tail_next_int _ _ _ _ NOOV TAIL). intro CT1. eauto.
    eapply agree_exten; eauto. intros. Simpl.
    discriminate.
Qed.

Definition mb_remove_first (bb: MB.bblock) := 
  {| MB.header := MB.header bb; MB.body := tail (MB.body bb); MB.exit := MB.exit bb |}.

Lemma exec_straight_body:
  forall c c' lc rs1 m1 rs2 m2,
  exec_straight tge c rs1 m1 c' rs2 m2 ->
  code_to_basics c = Some lc ->
  exists l ll,
     c = l ++ c'
  /\ code_to_basics l = Some ll
  /\ exec_body tge ll rs1 m1 = Next rs2 m2.
Proof.
  induction c; try (intros; inv H; fail).
  intros until m2. intros EXES CTB. inv EXES.
  - exists (i1 ::g nil),(i1::nil). repeat (split; simpl; auto). rewrite H6. auto.
  - inv CTB. destruct (code_to_basics c); try discriminate. inv H0.
    eapply IHc in H7; eauto. destruct H7 as (l' & ll & Hc & CTB & EXECB). subst.
    exists (i ::g l'),(i::ll). repeat (split; simpl; auto).
      rewrite CTB. auto.
      rewrite H1. auto.
Qed.

Lemma basics_to_code_app:
  forall c l x ll,
  basics_to_code c = l ++ basics_to_code x ->
  code_to_basics l = Some ll ->
  c = ll ++ x.
Proof.
  intros. apply (f_equal code_to_basics) in H.
  erewrite code_to_basics_dist in H; eauto. 2: eapply code_to_basics_id.
  rewrite code_to_basics_id in H. inv H. auto.
Qed.

Lemma basics_to_code_app2:
  forall i c l x ll,
  (PBasic i) :: basics_to_code c = l ++ basics_to_code x ->
  code_to_basics l = Some ll ->
  i :: c = ll ++ x.
Proof.
  intros until ll. intros.
  exploit basics_to_code_app. instantiate (3 := (i::c)). simpl.
  all: eauto.
Qed.

(* Handling the individual instructions of theorem (B) in the above diagram. A bit less cumbersome, but still tough *)
Theorem step_simu_basic:
  forall bb bb' s fb sp c ms m rs1 m1 ms' m' bi cs1 tbdy bdy,
  MB.header bb = nil -> MB.body bb = bi::(bdy) -> (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  bb' = {| MB.header := nil; MB.body := bdy; MB.exit := MB.exit bb |} ->
  basic_step ge s fb sp ms m bi ms' m' ->
  pstate cs1 = (State rs1 m1) -> pbody1 cs1 = tbdy ->
  match_codestate fb (MB.State s fb sp (bb::c) ms m) cs1 ->
  (exists rs2 m2 l cs2 tbdy',
       cs2 = {| pstate := (State rs2 m2); pheader := nil; pbody1 := tbdy'; pbody2 := pbody2 cs1;
                pctl := pctl cs1; ep := fp_is_parent (ep cs1) bi; rem := rem cs1; cur := cur cs1 |}
    /\ tbdy = l ++ tbdy'
    /\ exec_body tge l rs1 m1 = Next rs2 m2
    /\ match_codestate fb (MB.State s fb sp (bb'::c) ms' m') cs2).
Proof.
  intros until bdy. intros Hheader Hbody Hnobuiltin (* Hnotempty *) Hbb' BSTEP Hpstate Hpbody1 MCS. inv MCS.
  simpl in *. inv Hpstate.
  rewrite Hbody in TBC. monadInv TBC.
  inv BSTEP.

  - (* MBgetstack *)
    simpl in EQ0.
    unfold Mach.load_stack in H.
    exploit Mem.loadv_extends; eauto. intros [v' [A B]].
    rewrite (sp_val _ _ _ AG) in A.
    exploit loadind_correct; eauto with asmgen.
    intros (rs2 & EXECS & Hrs'1 & Hrs'2).
    eapply exec_straight_body in EXECS.
      2: eapply code_to_basics_id; eauto.
    destruct EXECS as (l & Hlbi & BTC & CTB & EXECB).
    exists rs2, m1, Hlbi.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
      eapply basics_to_code_app; eauto.
    remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    assert (Hheadereq: MB.header bb' = MB.header bb). { subst. simpl. auto. }
    subst. simpl in Hheadereq.

    eapply match_codestate_intro; eauto.
      { simpl. simpl in EQ. rewrite <- Hheadereq in EQ. assumption. }
    eapply agree_set_mreg; eauto with asmgen.
    intro Hep. simpl in Hep. 
    destruct (andb_prop _ _ Hep). clear Hep.
    rewrite <- Hheadereq in DXP. subst. rewrite <- DXP. rewrite Hrs'2. reflexivity.
    discriminate. apply preg_of_not_FP; assumption. reflexivity.

  - (* MBsetstack *)
    simpl in EQ0.
    unfold Mach.store_stack in H.
    assert (Val.lessdef (ms src) (rs1 (preg_of src))). { eapply preg_val; eauto. }
    exploit Mem.storev_extends; eauto. intros [m2' [A B]].
    exploit storeind_correct; eauto with asmgen.
    rewrite (sp_val _ _ _ AG) in A. eauto. intros [rs' [P Q]].

    eapply exec_straight_body in P.
      2: eapply code_to_basics_id; eauto.
    destruct P as (l & ll & TBC & CTB & EXECB).
    exists rs', m2', ll.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
      eapply basics_to_code_app; eauto.
    remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    subst.
    eapply match_codestate_intro; eauto. simpl. simpl in EQ. rewrite Hheader in EQ. auto.

    eapply agree_undef_regs; eauto with asmgen.
    simpl; intros. rewrite Q; auto with asmgen. rewrite Hheader in DXP. auto.
  - (* MBgetparam *)
    simpl in EQ0.

    assert (f0 = f) by congruence; subst f0.
    unfold Mach.load_stack in *.
    exploit Mem.loadv_extends. eauto. eexact H0. auto.
    intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
    exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
    exploit Mem.loadv_extends. eauto. eexact H1. auto.
    intros [v' [C D]].

    monadInv EQ0. rewrite Hheader. rewrite Hheader in DXP.
    destruct ep0 eqn:EPeq.

  (* RTMP contains parent *)
    + exploit loadind_correct. eexact EQ1.
      instantiate (2 := rs1). rewrite DXP; eauto.
      intros [rs2 [P [Q R]]].

      eapply exec_straight_body in P.
        2: eapply code_to_basics_id; eauto.
      destruct P as (l & ll & BTC & CTB & EXECB).
      exists rs2, m1, ll. eexists.
      eexists. split. instantiate (1 := x). eauto.
      repeat (split; auto).
      { eapply basics_to_code_app; eauto. }
      remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
      assert (Hheadereq: MB.header bb' = MB.header bb). { subst. simpl. auto. }
      subst.
      eapply match_codestate_intro; eauto.

      eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
      simpl; intros. rewrite R; auto with asmgen.
      apply preg_of_not_FP; auto.

  (* RTMP does not contain parent *)
    + rewrite chunk_of_Tptr in A. 
      exploit loadind_ptr_correct. eexact A. intros [rs2 [P [Q R]]].
      exploit loadind_correct. eexact EQ1. instantiate (2 := rs2). rewrite Q. eauto.
      intros [rs3 [S [T U]]].

      exploit exec_straight_trans.
        eapply P.
        eapply S.
      intros EXES.

      eapply exec_straight_body in EXES.
        2: simpl. 2: erewrite code_to_basics_id; eauto.
      destruct EXES as (l & ll & BTC & CTB & EXECB).
      exists rs3, m1, ll.
      eexists. eexists. split. instantiate (1 := x). eauto.
      repeat (split; auto).
        eapply basics_to_code_app2; eauto.
      remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
      assert (Hheadereq: MB.header bb' = MB.header bb). { subst. auto. }
      subst.
      eapply match_codestate_intro; eauto.
      eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
      instantiate (1 := rs2#FP <- (rs3#FP)). intros.
      rewrite Pregmap.gso; auto with asmgen.
      congruence.
      intros. unfold Pregmap.set. destruct (PregEq.eq r' FP). congruence. auto with asmgen.
      simpl; intros. rewrite U; auto with asmgen.
      apply preg_of_not_FP; auto.
  - (* MBop *)
    simpl in EQ0. rewrite Hheader in DXP.
    
    assert (eval_operation tge sp op (map ms args) m' = Some v).
      rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
    exploit eval_operation_lessdef.
      eapply preg_vals; eauto.
      2: eexact H0.
      all: eauto.
    intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
    exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].

    eapply exec_straight_body in P.
      2: eapply code_to_basics_id; eauto.
    destruct P as (l & ll & TBC & CTB & EXECB).
    exists rs2, m1, ll.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
      eapply basics_to_code_app; eauto.
    remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    subst.
    eapply match_codestate_intro; eauto. simpl. simpl in EQ. rewrite Hheader in EQ. auto.
    apply agree_set_undef_mreg with rs1; auto. 
    apply Val.lessdef_trans with v'; auto.
    simpl; intros. destruct (andb_prop _ _ H1); clear H1.
    rewrite R; auto. apply preg_of_not_FP; auto.
Local Transparent destroyed_by_op.
    destruct op; simpl; auto; congruence.
  - (* MBload *)
    simpl in EQ0. rewrite Hheader in DXP.

    assert (eval_addressing tge sp addr (map ms args) = Some a).
      rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
    exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
    intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
    exploit Mem.loadv_extends; eauto. intros [v' [C D]].
    exploit transl_load_correct; eauto.
    intros [rs2 [P [Q R]]].

    eapply exec_straight_body in P.
      2: eapply code_to_basics_id; eauto.
    destruct P as (l & ll & TBC & CTB & EXECB).
    exists rs2, m1, ll.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
      eapply basics_to_code_app; eauto.
    remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    assert (Hheadereq: MB.header bb' = MB.header bb). { subst. auto. }
    subst.
    eapply match_codestate_intro; eauto. simpl. simpl in EQ.
    rewrite <- Hheadereq in EQ. assumption.
    eapply agree_set_mreg; eauto with asmgen.
    intro Hep. simpl in Hep. 
    destruct (andb_prop _ _ Hep). clear Hep.
    subst. rewrite <- DXP. rewrite R; try discriminate. reflexivity.
    apply preg_of_not_FP; assumption. reflexivity.

  - (* notrap1 cannot happen *)
    simpl in EQ0. unfold transl_load in EQ0.
    destruct addr; simpl in H.
    all: unfold transl_load_rrrXS, transl_load_rrr, transl_load_rro in EQ0;
    monadInv EQ0; unfold transl_memory_access2XS, transl_memory_access2, transl_memory_access in EQ2;
    destruct args as [|h0 t0]; try discriminate;
    destruct t0 as [|h1 t1]; try discriminate;
    destruct t1 as [|h2 t2]; try discriminate.
    
  - (* MBload notrap2 TODO *)
    simpl in EQ0. rewrite Hheader in DXP.

    assert (eval_addressing tge sp addr (map ms args) = Some a).
      rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
    exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
    intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.

    destruct (Mem.loadv chunk m1 a') as [v' | ] eqn:Hload.
    {
    exploit transl_load_correct; eauto.
    intros [rs2 [P [Q R]]].

    eapply exec_straight_body in P.
      2: eapply code_to_basics_id; eauto.
    destruct P as (l & ll & TBC & CTB & EXECB).
    exists rs2, m1, ll.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
    eapply basics_to_code_app; eauto.
    eapply match_codestate_intro; eauto. simpl. rewrite Hheader in *.
    simpl in EQ. assumption.

    eapply agree_set_undef_mreg; eauto. intros; auto with asmgen.

    simpl. intro.
    rewrite R; try congruence.
    apply DXP.
    destruct ep0; simpl in *; congruence.
    apply preg_of_not_FP.
    destruct ep0; simpl in *; congruence.
    }
    { 
    exploit transl_load_correct_notrap2; eauto.
    intros [rs2 [P [Q R]]].

    eapply exec_straight_body in P.
      2: eapply code_to_basics_id; eauto.
    destruct P as (l & ll & TBC & CTB & EXECB).
    exists rs2, m1, ll.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
      eapply basics_to_code_app; eauto.
    remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
(*     assert (Hheadereq: MB.header bb' = MB.header bb). { subst. auto. }
    rewrite <- Hheadereq. *) subst.
    eapply match_codestate_intro; eauto. simpl. rewrite Hheader in *. simpl in EQ. assumption.

    eapply agree_set_undef_mreg; eauto. intros; auto with asmgen.
    simpl. intro.
    rewrite R; try congruence.
    apply DXP.
    destruct ep0; simpl in *; congruence.
    apply preg_of_not_FP.
    destruct ep0; simpl in *; congruence.
    }
  - (* MBstore *)
    simpl in EQ0. rewrite Hheader in DXP.

    assert (eval_addressing tge sp addr (map ms args) = Some a).
      rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
    exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
    intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
    assert (Val.lessdef (ms src) (rs1 (preg_of src))). eapply preg_val; eauto.
    exploit Mem.storev_extends; eauto. intros [m2' [C D]].
    exploit transl_store_correct; eauto. intros [rs2 [P Q]].

    eapply exec_straight_body in P.
      2: eapply code_to_basics_id; eauto.
    destruct P as (l & ll & TBC & CTB & EXECB).
    exists rs2, m2', ll.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto).
      eapply basics_to_code_app; eauto.
    remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    assert (Hheadereq: MB.header bb' = MB.header bb). { subst. auto. }
    subst.
    eapply match_codestate_intro; eauto. simpl. simpl in EQ.
    rewrite <- Hheadereq in EQ. assumption.
    eapply agree_undef_regs; eauto with asmgen.
    intro Hep. simpl in Hep.
    subst. rewrite <- DXP. rewrite Q; try discriminate. reflexivity. reflexivity.
Qed.

Lemma exec_body_trans:
  forall l l' rs0 m0 rs1 m1 rs2 m2,
  exec_body tge l rs0 m0 = Next rs1 m1 ->
  exec_body tge l' rs1 m1 = Next rs2 m2 ->
  exec_body tge (l++l') rs0 m0 = Next rs2 m2.
Proof.
  induction l.
  - simpl. congruence.
  - intros until m2. intros EXEB1 EXEB2.
    inv EXEB1. destruct (exec_basic_instr _) eqn:EBI; try discriminate.
    simpl. rewrite EBI. eapply IHl; eauto.
Qed.

Definition mb_remove_header bb := {| MB.header := nil; MB.body := MB.body bb; MB.exit := MB.exit bb |}.

Program Definition remove_header tbb := {| header := nil; body := body tbb; exit := exit tbb |}.
Next Obligation.
  destruct tbb. simpl. auto.
Qed.

Inductive exec_header: codestate -> codestate -> Prop :=
  | exec_header_cons: forall cs1,
      exec_header cs1 {| pstate := pstate cs1; pheader := nil; pbody1 := pbody1 cs1; pbody2 := pbody2 cs1;
                          pctl := pctl cs1; ep := (if pheader cs1 then ep cs1 else false); rem := rem cs1;
                          cur := cur cs1 |}.

(* Theorem (A) in the diagram, the easiest of all *)
Theorem step_simu_header:
  forall bb s fb sp c ms m rs1 m1 cs1,
  pstate cs1 = (State rs1 m1) ->
  match_codestate fb (MB.State s fb sp (bb::c) ms m) cs1 ->
  (exists cs1',
       exec_header cs1 cs1'
    /\ match_codestate fb (MB.State s fb sp (mb_remove_header bb::c) ms m) cs1').
Proof.
  intros until cs1. intros Hpstate MCS.
  eexists. split; eauto.
  econstructor; eauto.
  inv MCS. simpl in *. inv Hpstate.
  econstructor; eauto.
Qed.

Lemma step_matchasm_header:
  forall fb cs1 cs1' s1,
  match_asmstate fb cs1 s1 ->
  exec_header cs1 cs1' ->
  match_asmstate fb cs1' s1.
Proof.
  intros until s1. intros MAS EXH.
  inv MAS. inv EXH.
  simpl. econstructor; eauto.
Qed.

(* Theorem (B) in the diagram, using step_simu_basic + induction on the Machblock body *)
Theorem step_simu_body:
  forall bb s fb sp c ms m rs1 m1 ms' cs1 m',
  MB.header bb = nil ->
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  body_step ge s fb sp (MB.body bb) ms m ms' m' ->
  pstate cs1 = (State rs1 m1) ->
  match_codestate fb (MB.State s fb sp (bb::c) ms m) cs1 ->
  (exists rs2 m2 cs2 ep,
       cs2 = {| pstate := (State rs2 m2); pheader := nil; pbody1 := nil; pbody2 := pbody2 cs1;
                pctl := pctl cs1; ep := ep; rem := rem cs1; cur := cur cs1 |}
    /\ exec_body tge (pbody1 cs1) rs1 m1 = Next rs2 m2
    /\ match_codestate fb (MB.State s fb sp ({| MB.header := nil; MB.body := nil; MB.exit := MB.exit bb |}::c) ms' m') cs2).
Proof.
  intros bb. destruct bb as [hd bdy ex]; simpl; auto. induction bdy as [|bi bdy].
  - intros until m'. intros Hheader Hnobuiltin BSTEP Hpstate MCS.
    inv BSTEP.
    exists rs1, m1, cs1, (ep cs1).
    inv MCS. inv Hpstate. simpl in *. monadInv TBC. repeat (split; simpl; auto).
    econstructor; eauto.
  - intros until m'. intros Hheader Hnobuiltin BSTEP Hpstate MCS. inv BSTEP.
    rename ms' into ms''. rename m' into m''. rename rs' into ms'. rename m'0 into m'.
    exploit (step_simu_basic); eauto. simpl. eauto. simpl; auto. simpl; auto.
    intros (rs2 & m2 & l & cs2 & tbdy' & Hcs2 & Happ & EXEB & MCS').
    simpl in *.
    exploit IHbdy. auto. 2: eapply H6. 3: eapply MCS'. all: eauto. subst; eauto. simpl; auto.
    intros (rs3 & m3 & cs3 & ep & Hcs3 & EXEB' & MCS'').
    exists rs3, m3, cs3, ep.
    repeat (split; simpl; auto). subst. simpl in *. auto.
    rewrite Happ. eapply exec_body_trans; eauto. rewrite Hcs2 in EXEB'; simpl in EXEB'. auto.
Qed.

Lemma exec_body_control:
  forall b rs1 m1 rs2 m2 rs3 m3 fn,
  exec_body tge (body b) rs1 m1 = Next rs2 m2 ->
  exec_control_rel tge fn (exit b) b rs2 m2 rs3 m3 ->
  exec_bblock_rel tge fn b rs1 m1 rs3 m3.
Proof.
  intros until fn. intros EXEB EXECTL.
  econstructor; eauto. inv EXECTL.
  unfold exec_bblock. rewrite EXEB. auto.
Qed.

Definition mbsize (bb: MB.bblock) := (length (MB.body bb) + length_opt (MB.exit bb))%nat.

Lemma mbsize_eqz:
  forall bb, mbsize bb = 0%nat -> MB.body bb = nil /\ MB.exit bb = None.
Proof.
  intros. destruct bb as [hd bdy ex]; simpl in *. unfold mbsize in H.
  remember (length _) as a. remember (length_opt _) as b.
  assert (a = 0%nat) by omega. assert (b = 0%nat) by omega. subst. clear H.
  inv H0. inv H1. destruct bdy; destruct ex; auto.
  all: try discriminate.
Qed.

Lemma mbsize_neqz:
  forall bb, mbsize bb <> 0%nat -> (MB.body bb <> nil \/ MB.exit bb <> None).
Proof.
  intros. destruct bb as [hd bdy ex]; simpl in *.
  destruct bdy; destruct ex; try (right; discriminate); try (left; discriminate).
  contradict H. unfold mbsize. simpl. auto.
Qed.

(* Bringing theorems (A), (B) and (C) together, for the case of the absence of builtin instruction *)
(* This more general form is easier to prove, but the actual theorem is step_simulation_bblock further below *)
Lemma step_simulation_bblock':
  forall sf f sp bb bb' bb'' rs m rs' m' s'' c S1,
  bb' = mb_remove_header bb ->
  body_step ge sf f sp (Machblock.body bb') rs m rs' m' ->
  bb'' = mb_remove_body bb' ->
  (forall ef args res, MB.exit bb'' <> Some (MBbuiltin ef args res)) ->
  exit_step return_address_offset ge (Machblock.exit bb'') (Machblock.State sf f sp (bb'' :: c) rs' m') E0 s'' ->
  match_states (Machblock.State sf f sp (bb :: c) rs m) S1 ->
  exists S2 : state, plus step tge S1 E0 S2 /\ match_states s'' S2.
Proof.
  intros until S1. intros Hbb' BSTEP Hbb'' Hbuiltin ESTEP MS.
  destruct (mbsize bb) eqn:SIZE.
  - apply mbsize_eqz in SIZE. destruct SIZE as (Hbody & Hexit).
    destruct bb as [hd bdy ex]; simpl in *; subst.
    inv MS. inv AT. exploit transl_blocks_nonil; eauto. intros (tbb & tc' & Htc). subst. rename tc' into tc.
    monadInv H2. simpl in *. inv ESTEP. inv BSTEP.
    eexists. split. eapply plus_one.
    exploit functions_translated; eauto. intros (tf0 & FIND' & TRANSF'). monadInv TRANSF'.
    assert (x = tf) by congruence. subst x.
    eapply exec_step_internal; eauto. eapply find_bblock_tail; eauto.
    unfold exec_bblock. simpl. eauto.
    econstructor. eauto. eauto. eauto.
    unfold nextblock, incrPC. Simpl. unfold Val.offset_ptr. rewrite <- H.
    assert (NOOV: size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned).
      eapply transf_function_no_overflow; eauto.
    econstructor; eauto.
      generalize (code_tail_next_int _ _ _ _ NOOV H3). intro CT1. eauto.
    eapply agree_exten; eauto. intros. Simpl.
    intros. discriminate.
  - subst. exploit mbsize_neqz. { instantiate (1 := bb). rewrite SIZE. discriminate. }
    intros Hnotempty.

    (* initial setting *)
    exploit match_state_codestate.
      2: eapply Hnotempty.
      all: eauto.
    intros (cs1 & fb & f0 & tbb & tc & ep & MCS & MAS & FIND & TLBS & Hbody & Hexit & Hcur & Hrem & Hpstate).

    (* step_simu_header part *)
    assert (exists rs1 m1, pstate cs1 = State rs1 m1). { inv MAS. simpl. eauto. }
    destruct H as (rs1 & m1 & Hpstate2). subst.
    assert (f = fb). { inv MCS. auto. } subst fb.
    exploit step_simu_header.
      2: eapply MCS.
      all: eauto.
    intros (cs1' & EXEH & MCS2).

    (* step_simu_body part *)
    assert (Hpstate': pstate cs1' = pstate cs1). { inv EXEH; auto. }
    exploit step_simu_body.
      3: eapply BSTEP.
      4: eapply MCS2.
      all: eauto. rewrite Hpstate'. eauto.
    intros (rs2 & m2 & cs2 & ep' & Hcs2 & EXEB & MCS').

    (* step_simu_control part *)
    assert (exists tf, Genv.find_funct_ptr tge f = Some (Internal tf)).
    { exploit functions_translated; eauto. intros (tf & FIND' & TRANSF'). monadInv TRANSF'. eauto. }
    destruct H as (tf & FIND').
    assert (exists tex, pbody2 cs1 = extract_basic tex /\ pctl cs1 = extract_ctl tex).
    { inv MAS. simpl in *. eauto. }
    destruct H as (tex & Hpbody2 & Hpctl).
    inv EXEH. simpl in *.
    subst. exploit step_simu_control.
      9: eapply MCS'. all: simpl.
      10: eapply ESTEP.
      all: simpl; eauto.
      rewrite Hpbody2. rewrite Hpctl.
      { inv MAS; simpl in *. inv Hpstate2. eapply match_asmstate_some; eauto.
        erewrite exec_body_pc; eauto. }
    intros (rs3 & m3 & rs4 & m4 & EXEB' & EXECTL' & MS').

    (* bringing the pieces together *)
    exploit exec_body_trans.
      eapply EXEB.
      eauto.
    intros EXEB2.
    exploit exec_body_control; eauto.
    rewrite <- Hpbody2 in EXEB2. rewrite <- Hbody in EXEB2. eauto.
    rewrite Hexit. rewrite Hpctl. eauto.
    intros EXECB. inv EXECB.
    exists (State rs4 m4).
    split; auto. eapply plus_one. rewrite Hpstate2.
    assert (exists ofs, rs1 PC = Vptr f ofs).
    { rewrite Hpstate2 in MAS. inv MAS. simpl in *. eauto. }
    destruct H0 as (ofs & Hrs1pc).
    eapply exec_step_internal; eauto.

    (* proving the initial find_bblock *)
    rewrite Hpstate2 in MAS. inv MAS. simpl in *. 
    assert (f1 = f0) by congruence. subst f0.
    rewrite PCeq in Hrs1pc. inv Hrs1pc.
    exploit functions_translated; eauto. intros (tf1 & FIND'' & TRANS''). rewrite FIND' in FIND''.
    inv FIND''. monadInv TRANS''. rewrite TRANSF0 in EQ. inv EQ.
    eapply find_bblock_tail; eauto.
Qed.

Theorem step_simulation_bblock:
  forall sf f sp bb ms m ms' m' S2 c,
  body_step ge sf f sp (Machblock.body bb) ms m ms' m' ->
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  exit_step return_address_offset ge (Machblock.exit bb) (Machblock.State sf f sp (bb :: c) ms' m') E0 S2 ->
  forall S1', match_states (Machblock.State sf f sp (bb :: c) ms m) S1' ->
  exists S2' : state, plus step tge S1' E0 S2' /\ match_states S2 S2'.
Proof.
  intros until c. intros BSTEP Hbuiltin ESTEP S1' MS.
  eapply step_simulation_bblock'; eauto.
  all: destruct bb as [hd bdy ex]; simpl in *; eauto.
  inv ESTEP.
  - econstructor. inv H; try (econstructor; eauto; fail).
  - econstructor.
Qed.

(** Dealing now with the builtin case *)

Definition split (c: MB.code) :=
  match c with
  | nil => nil
  | bb::c => {| MB.header := MB.header bb; MB.body := MB.body bb; MB.exit := None |}
              :: {| MB.header := nil; MB.body := nil; MB.exit := MB.exit bb |} :: c
  end.

Lemma cons_ok_eq3 {A: Type} :
  forall (x:A) y z x' y' z',
  x = x' -> y = y' -> z = z' ->
  OK (x::y::z) = OK (x'::y'::z').
Proof.
  intros. subst. auto.
Qed.

Lemma transl_blocks_split_builtin:
  forall bb c ep f ef args res,
  MB.exit bb = Some (MBbuiltin ef args res) -> MB.body bb <> nil ->
  transl_blocks f (split (bb::c)) ep = transl_blocks f (bb::c) ep.
Proof.
  intros until res. intros Hexit Hbody. simpl split.
  unfold transl_blocks. fold transl_blocks. unfold transl_block.
  simpl. remember (transl_basic_code _ _ _) as tbc. remember (transl_instr_control _ _) as tbi.
  remember (transl_blocks _ _ _) as tlbs.
  destruct tbc; destruct tbi; destruct tlbs.
  all: try simpl; auto.
  - simpl. rewrite Hexit in Heqtbi. simpl in Heqtbi. monadInv Heqtbi. simpl.
    unfold gen_bblocks. simpl. destruct l.
    + exploit transl_basic_code_nonil; eauto. intro. destruct H.
    + simpl. rewrite app_nil_r. apply cons_ok_eq3. all: try eapply bblock_equality. all: simpl; auto.
Qed.

Lemma transl_code_at_pc_split_builtin:
  forall rs f f0 bb c ep tf tc ef args res,
  MB.body bb <> nil -> MB.exit bb = Some (MBbuiltin ef args res) ->
  transl_code_at_pc ge (rs PC) f f0 (bb :: c) ep tf tc ->
  transl_code_at_pc ge (rs PC) f f0 (split (bb :: c)) ep tf tc.
Proof.
  intros until res. intros Hbody Hexit AT. inv AT.
  econstructor; eauto. erewrite transl_blocks_split_builtin; eauto.
Qed.

Theorem match_states_split_builtin:
  forall sf f sp bb c rs m ef args res S1,
  MB.body bb <> nil -> MB.exit bb = Some (MBbuiltin ef args res) ->
  match_states (Machblock.State sf f sp (bb :: c) rs m) S1 ->
  match_states (Machblock.State sf f sp (split (bb::c)) rs m) S1.
Proof.
  intros until S1. intros Hbody Hexit MS.
  inv MS.
  econstructor; eauto.
  eapply transl_code_at_pc_split_builtin; eauto.
Qed.

Theorem step_simulation_builtin:
  forall ef args res bb sf f sp c ms m t S2,
  MB.body bb = nil -> MB.exit bb = Some (MBbuiltin ef args res) ->
  exit_step return_address_offset ge (MB.exit bb) (Machblock.State sf f sp (bb :: c) ms m) t S2 ->
  forall S1', match_states (Machblock.State sf f sp (bb :: c) ms m) S1' ->
  exists S2' : state, plus step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros until S2. intros Hbody Hexit ESTEP S1' MS.
  inv MS. inv AT. monadInv H2. monadInv EQ.
  rewrite Hbody in EQ0. monadInv EQ0.
  rewrite Hexit in EQ. monadInv EQ.
  rewrite Hexit in ESTEP. inv ESTEP. inv H4.

  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H1); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  econstructor; split. apply plus_one.
  simpl in H3.
  eapply exec_step_builtin. eauto. eauto.
    eapply find_bblock_tail; eauto.
    simpl. eauto.
    erewrite <- sp_val by eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    eauto.
  econstructor; eauto.
    instantiate (2 := tf); instantiate (1 := x0).
    unfold nextblock, incrPC. rewrite Pregmap.gss.
    rewrite set_res_other. rewrite undef_regs_other_2. rewrite Pregmap.gso by congruence. 
    rewrite <- H. simpl. econstructor; eauto.
    eapply code_tail_next_int; eauto.
    rewrite preg_notin_charact. intros. auto with asmgen.
    auto with asmgen.
    apply agree_nextblock. eapply agree_set_res; auto.
    eapply agree_undef_regs; eauto. intros. rewrite undef_regs_other_2; auto.
    apply Pregmap.gso; auto with asmgen.
    congruence.
Qed.

Lemma next_sep:
  forall rs m rs' m', rs = rs' -> m = m' -> Next rs m = Next rs' m'.
Proof.
  congruence.
Qed.

(* Measure to prove finite stuttering, see the other backends *)
Definition measure (s: MB.state) : nat :=
  match s with
  | MB.State _ _ _ _ _ _ => 0%nat
  | MB.Callstate _ _ _ _ => 0%nat
  | MB.Returnstate _ _ _ => 1%nat
  end.

(* The actual MB.step/AB.step simulation, using the above theorems, plus extra proofs
   for the internal and external function cases *)
Theorem step_simulation:
  forall S1 t S2, MB.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros.

- (* bblock *)
  left. destruct (Machblock.exit bb) eqn:MBE; try destruct c0.
  all: try(inversion H0; subst; inv H2; eapply step_simulation_bblock; 
            try (rewrite MBE; try discriminate); eauto).
  + (* MBbuiltin *)
    destruct (MB.body bb) eqn:MBB.
    * inv H. eapply step_simulation_builtin; eauto. rewrite MBE. eauto.
    * eapply match_states_split_builtin in MS; eauto.
        2: rewrite MBB; discriminate.
      simpl split in MS.
      rewrite <- MBB in H.
      remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb1.
      assert (MB.body bb = MB.body bb1). { subst. simpl. auto. }
      rewrite H1 in H. subst.
      exploit step_simulation_bblock. eapply H.
        discriminate.
        simpl. constructor.
        eauto.
      intros (S2' & PLUS1 & MS').
      rewrite MBE in MS'.
      assert (exit_step return_address_offset ge (Some (MBbuiltin e l b)) 
              (MB.State sf f sp ({| MB.header := nil; MB.body := nil; MB.exit := Some (MBbuiltin e l b) |}::c) 
                rs' m') t s').
      { inv H0. inv H3. econstructor. econstructor; eauto. }
      exploit step_simulation_builtin.
        4: eapply MS'.
        all: simpl; eauto.
      intros (S3' & PLUS'' & MS'').
      exists S3'. split; eauto.
      eapply plus_trans. eapply PLUS1. eapply PLUS''. eauto.
  + inversion H0. subst. eapply step_simulation_bblock; try (rewrite MBE; try discriminate); eauto.

- (* internal function *)
  inv MS.
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (size_blocks x0.(fn_blocks))); inversion EQ1. clear EQ1. subst x0.
  unfold Mach.store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  simpl chunk_of_type in F.
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0.
  set (tfbody := make_prologue f x0) in *.
  set (tf := {| fn_sig := MB.fn_sig f; fn_blocks := tfbody |}) in *.
  set (rs2 := rs0#FP <- (parent_sp s) #SP <- sp #RTMP <- Vundef).
  exploit (Pget_correct tge GPRA RA nil rs2 m2'); auto.
  intros (rs' & U' & V').
  exploit (storeind_ptr_correct tge SP (fn_retaddr_ofs f) GPRA nil rs' m2').
  { rewrite chunk_of_Tptr in P.
    assert (rs' GPRA = rs0 RA). { apply V'. }
    assert (rs' SP = rs2 SP). { apply V'; discriminate. }
    rewrite H4. rewrite H3.
    rewrite ATLR.
    change (rs2 SP) with sp. eexact P. }
  intros (rs3 & U & V).
  assert (EXEC_PROLOGUE: exists rs3',
            exec_straight_blocks tge tf
              tf.(fn_blocks) rs0 m'
              x0 rs3' m3'
          /\ forall r, r <> PC -> rs3' r = rs3 r).
  { eexists. split.
    - change (fn_blocks tf) with tfbody; unfold tfbody.
      econstructor; eauto. unfold exec_bblock. simpl exec_body.
      rewrite C. fold sp. rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. simpl in F. rewrite F.
      Simpl. unfold parexec_store_offset. rewrite Ptrofs.of_int64_to_int64. unfold eval_offset.
      rewrite chunk_of_Tptr in P. Simpl. rewrite ATLR. unfold Mptr in P. assert (Archi.ptr64 = true) by auto. 2: auto. rewrite H3 in P. rewrite P.
      simpl. apply next_sep; eauto. reflexivity.
    - intros. destruct V' as (V'' & V'). destruct r.
      + Simpl.
        destruct (gpreg_eq g0 GPR16). { subst. Simpl. rewrite V; try discriminate. rewrite V''. subst rs2. Simpl. }
        destruct (gpreg_eq g0 GPR32). { subst. Simpl. rewrite V; try discriminate. rewrite V'; try discriminate. subst rs2. Simpl. }
        destruct (gpreg_eq g0 GPR12). { subst. Simpl. rewrite V; try discriminate. rewrite V'; try discriminate. subst rs2. Simpl. }
        destruct (gpreg_eq g0 GPR17). { subst. Simpl. rewrite V; try discriminate. rewrite V'; try discriminate. subst rs2. Simpl. }
        Simpl. rewrite V; try discriminate. rewrite V'; try discriminate. subst rs2. Simpl. { destruct g0; try discriminate. contradiction. }
      + Simpl. rewrite V; try discriminate. rewrite V'; try discriminate. subst rs2. Simpl.
      + contradiction.
  } destruct EXEC_PROLOGUE as (rs3' & EXEC_PROLOGUE & Heqrs3').
  exploit exec_straight_steps_2; eauto using functions_transl.
  simpl fn_blocks. simpl fn_blocks in g. omega. constructor.
  intros (ofs' & X & Y).                    
  left; exists (State rs3' m3'); split.
  eapply exec_straight_steps_1; eauto.
  simpl fn_blocks. simpl fn_blocks in g. omega.
  constructor.
  econstructor; eauto.
  rewrite X; econstructor; eauto. 
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2. 
  apply agree_set_other; auto with asmgen.
  apply agree_change_sp with (parent_sp s). 
  apply agree_undef_regs with rs0. auto.
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.

  intros.
  assert (r <> RTMP). { contradict H3; rewrite H3; unfold data_preg; auto. }
  rewrite Heqrs3'. Simpl. rewrite V. inversion V'. rewrite H6. auto.
  assert (r <> GPRA). { contradict H3; rewrite H3; unfold data_preg; auto. }
  assert (forall r : preg, r <> PC -> r <> GPRA -> rs' r = rs2 r). { apply V'. }
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  intros. rewrite Heqrs3'. rewrite V by auto with asmgen.
  assert (forall r : preg, r <> PC -> r <> GPRA -> rs' r = rs2 r). { apply V'. }
  rewrite H4 by auto with asmgen. reflexivity. discriminate.

- (* external function *)
  inv MS.
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  unfold loc_external_result.
  apply agree_set_other; auto.
  apply agree_set_pair; auto.
  apply agree_undef_caller_save_regs; auto.

- (* return *) 
  inv MS.
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  rewrite <- ATPC in H5.
  econstructor; eauto. congruence.
Qed.

Lemma transf_initial_states:
  forall st1, MB.initial_state prog st1 ->
  exists st2, AB.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. unfold Vnullptr; destruct Archi.ptr64; congruence.
  intros. rewrite Mach.Regmap.gi. auto.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> MB.final_state st1 r -> AB.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. assumption.
  compute in H1. inv H1.
  generalize (preg_val _ _ _ R0 AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Definition return_address_offset : Machblock.function -> Machblock.code -> ptrofs -> Prop := 
  Asmblockgenproof0.return_address_offset.

Theorem transf_program_correct:
  forward_simulation (MB.semantics return_address_offset prog) (Asmblock.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - exact step_simulation.
Qed.

End PRESERVATION.
