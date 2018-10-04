(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for RISC-V generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Machblock Conventions Asmblock.
(* Require Import Asmgen Asmgenproof0 Asmgenproof1. *)
Require Import Asmblockgen Asmblockgenproof0 Asmblockgenproof1.

Module MB := Machblock.
Module AB := Asmblock.

Definition match_prog (p: Machblock.program) (tp: Asmblock.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Machblock.program.
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
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (size_blocks x.(fn_blocks))); inv EQ0.
  omega.
Qed.

(*
Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.
 *)
(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

(* Remark loadimm32_label:
  forall r n k, tail_nolabel k (loadimm32 r n k).
Proof.
  intros; unfold loadimm32. destruct (make_immed32 n); TailNoLabel.
(*unfold load_hilo32. destruct (Int.eq lo Int.zero); TailNoLabel.*)
Qed.
Hint Resolve loadimm32_label: labels.

Remark opimm32_label:
  forall (op: arith_name_rrr) (opimm: arith_name_rri32) r1 r2 n k,
  (forall r1 r2 r3, nolabel (op r1 r2 r3)) ->
  (forall r1 r2 n, nolabel (opimm r1 r2 n)) ->
  tail_nolabel k (opimm32 op opimm r1 r2 n k).
Proof.
  intros; unfold opimm32. destruct (make_immed32 n); TailNoLabel.
(*unfold load_hilo32. destruct (Int.eq lo Int.zero); TailNoLabel.*)
Qed.
Hint Resolve opimm32_label: labels.

Remark loadimm64_label:
  forall r n k, tail_nolabel k (loadimm64 r n k).
Proof.
  intros; unfold loadimm64. destruct (make_immed64 n); TailNoLabel.
(*unfold load_hilo64. destruct (Int64.eq lo Int64.zero); TailNoLabel.*)
Qed.
Hint Resolve loadimm64_label: labels.

Remark cast32signed_label:
  forall rd rs k, tail_nolabel k (cast32signed rd rs k).
Proof.
  intros; unfold cast32signed. destruct (ireg_eq rd rs); TailNoLabel.
Qed.
Hint Resolve cast32signed_label: labels.

Remark opimm64_label:
  forall (op: arith_name_rrr) (opimm: arith_name_rri64) r1 r2 n k,
  (forall r1 r2 r3, nolabel (op r1 r2 r3)) ->
  (forall r1 r2 n, nolabel (opimm r1 r2 n)) ->
  tail_nolabel k (opimm64 op opimm r1 r2 n k).
Proof.
  intros; unfold opimm64. destruct (make_immed64 n); TailNoLabel.
(*unfold load_hilo64. destruct (Int64.eq lo Int64.zero); TailNoLabel.*)
Qed.
Hint Resolve opimm64_label: labels.

Remark addptrofs_label:
  forall r1 r2 n k, tail_nolabel k (addptrofs r1 r2 n k).
Proof.
  unfold addptrofs; intros. destruct (Ptrofs.eq_dec n Ptrofs.zero). TailNoLabel.
  apply opimm64_label; TailNoLabel.
Qed.
Hint Resolve addptrofs_label: labels.
(*
Remark transl_cond_float_nolabel:
  forall c r1 r2 r3 insn normal,
  transl_cond_float c r1 r2 r3 = (insn, normal) -> nolabel insn.
Proof.
  unfold transl_cond_float; intros. destruct c; inv H; exact I.
Qed.

Remark transl_cond_single_nolabel:
  forall c r1 r2 r3 insn normal,
  transl_cond_single c r1 r2 r3 = (insn, normal) -> nolabel insn.
Proof.
  unfold transl_cond_single; intros. destruct c; inv H; exact I.
Qed.
*)
Remark transl_cbranch_label:
  forall cond args lbl k c,
  transl_cbranch cond args lbl k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cbranch in H. destruct cond; TailNoLabel.
(* Ccomp *)
  - unfold transl_comp; TailNoLabel.
(* Ccompu *)
  - unfold transl_comp; TailNoLabel.
(* Ccompimm *)
  - destruct (Int.eq n Int.zero); TailNoLabel.
    unfold loadimm32. destruct (make_immed32 n); TailNoLabel. unfold transl_comp; TailNoLabel.
(* Ccompuimm *)
  - unfold transl_opt_compuimm.
    remember (select_comp n c0) as selcomp; destruct selcomp.
    + destruct c; TailNoLabel; contradict Heqselcomp; unfold select_comp;
      destruct (Int.eq n Int.zero); destruct c0; discriminate.
    + unfold loadimm32;
      destruct (make_immed32 n); TailNoLabel; unfold transl_comp; TailNoLabel.
(* Ccompl *)
  - unfold transl_compl; TailNoLabel.
(* Ccomplu *)
  - unfold transl_compl; TailNoLabel.
(* Ccomplimm *)
  - destruct (Int64.eq n Int64.zero); TailNoLabel.
    unfold loadimm64. destruct (make_immed64 n); TailNoLabel. unfold transl_compl; TailNoLabel.
(* Ccompluimm *)
  - unfold transl_opt_compluimm.
    remember (select_compl n c0) as selcomp; destruct selcomp.
    + destruct c; TailNoLabel; contradict Heqselcomp; unfold select_compl;
      destruct (Int64.eq n Int64.zero); destruct c0; discriminate.
    + unfold loadimm64;
      destruct (make_immed64 n); TailNoLabel; unfold transl_compl; TailNoLabel.
Qed.

(*
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct (Int.eq n Int.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int32s c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (Int.eq n Int.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int32u c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct (Int64.eq n Int64.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int64s c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (Int64.eq n Int64.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int64u c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto. 
  destruct normal; TailNoLabel.
*)

Remark transl_cond_op_label:
  forall cond args r k c,
  transl_cond_op cond r args k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cond_op in H; destruct cond; TailNoLabel.
- unfold transl_cond_int32s; destruct c0; simpl; TailNoLabel.
- unfold transl_cond_int32u; destruct c0; simpl; TailNoLabel. 
- unfold transl_condimm_int32s; destruct c0; simpl; TailNoLabel.
- unfold transl_condimm_int32u; destruct c0; simpl; TailNoLabel.
- unfold transl_cond_int64s; destruct c0; simpl; TailNoLabel.
- unfold transl_cond_int64u; destruct c0; simpl; TailNoLabel. 
- unfold transl_condimm_int64s; destruct c0; simpl; TailNoLabel.
- unfold transl_condimm_int64u; destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c -> tail_nolabel k c.
Proof.
Opaque Int.eq.
  unfold transl_op; intros; destruct op; TailNoLabel.
(* Omove *)
- destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
(* Oaddrsymbol *)
- destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)); TailNoLabel.
(* Oaddimm32 *)
- apply opimm32_label; intros; exact I.
(* Oandimm32 *)
- apply opimm32_label; intros; exact I.
(* Oorimm32 *)
- apply opimm32_label; intros; exact I.
(* Oxorimm32 *)
- apply opimm32_label; intros; exact I.
(* Oshrximm *)
- destruct (Int.eq n Int.zero); TailNoLabel.
(* Oaddimm64 *)
- apply opimm64_label; intros; exact I.
(* Oandimm64  *)
- apply opimm64_label; intros; exact I.
(* Oorimm64  *)
- apply opimm64_label; intros; exact I.
(* Oxorimm64  *)
- apply opimm64_label; intros; exact I.
(* Ocmp *)
- eapply transl_cond_op_label; eauto.
Qed.

(*
- destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
- destruct (Float.eq_dec n Float.zero); TailNoLabel.
- destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
- destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)).
+ eapply tail_nolabel_trans; [|apply addptrofs_label]. TailNoLabel.
+ TailNoLabel. 
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- destruct (Int.eq n Int.zero); TailNoLabel.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- destruct (Int.eq n Int.zero); TailNoLabel.
- eapply transl_cond_op_label; eauto.
*)

Remark indexed_memory_access_label:
  forall (mk_instr: ireg -> offset -> instruction) base ofs k,
  (forall r o, nolabel (mk_instr r o)) ->
  tail_nolabel k (indexed_memory_access mk_instr base ofs k).
Proof.
  unfold indexed_memory_access; intros. 
  (* destruct Archi.ptr64. *)
  destruct (make_immed64 (Ptrofs.to_int64 ofs)); TailNoLabel.
  (* destruct (make_immed32 (Ptrofs.to_int ofs)); TailNoLabel. *)
Qed.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c -> tail_nolabel k c.
Proof.
  unfold loadind; intros.
  destruct ty, (preg_of dst); inv H; apply indexed_memory_access_label; intros; exact I.
Qed.

Remark storeind_label:
  forall src base ofs ty k c,
  storeind src base ofs ty k = OK c -> tail_nolabel k c.
Proof.
  unfold storeind; intros.
  destruct ty, (preg_of src); inv H; apply indexed_memory_access_label; intros; exact I.
Qed.

Remark loadind_ptr_label:
  forall base ofs dst k, tail_nolabel k (loadind_ptr base ofs dst k).
Proof.
  intros. apply indexed_memory_access_label. intros; destruct Archi.ptr64; exact I.
Qed.

Remark storeind_ptr_label:
  forall src base ofs k, tail_nolabel k (storeind_ptr src base ofs k).
Proof.
  intros. apply indexed_memory_access_label. intros; destruct Archi.ptr64; exact I.
Qed.

Remark transl_memory_access_label:
  forall (mk_instr: ireg -> offset -> instruction) addr args k c,
  (forall r o, nolabel (mk_instr r o)) ->
  transl_memory_access mk_instr addr args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_memory_access; intros; destruct addr; TailNoLabel; apply indexed_memory_access_label; auto. 
Qed.

Remark make_epilogue_label:
  forall f k, tail_nolabel k (make_epilogue f k).
Proof.
  unfold make_epilogue; intros. eapply tail_nolabel_trans. apply loadind_ptr_label. TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl ::i k | _ => tail_nolabel k c end.
Proof.
  unfold transl_instr; intros; destruct i; TailNoLabel.
(* loadind *)
- eapply loadind_label; eauto.
(* storeind *)
- eapply storeind_label; eauto.
(* Mgetparam *)
- destruct ep. eapply loadind_label; eauto.
  eapply tail_nolabel_trans. apply loadind_ptr_label. eapply loadind_label; eauto. 
(* transl_op *)
- eapply transl_op_label; eauto.
(* transl_load *)
- destruct m; monadInv H; eapply transl_memory_access_label; eauto; intros; exact I.
(* transl store *)
- destruct m; monadInv H; eapply transl_memory_access_label; eauto; intros; exact I.
- destruct s0; monadInv H; TailNoLabel.
- destruct s0; monadInv H; eapply tail_nolabel_trans
  ; [eapply make_epilogue_label|TailNoLabel].
- eapply transl_cbranch_label; eauto.
- eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel].
Qed.
(*


- eapply transl_op_label; eauto.
- destruct m; monadInv H; eapply transl_memory_access_label; eauto; intros; exact I.
- destruct m; monadInv H; eapply transl_memory_access_label; eauto; intros; exact I.
- destruct s0; monadInv H; (eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel]).
- eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel].
*)

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0. unfold fn_code. 
  simpl. destruct (storeind_ptr_label GPR8 GPR12 (fn_retaddr_ofs f) x) as [A B]. 
  (* destruct B. *)
  eapply transl_code_label; eauto.
Qed.
 *)
End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated Asm code. *)

(* Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.
*)

(** Existence of return addresses *)

(* NB: the hypothesis in comment on [b] is not needed in the proof ! 
*)
Lemma return_address_exists:
  forall b f (* sg ros *) c, (* b.(MB.exit) = Some (MBcall sg ros) -> *) is_tail (b :: c) f.(MB.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmblockgenproof0.return_address_exists; eauto.
  - intros f0 tf H0. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (size_blocks x.(fn_blocks))); inv EQ0.
  monadInv EQ. simpl.
  eapply ex_intro; constructor 1; eauto with coqlib.
  - exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The Asm code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and Asm register values agree.
*)

(*
Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#FP = parent_sp s)) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.
*)

(*
Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

Lemma exec_straight_opt_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  inv A.
- exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
- exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed. *)

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the Asm side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Machsem.Returnstate] to [Machsem.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

(* 
Remark preg_of_not_FP: forall r, negb (mreg_eq r R10) = true -> IR FP <> preg_of r.
Proof.
  intros. change (IR FP) with (preg_of R10). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed. *)

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)
(* 
Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto with asmgen. congruence.
  simpl; congruence.


- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  inversion TR.
  exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; intros. rewrite Q; auto with asmgen.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
(* Opaque loadind. *)
  left; eapply exec_straight_steps; eauto; intros. monadInv TR.
  destruct ep.
(* GPR31 contains parent *)
  exploit loadind_correct. eexact EQ.
  instantiate (2 := rs0). rewrite DXP; eauto. congruence.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
  simpl; intros. rewrite R; auto with asmgen.
  apply preg_of_not_FP; auto.
(* GPR11 does not contain parent *)
  rewrite chunk_of_Tptr in A. 
  exploit loadind_ptr_correct. eexact A. congruence. intros [rs1 [P [Q R]]].
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto. congruence.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
  instantiate (1 := rs1#FP <- (rs2#FP)). intros.
  rewrite Pregmap.gso; auto with asmgen.
  congruence.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' FP). congruence. auto with asmgen.
  simpl; intros. rewrite U; auto with asmgen.
  apply preg_of_not_FP; auto.
- (* Mop *)
  assert (eval_operation tge sp op (map rs args) m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split. auto.
  apply agree_set_undef_mreg with rs0; auto. 
  apply Val.lessdef_trans with v'; auto.
  simpl; intros. destruct (andb_prop _ _ H1); clear H1.
  rewrite R; auto. apply preg_of_not_FP; auto.
Local Transparent destroyed_by_op.
  destruct op; simpl; auto; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  inversion TR.
  exploit transl_load_correct; eauto.
  intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen.
  simpl; congruence.


- (* Mstore *)
  assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR.
  inversion TR.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; congruence.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
(*
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. Simpl. rewrite <- H2; simpl; eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl.
  Simpl. rewrite <- H2. auto.
*)
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl.
  Simpl. rewrite <- H2. auto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
(*
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z). 
  exploit exec_straight_steps_2; eauto using functions_transl.                      
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.
  Simpl. rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen). assumption. 
*)
+ (* Direct call *)
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z). 
  exploit exec_straight_steps_2; eauto using functions_transl.                      
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  { apply agree_set_other.
    - econstructor; auto with asmgen.
      + apply V.
      + intro r. destruct r; apply V; auto.
    - eauto with asmgen. }
  { Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto. }

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr. rewrite Pregmap.gss.
  rewrite set_res_other. rewrite undef_regs_other_2. rewrite Pregmap.gso by congruence. 
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  apply agree_nextinstr. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros. rewrite undef_regs_other_2; auto. apply Pregmap.gso; auto with asmgen.
  congruence.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.
- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_opt_steps_goto; eauto.
  intros. simpl in TR.
  inversion TR.
  exploit transl_cbranch_correct_true; eauto. intros (rs' & jmp & A & B & C).
  exists jmp; exists k; exists rs'.
  split. eexact A. 
  split. apply agree_exten with rs0; auto with asmgen.
  exact B. 
- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  inversion TR.
  exploit transl_cbranch_correct_false; eauto. intros (rs' & A & B).
  exists rs'.
  split. eexact A.
  split. apply agree_exten with rs0; auto with asmgen.
  simpl. congruence.
- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
(*
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label. eauto. eauto.
  instantiate (2 := rs0#X5 <- Vundef #X31 <- Vundef).
  Simpl. eauto.
  eauto.
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto.
  eapply agree_undef_regs; eauto.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.
*)
- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inversion AT; subst. simpl in H6; monadInv H6.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  exploit make_epilogue_correct; eauto. intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.                      
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x0.(fn_code))); inversion EQ1. clear EQ1. subst x0.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  simpl chunk_of_type in F.
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  set (tfbody := Pallocframe (fn_stacksize f) (fn_link_ofs f) ::i
                 Pget GPR8 RA ::i
                 storeind_ptr GPR8 SP (fn_retaddr_ofs f) x0) in *.
  set (tf := {| fn_sig := Mach.fn_sig f; fn_code := tfbody |}) in *.
  set (rs2 := nextinstr (rs0#FP <- (parent_sp s) #SP <- sp #GPR31 <- Vundef)).
  exploit (Pget_correct tge tf GPR8 RA (storeind_ptr GPR8 SP (fn_retaddr_ofs f) x0) rs2 m2'); auto.
  intros (rs' & U' & V').
  exploit (storeind_ptr_correct tge tf SP (fn_retaddr_ofs f) GPR8 x0 rs' m2').
    rewrite chunk_of_Tptr in P.
    assert (rs' GPR8 = rs0 RA). { apply V'. }
    assert (rs' GPR12 = rs2 GPR12). { apply V'; discriminate. }
    rewrite H3. rewrite H4.
    (* change (rs' GPR8) with (rs0 RA). *)
    rewrite ATLR.
    change (rs2 GPR12) with sp. eexact P.
    congruence. congruence.
  intros (rs3 & U & V).
  assert (EXEC_PROLOGUE:
            exec_straight tge tf
              tf.(fn_code) rs0 m'
              x0 rs3 m3').
  { change (fn_code tf) with tfbody; unfold tfbody.
    apply exec_straight_step with rs2 m2'.
    unfold exec_instr. rewrite C. fold sp.
    rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. rewrite F. reflexivity.
    reflexivity.
    eapply exec_straight_trans.
    - eexact U'.
    - eexact U. }
  exploit exec_straight_steps_2; eauto using functions_transl. omega. constructor.
  intros (ofs' & X & Y).                    
  left; exists (State rs3 m3'); split.
  eapply exec_straight_steps_1; eauto. omega. constructor.
  econstructor; eauto.
  rewrite X; econstructor; eauto. 
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2. 
  apply agree_nextinstr. apply agree_set_other; auto with asmgen.
  apply agree_change_sp with (parent_sp s). 
  apply agree_undef_regs with rs0. auto.
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.

  intros.
  assert (r <> GPR31). { contradict H3; rewrite H3; unfold data_preg; auto. }
  rewrite V.
  assert (r <> GPR8). { contradict H3; rewrite H3; unfold data_preg; auto. }
  assert (forall r : preg, r <> PC -> r <> GPR8 -> rs' r = rs2 r). { apply V'. }
  rewrite H6; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  intros. rewrite V by auto with asmgen.
  assert (forall r : preg, r <> PC -> r <> GPR8 -> rs' r = rs2 r). { apply V'. }
  rewrite H4 by auto with asmgen. reflexivity.

- (* external function *)
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
  apply agree_set_other; auto. apply agree_set_pair; auto.

- (* return *)
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  rewrite <- ATPC in H5.
  econstructor; eauto. congruence.
Qed.
*)

Inductive match_states: Machblock.state -> Asmblock.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#FP = parent_sp s),
      match_states (Machblock.State s fb sp c ms m)
                   (Asmblock.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Machblock.Callstate s fb ms m)
                   (Asmblock.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Machblock.Returnstate s ms m)
                   (Asmblock.State rs m').

Inductive codestate: Type :=
  | Codestate: state -> list AB.bblock -> codestate.

Inductive match_codestate fb: Machblock.state -> codestate -> Prop :=
  | match_codestate_intro:
      forall s sp ms m m' rs f tc ep c
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (TRANS: transl_blocks f c = OK tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#FP = parent_sp s),
      match_codestate fb (Machblock.State s fb sp c ms m)
                   (Codestate (Asmblock.State rs m') tc)
  | match_codestate_call:
      forall s ms m m' rs tc
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_codestate fb (Machblock.Callstate s fb ms m)
                            (Codestate (Asmblock.State rs m') tc)
  | match_codestate_return:
      forall s ms m m' rs tc
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_codestate fb (Machblock.Returnstate s ms m)
                       (Codestate (Asmblock.State rs m') tc).

Inductive match_asmblock fb: codestate -> Asmblock.state -> Prop :=
  | match_asmblock_intro:
      forall rs f tf tc m ep c
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc),
      match_asmblock fb (Codestate (Asmblock.State rs m) tc) (Asmblock.State rs m)
.

Theorem match_codestate_state:
  forall mbs abs fb cs,
  match_codestate fb mbs cs ->
  match_asmblock fb cs abs ->
  match_states mbs abs.
Proof.
  intros until cs. intros MCS MAB.
  inv MCS.
  - inv MAB. rewrite FIND0 in FIND. inv FIND.
    econstructor; eauto. inv AT. econstructor; eauto.
  - inv MAB. econstructor; eauto.
  - inv MAB. econstructor; eauto.
Qed.

Theorem match_state_codestate:
  forall mbs abs s fb sp c ms m rs m' tc tf ep f,
  mbs = (Machblock.State s fb sp c ms m) ->
  abs = (Asmblock.State rs m') ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_blocks f c = OK tc ->
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  match_states mbs abs ->
  exists cs, (match_codestate fb mbs cs /\ match_asmblock fb cs abs 
              /\ cs = (Codestate (Asmblock.State rs m') tc)).
Proof.
  intros. inv H4; try discriminate.
  inv H6. inv H5. rewrite FIND in H1. inv H1.
  esplit. repeat split.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Definition measure (s: MB.state) : nat :=
  match s with
  | MB.State _ _ _ _ _ _ => 0%nat
  | MB.Callstate _ _ _ _ => 0%nat
  | MB.Returnstate _ _ _ => 1%nat
  end.

Axiom TODO: False.

Definition remove_body (bb: MB.bblock) := {| MB.header := MB.header bb; MB.body := nil; MB.exit := MB.exit bb |}.

Lemma remove_body_id : forall bb, MB.body bb = nil -> remove_body bb = bb.
Proof.
  intros. destruct bb as [hd bdy ex]. simpl in *. subst. auto.
Qed.

(* To be expanded later based on what we need for step_simu_control *)
Inductive control_preserved : state -> state -> Prop :=
  | control_pres_intro: 
      forall rs rs' m m', rs PC = rs' PC -> control_preserved (State rs m) (State rs' m').

Lemma step_simu_body:
  forall sf f sp bb bb' ms m ms' m' rs0 m0 s' c tc tbb,
  body_step ge sf f sp (MB.body bb) ms m ms' m' ->
  bb' = remove_body bb ->
  s' = (Machblock.State sf f sp (bb' :: c) ms' m') ->
  match_codestate f (Machblock.State sf f sp (bb::c) ms m) (Codestate (State rs0 m0) tc) ->
  exists S1'' rs1 m1,
     S1'' = (Codestate (Asmblock.State rs1 m1) tc)
  /\ exec_body tge (body tbb) rs0 m0 = Next rs1 m1
  /\ match_codestate f s' S1''
  /\ exists tbb' tc', tc = tbb' :: tc'
  /\ control_preserved (State rs0 m0) (State rs1 m1)
.
Proof.
Admitted.

Lemma transl_blocks_distrib:
  forall f bb c tbb tc ef args res,
  transl_blocks f (bb::c) = OK (tbb::tc)
  -> MB.exit bb <> Some (MBbuiltin ef args res)
  -> transl_block f bb = OK (tbb :: nil)
  /\ transl_blocks f c = OK tc.
Proof.
Admitted.

Lemma transl_basic_code_length :
  forall f bdy tbdy,
  transl_basic_code' f bdy true = OK tbdy -> length bdy = length tbdy.
Proof.
Admitted.

(** TODO - factoriser la preuve du exit=None en introduisant des lemmes *)
Lemma step_simu_control:
  forall S0 bb bb' f tf f0 sf sp c ms' m' rs1 m1 tbb' tbb tc tc' rs0 m'0 t s'' ep ms
  (AT: transl_code_at_pc ge (rs0 PC) f f0 (bb::c) ep tf (tbb :: tc'))
  (DXP: ep = true -> rs0 GPR10 = parent_sp sf)
  (AG : agree ms sp rs0),
  bb' = remove_body bb ->
  S0 = (State rs0 m'0) ->
  exec_body tge (body tbb) rs0 m'0 = Next rs1 m1 ->
  match_codestate f (Machblock.State sf f sp (bb' :: c) ms' m') 
    (Codestate (State rs1 m1) (tbb' :: tc)) ->
(*   match_asmblock f (Codestate S0 (tbb::tc)) (State rs0 m'0) -> *)
  control_preserved S0 (State rs1 m1) ->
  exit_step return_address_offset ge (MB.exit bb') 
    (Machblock.State sf f sp (bb'::c) ms' m') t s'' ->
  exists rs2 m2,
     exec_control tge tf (exit tbb') (nextblock tbb rs1) m1 = Next rs2 m2
  /\ match_codestate f s'' (Codestate (State rs2 m2) tc)
  /\ match_asmblock f (Codestate (State rs2 m2) tc) (State rs2 m2)
  /\ plus step tge S0 t (State rs2 m2).
Proof.
  intros until ms. intros AT DXP AG. intros H20 H21. intros EBDY MCS (* MAB *) CP ESTEP.
  (* destruct tbb as [thd tbdy tex]. destruct bb as [hd bdy ex]. destruct bb' as [hd' bdy' ex']. *) simpl in *.
  inv CP. inv H0.
  inv ESTEP. 
  - destruct TODO.
  - inv MCS. destruct bb as [hd bdy ex]; simpl in *. subst. eapply transl_blocks_distrib in TRANS; [| simpl; discriminate].
    destruct TRANS as (TRANS1 & TRANS2). monadInv TRANS1.
    inv EQ1. inv EQ. unfold gen_bblocks in H0; simpl in H0. inv H0.
  esplit; esplit. esplit. 2: esplit. 3: esplit.
    + simpl; auto.
    + econstructor; eauto. inv AG0. econstructor; eauto. intro. Simpl.
    + inv AT. econstructor; eauto. unfold nextblock; unfold size; simpl.
      destruct tbb as [thd tbdy tex]; simpl.
      eapply transl_blocks_distrib in H3. destruct H3 as (H31 & H32). monadInv H31. simpl in EQ. simpl in EQ1.
      inv EQ1. inv H5. 2: simpl; discriminate.
      simpl. rewrite FIND in H0. inv H0. rewrite H32 in TRANS2. inv TRANS2.
      destruct bdy as [|i bdy].
      * inv EQ. Simpl. rewrite <- H1. rewrite <- H. econstructor; eauto.
        assert (H42: size {| header := thd; body := nil; exit := None |} = 1) by (simpl; auto).
        rewrite <- H42. eapply code_tail_next_int. 
        eapply transf_function_no_overflow; eauto.
        eauto.
      * apply transl_basic_code_length in EQ. destruct tbdy as [|i' tbdy]. simpl in EQ. discriminate.
        Simpl. rewrite <- H1. rewrite <- H. econstructor; eauto.
        assert (H42: size {| header := thd; body := i' ::i tbdy; exit := None |} = Z.of_nat (length (i' ::i tbdy))).
          unfold size; simpl; auto. rewrite Nat.add_0_r. auto.
        rewrite Nat.add_0_r. rewrite <- H42. eapply code_tail_next_int.
        eapply transf_function_no_overflow; eauto.
        eauto.
    + apply plus_one. inv AT. econstructor; eauto. eapply functions_transl; eauto.
      eapply find_bblock_tail; eauto.
      unfold exec_bblock. rewrite EBDY.
      eapply transl_blocks_distrib in H3; [|simpl; discriminate]. destruct H3 as [H31 H32].
      destruct tbb as [thd tbdy tex]; simpl in H31. monadInv H31. simpl. inv EQ1. inv EQ. inv H5. simpl. auto.
Unshelve.
  all: destruct TODO.
Qed.

(* Alternative form of step_simulation_bblock, easier to prove *)
Lemma step_simulation_bblock':
  forall sf f sp bb bb' rs m rs' m' t s'' c S1,
  body_step ge sf f sp (Machblock.body bb) rs m rs' m' ->
  bb' = remove_body bb ->
  exit_step return_address_offset ge (Machblock.exit bb') (Machblock.State sf f sp (bb' :: c) rs' m') t s'' ->
  match_states (Machblock.State sf f sp (bb :: c) rs m) S1 ->
  exists S2 : state, plus step tge S1 t S2 /\ match_states s'' S2.
Proof.
  intros. inversion H2. subst.
  remember (Machblock.State sf f sp (bb::c) rs m) as mbs. 
  remember (State rs0 m'0) as abs.
  exploit match_state_codestate; eauto. inv AT. auto.
  intros (S1' & MCS & MAS & cseq). subst.
  exploit step_simu_body; eauto.
  intros (S1'' & rs1 & m1 & S1''eq & EBD & MCS' & tbb' & tc' & tceq & PRES).
  subst. exploit step_simu_control; eauto.
Admitted. (* TODO - fix the proof with the new step_simulation_control *)
(*   eauto. 
  intros (rs2 & m2 & EBB & MCS'' & MAB' & PSTEP). subst.
  exists (State rs2 m2). split; auto.
  eapply match_codestate_state; eauto.
Unshelve.
  destruct TODO.
Qed.
 *)

(* Previous attempt at simulation_control and simulation_body

Lemma step_simulation_control:
  forall (bb: Machblock.bblock) sf f sp bb c rs' m' t s' (S1' S2': state),
  exit_step return_address_offset ge (Machblock.exit bb) (Machblock.State sf f sp (bb::c) rs' m') t s' ->
  match_states (Machblock.State sf f sp (bb :: c) rs' m') S1' ->
  exists S2' : state, plus step tge S1' t S2' /\ match_states s' S2'.
Proof.
Admitted.

Lemma step_simulation_body:
  forall body hd sf f sp bb bb' rs m rs' m' (S1' S2': state) s' t c,
  body <> nil ->
  bb = {| MB.header := hd; MB.body := body; MB.exit := None |} ->
  body_step ge sf f sp body rs m rs' m' ->
  bb' = remove_body bb ->
  s' = (Machblock.State sf f sp (bb' :: c) rs' m') ->
  match_states (Machblock.State sf f sp (bb::c) rs m) S1' ->
  exists S2': state, step tge S1' t S2' /\ match_states s' S2' /\ t=E0.
Proof.
  induction body as [|bi body].
  - intros. contradict H; simpl; auto.
  - intros. destruct body as [|bi' body].
    + clear IHbody H.
      destruct TODO. (* proof of individual instructions *)
    + inv H1.
      exploit IHbody. eauto. discriminate. 2: eapply H12. eauto. eauto.
      (* 2: eapply H4. *)
Admitted.

(* Alternative form of step_simulation_bblock, easier to prove *)
Lemma step_simulation_bblock':
  forall sf f sp bb bb' rs m rs' m' t S1' s' c,
  body_step ge sf f sp (Machblock.body bb) rs m rs' m' ->
  bb' = remove_body bb ->
  exit_step return_address_offset ge (Machblock.exit bb') (Machblock.State sf f sp (bb' :: c) rs' m') t s' ->
  match_states (Machblock.State sf f sp (bb :: c) rs m) S1' ->
  exists S2' : state, plus step tge S1' t S2' /\ match_states s' S2'.
Proof.
  intros.
  exploit step_simulation_body; eauto. intros. destruct H3 as (S2' & H31 & H32 & H33).
  exploit step_simulation_control; eauto. intros. destruct H3 as (S3' & H41 & H42).
  econstructor. econstructor. econstructor.
  eapply H31. apply plus_star. eapply H41.
  erewrite H33. traceEq. auto.
Qed.
*)

Lemma step_simulation_bblock:
  forall sf f sp bb rs m rs' m' t S1' s' c,
  body_step ge sf f sp (Machblock.body bb) rs m rs' m' ->
  exit_step return_address_offset ge (Machblock.exit bb) (Machblock.State sf f sp (bb :: c) rs' m') t s' ->
  match_states (Machblock.State sf f sp (bb :: c) rs m) S1' ->
  exists S2' : state, plus step tge S1' t S2' /\ match_states s' S2'.
Proof.
  intros. eapply step_simulation_bblock'; eauto. destruct bb as [hd bdy ex]; simpl in *. unfold remove_body; simpl.
  inv H0.
  - simpl in *. subst. econstructor. inv H2; try (econstructor; eauto; fail).
  - simpl in *. subst. econstructor.
Qed.

Theorem step_simulation:
  forall S1 t S2, MB.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros.

- (* bblock *)
  left. eapply step_simulation_bblock; eauto.

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
  monadInv EQ0. (* rewrite transl_code'_transl_code in EQ1. *)
  set (tfbody := Pallocframe (fn_stacksize f) (fn_link_ofs f) ::b
                 Pget GPR8 RA ::b
                 storeind_ptr GPR8 SP (fn_retaddr_ofs f) ::b x0) in *.
  set (tf := {| fn_sig := MB.fn_sig f; fn_blocks := tfbody |}) in *.
  set (rs2 := nextblock (bblock_single_inst (Pallocframe (fn_stacksize f) (fn_link_ofs f))) 
                          (rs0#FP <- (parent_sp s) #SP <- sp #GPR31 <- Vundef)).
  exploit (Pget_correct tge GPR8 RA nil rs2 m2'); auto.
  intros (rs' & U' & V').
  exploit (exec_straight_through_singleinst); eauto.
  intro W'. remember (nextblock _ rs') as rs''.
  exploit (storeind_ptr_correct tge SP (fn_retaddr_ofs f) GPR8 nil rs'' m2').
    rewrite chunk_of_Tptr in P.
    assert (rs' GPR8 = rs0 RA). { apply V'. }
    assert (rs'' GPR8 = rs' GPR8). { subst. Simpl. }
    assert (rs' GPR12 = rs2 GPR12). { apply V'; discriminate. }
    assert (rs'' GPR12 = rs' GPR12). { subst. Simpl. }
    rewrite H4. rewrite H3. rewrite H6. rewrite H5.
    (* change (rs' GPR8) with (rs0 RA). *)
    rewrite ATLR.
    change (rs2 GPR12) with sp. eexact P.
    congruence. congruence.
  intros (rs3 & U & V).
  exploit (exec_straight_through_singleinst); eauto.
  intro W.
  remember (nextblock _ rs3) as rs3'.
  assert (EXEC_PROLOGUE:
            exec_straight_blocks tge tf
              tf.(fn_blocks) rs0 m'
              x0 rs3' m3').
  { change (fn_blocks tf) with tfbody; unfold tfbody.
    apply exec_straight_blocks_step with rs2 m2'.
    unfold exec_bblock. simpl exec_body. rewrite C. fold sp. simpl exec_control.
    rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. simpl in F. rewrite F. reflexivity.
    reflexivity.
    eapply exec_straight_blocks_trans.
    - eexact W'.
    - eexact W. }
  exploit exec_straight_steps_2; eauto using functions_transl.
  simpl fn_blocks. simpl fn_blocks in g. unfold tfbody. simpl bblock_single_inst. omega. constructor.
  intros (ofs' & X & Y).                    
  left; exists (State rs3' m3'); split.
  eapply exec_straight_steps_1; eauto.
  simpl fn_blocks. simpl fn_blocks in g. unfold tfbody. simpl bblock_single_inst. omega.
  constructor.
  econstructor; eauto.
  rewrite X; econstructor; eauto. 
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2. 
  apply agree_nextblock. apply agree_set_other; auto with asmgen.
  apply agree_change_sp with (parent_sp s). 
  apply agree_undef_regs with rs0. auto.
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.

  intros.
  assert (r <> GPR31). { contradict H3; rewrite H3; unfold data_preg; auto. }
  rewrite Heqrs3'. Simpl. rewrite V. rewrite Heqrs''. Simpl. inversion V'. rewrite H6. auto.
  assert (r <> GPR8). { contradict H3; rewrite H3; unfold data_preg; auto. }
  assert (forall r : preg, r <> PC -> r <> GPR8 -> rs' r = rs2 r). { apply V'. }
  (* rewrite H8; auto. *)
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  contradict H3; rewrite H3; unfold data_preg; auto.
  auto. intros. rewrite Heqrs3'. Simpl. rewrite V by auto with asmgen.
  assert (forall r : preg, r <> PC -> r <> GPR8 -> rs' r = rs2 r). { apply V'. }
  rewrite Heqrs''. Simpl.
  rewrite H4 by auto with asmgen. reflexivity.
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

- (* return *) 
  inv MS.
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  rewrite <- ATPC in H5.
  econstructor; eauto. congruence.
Unshelve.
  exact true.
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
  forward_simulation (MB.semantics return_address_offset prog) (AB.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - exact step_simulation.
Qed.

End PRESERVATION.
