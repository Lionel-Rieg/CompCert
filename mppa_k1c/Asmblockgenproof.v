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

- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (size_blocks x.(fn_blocks))); inv EQ0. monadInv EQ. simpl.
(*   rewrite transl_code'_transl_code in EQ0. *)
  exists x; exists true; split; auto. (*  unfold fn_code. *)
  repeat constructor.
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

Record codestate :=
  Codestate {     pstate: state;
                  pheader: list label;
                  pbody1: list basic;
                  pbody2: list basic;
                  pctl: option control;
                  fpok: bool;
                  rem: list AB.bblock;
                  cur: option bblock }.

(*   | Codestate: state -> list AB.bblock -> option bblock -> codestate. *)

Inductive match_codestate fb: Machblock.state -> codestate -> Prop :=
  | match_codestate_intro:
      forall s sp ms m rs0 m0 f tc ep c bb tbb tbc tbi
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m0)
        (TBC: transl_basic_code f (MB.body bb) ep = OK tbc)
        (TIC: transl_instr_control f (MB.exit bb) = OK tbi)
        (TBLS: transl_blocks f c false = OK tc)
(*         (TRANS: transl_blocks f (bb::c) ep = OK (tbb::tc)) *)
        (AG: agree ms sp rs0)
        (DXP: ep = true -> rs0#FP = parent_sp s),
      match_codestate fb (Machblock.State s fb sp (bb::c) ms m)
        {|  pstate := (Asmblock.State rs0 m0);
            pheader := (MB.header bb);
            pbody1 := tbc;
            pbody2 := (extract_basic tbi);
            pctl := extract_ctl tbi;
            fpok := ep;
            rem := tc;
            cur := Some tbb
        |}
.

Inductive match_asmblock fb: codestate -> Asmblock.state -> Prop :=
  | match_asmblock_some:
      forall rs f tf tc m tbb ofs ep tbdy tex lhd
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (TRANSF: transf_function f = OK tf)
        (PCeq: rs PC = Vptr fb ofs)
        (TAIL: code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) (tbb::tc))
        (HDROK: header tbb = lhd)
        ,
      match_asmblock fb 
        {|  pstate := (Asmblock.State rs m);
            pheader := lhd;
            pbody1 := tbdy;
            pbody2 := extract_basic tex;
            pctl := extract_ctl tex;
            fpok := ep;
            rem := tc;
            cur := Some tbb |}
        (Asmblock.State rs m)
.


Lemma transl_blocks_nonil:
  forall f bb c tc ep,
  transl_blocks f (bb::c) ep = OK tc ->
  exists tbb tc', tc = tbb :: tc'.
Proof.
  intros until ep. intros TLBS. monadInv TLBS. monadInv EQ. unfold gen_bblocks.
  destruct (extract_ctl x2).
  - destruct c0; destruct i; simpl; eauto.
  - destruct x1; simpl; eauto.
Qed.

Ltac exploreInst :=
  repeat match goal with
  | [ H : match ?var with | _ => _ end = _ |- _ ] => destruct var
  | [ H : OK _ = OK _ |- _ ] => monadInv H
  | [ |- context[if ?b then _ else _] ] => destruct b
  | [ |- context[match ?m with | _ => _ end] ] => destruct m
  | [ H : bind _ _ = OK _ |- _ ] => monadInv H
  | [ H : Error _ = OK _ |- _ ] => inversion H
  end.

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
    + simpl in TIC. exploreInst; simpl; eauto.
    + simpl in TIC. exploreInst; simpl; eauto.
    + assert (H: Some (MBbuiltin e l b) <>  Some (MBbuiltin e l b)).
        apply Hbuiltin. contradict H; auto.
    + simpl in TIC. exploreInst; simpl; eauto.
    + simpl in TIC. unfold transl_cbranch in TIC. exploreInst; simpl; eauto.
      * unfold transl_opt_compuimm. exploreInst; simpl; eauto.
      * unfold transl_opt_compluimm. exploreInst; simpl; eauto.
    + simpl in TIC. inv TIC.
    + simpl in TIC. monadInv TIC. simpl. eauto.
  - monadInv TIC. simpl; auto.
Qed.

Lemma transl_blocks_distrib:
  forall c f bb tbb tc ep,
  transl_blocks f (bb::c) ep = OK (tbb::tc)
  -> (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res))
  -> transl_block f bb ep = OK (tbb :: nil)
  /\ transl_blocks f c false = OK tc.
Proof.
  intros until ep. intros TLBS Hbuiltin.
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
  gen_bblocks thd tbdy tex = tbb :: nil ->
     header tbb = thd
  /\ body tbb = tbdy ++ extract_basic tex
  /\ exit tbb = extract_ctl tex.
Proof.
  intros until tbb. intros Hnonil GENB. unfold gen_bblocks in GENB.
  destruct (extract_ctl tex) eqn:ECTL.
  - destruct c.
    + destruct i. inv GENB.
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
  - simpl in TIB. unfold transl_load in TIB. exploreInst; try discriminate.
    all: unfold transl_memory_access in EQ0; exploreInst; try discriminate.
  - simpl in TIB. unfold transl_store in TIB. exploreInst; try discriminate.
    all: unfold transl_memory_access in EQ0; exploreInst; try discriminate.
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
  - contradict Hnonil; auto.
Qed.

Theorem match_state_codestate:
  forall mbs abs s fb sp bb c ms m,
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  (MB.body bb <> nil \/ MB.exit bb <> None) ->
  mbs = (Machblock.State s fb sp (bb::c) ms m) ->
  match_states mbs abs ->
  exists cs fb f tbb tc ep,
    match_codestate fb mbs cs /\ match_asmblock fb cs abs
    /\ Genv.find_funct_ptr ge fb = Some (Internal f)
    /\ transl_blocks f (bb::c) ep = OK (tbb::tc)
    /\ body tbb = pbody1 cs ++ pbody2 cs
    /\ exit tbb = pctl cs
    /\ cur cs = Some tbb /\ rem cs = tc
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
  intros (Hth & Htbdy & Htexit).
  exists {| pstate := (State rs m'); pheader := (Machblock.header bb); pbody1 := x; pbody2 := extract_basic x0;
            pctl := extract_ctl x0; fpok := ep; rem := tc'; cur := Some tbb |}, fb, f, tbb, tc', ep.
  repeat split. 1-2: econstructor; eauto. eauto.
  unfold transl_blocks. fold transl_blocks. unfold transl_block. rewrite EQ. simpl. rewrite EQ1; simpl.
  rewrite TLBS. simpl. rewrite H2.
  all: simpl; auto.
Qed.

Definition mb_remove_body (bb: MB.bblock) := 
  {| MB.header := MB.header bb; MB.body := nil; MB.exit := MB.exit bb |}.

Lemma exec_straight_pnil:
  forall c rs1 m1 rs2 m2,
  exec_straight tge c rs1 m1 (Pnop::nil) rs2 m2 ->
  exec_straight tge c rs1 m1 nil rs2 m2.
Proof.
  intros. eapply exec_straight_trans. eapply H. econstructor; eauto.
Qed.

Lemma transl_block_nobuiltin:
  forall f bb ep tbb,
  (MB.body bb <> nil \/ MB.exit bb <> None) ->
  transl_block f bb ep = OK (tbb :: nil) ->
  exists c c',
     transl_basic_code f (MB.body bb) ep = OK c
  /\ transl_instr_control f (MB.exit bb) = OK c'
  /\ body tbb = c ++ extract_basic c'
  /\ exit tbb = extract_ctl c'.
Proof.
  intros until tbb. intros Hnonil TLB. monadInv TLB. destruct Hnonil.
  - eexists. eexists. split; eauto. split; eauto. eapply gen_bblocks_nobuiltin; eauto.
    left. eapply transl_basic_code_nonil; eauto.
  - eexists. eexists. split; eauto. split; eauto. eapply gen_bblocks_nobuiltin; eauto.
    right. eapply transl_instr_control_nonil; eauto.
Qed.

Lemma nextblock_preserves: 
  forall rs rs' bb r,
  rs' = nextblock bb rs ->
  data_preg r = true ->
  rs r = rs' r.
Proof.
  intros. destruct r; try discriminate.
  - subst. Simpl.
  - subst. Simpl.
Qed.

Axiom TODO: False.

Theorem step_simu_control:
  forall bb' fb fn s sp c ms' m' rs2 m2 E0 S'' rs1 m1 tbb tbdy2 tex cs2,
  MB.body bb' = nil ->
  (forall ef args res, MB.exit bb' <> Some (MBbuiltin ef args res)) ->
  Genv.find_funct_ptr tge fb = Some (Internal fn) ->
  pstate cs2 = (Asmblock.State rs2 m2) ->
  pbody1 cs2 = nil -> pbody2 cs2 = tbdy2 -> pctl cs2 = tex ->
  cur cs2 = Some tbb ->
  match_codestate fb (MB.State s fb sp (bb'::c) ms' m') cs2 ->
  match_asmblock fb cs2 (Asmblock.State rs1 m1) ->
  exit_step return_address_offset ge (MB.exit bb') (MB.State s fb sp (bb'::c) ms' m') E0 S'' ->
  (exists rs3 m3 rs4 m4,
      exec_body tge tbdy2 rs2 m2 = Next rs3 m3
  /\  exec_control_rel tge fn tex tbb rs3 m3 rs4 m4
  /\  match_states S'' (State rs4 m4)).
Proof.
  intros until cs2. intros Hbody Hbuiltin FIND Hpstate Hpbody1 Hpbody2 Hpctl Hcur MCS MAS ESTEP. inv ESTEP.
  - inv MCS. inv MAS. simpl in *.
    destruct ctl.
    + (* MBcall *)
      destruct bb' as [mhd' mbdy' mex']; simpl in *. subst.
      inv TBC. inv TIC. inv H0.

      assert (f0 = f) by congruence. subst f0.
      assert (NOOV: size_blocks tf.(fn_blocks) <= Ptrofs.max_unsigned).
        eapply transf_function_no_overflow; eauto.
      destruct s1 as [rf|fid]; simpl in H7.
      * (* Indirect call *) inv H1.
      * (* Direct call *)
        monadInv H1.
        generalize (code_tail_next_int _ _ _ _ NOOV TAIL). intro CT1.
        remember (Ptrofs.add _ _) as ofs'.
        assert (TCA: transl_code_at_pc ge (Vptr fb ofs') fb f c false tf tc).
          econstructor; eauto.
        assert (f1 = f) by congruence. subst f1.
        exploit return_address_offset_correct; eauto. intros; subst ra.
        inv Hcur.
        repeat eexists.
          rewrite H6. econstructor; eauto.
          rewrite H7. econstructor; eauto.
        inv Hpstate. econstructor; eauto.
          econstructor; eauto. eapply agree_sp_def; eauto. simpl. eapply agree_exten; eauto. intros. Simpl.
        Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. simpl in H14. rewrite H14. auto.
        Simpl. simpl. subst. Simpl. simpl. unfold Val.offset_ptr. rewrite PCeq. auto.
    + (* MBtailcall *)
      destruct TODO.
    + (* MBbuiltin *)
      assert (MB.exit bb' <> Some (MBbuiltin e l b)) by (apply Hbuiltin).
      rewrite <- H in H1. contradict H1; auto.
    + (* MBgoto *)
      destruct TODO.
    + (* MBcond *)
      destruct TODO.
    + (* MBjumptable *)
      destruct TODO.
    + (* MBreturn *)
      destruct TODO.
  - inv MCS. inv MAS. simpl in *. subst. inv Hpstate. inv Hcur.
(*     exploit transl_blocks_distrib; eauto. (* rewrite <- H2. discriminate. *)
    intros (TLB & TLBS).
 *) destruct bb' as [hd' bdy' ex']; simpl in *. subst.
(*     unfold transl_block in TLB. simpl in TLB. unfold gen_bblocks in TLB; simpl in TLB. inv TLB. *)
    monadInv TBC. monadInv TIC. simpl in *. rewrite H5. rewrite H6.
    simpl. repeat eexists.
    econstructor. 4: instantiate (3 := false). all:eauto.
      unfold nextblock. Simpl. unfold Val.offset_ptr. rewrite PCeq.
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
  forall c c' rs1 m1 rs2 m2,
  exec_straight tge c rs1 m1 c' rs2 m2 ->
  exists l,
     c = l ++ c'
  /\ exec_body tge l rs1 m1 = Next rs2 m2.
Proof.
  induction c; try (intros; inv H; fail).
  intros. inv H.
  - exists (a ::i nil). split; auto. simpl. rewrite H7. auto.
  - apply IHc in H8. destruct H8 as (l & Hc & EXECB). subst.
    exists (a ::i l). split; auto. simpl. rewrite H2. auto.
Qed.

(* Lemma transl_blocks_basic_step:
  forall bb tbb c tc bi bdy x le f tbb' ep,
  transl_blocks f (bb::c) ep = OK (tbb::tc) ->
  MB.body bb = bi::(bdy) -> (bdy <> nil \/ MB.exit bb <> None) ->
  transl_basic_code f bdy (it1_is_parent true bi) = OK x ->
  transl_instr_control f (MB.exit bb) = OK le ->
  header tbb' = header tbb -> body tbb' = x ++ extract_basic le -> exit tbb' = exit tbb ->
  transl_blocks f ({| MB.header := MB.header bb; MB.body := bdy; MB.exit := MB.exit bb |}::c)
    (it1_is_parent ep bi)  =
    OK (tbb'::tc).
Proof.
Admitted.
 *)

Lemma step_simu_basic:
  forall bb bb' s fb sp c ms m rs1 m1 ms' m' bi cs1 tbdy bdy,
  MB.body bb = bi::(bdy) -> (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  bb' = {| MB.header := MB.header bb; MB.body := bdy; MB.exit := MB.exit bb |} ->
  basic_step ge s fb sp ms m bi ms' m' ->
  pstate cs1 = (State rs1 m1) -> pbody1 cs1 = tbdy ->
  match_codestate fb (MB.State s fb sp (bb::c) ms m) cs1 ->
  (exists rs2 m2 l cs2 tbdy',
       cs2 = {| pstate := (State rs2 m2); pheader := pheader cs1; pbody1 := tbdy'; pbody2 := pbody2 cs1;
                pctl := pctl cs1; fpok := it1_is_parent (fpok cs1) bi; rem := rem cs1; cur := cur cs1 |}
    /\ tbdy = l ++ tbdy'
    /\ exec_body tge l rs1 m1 = Next rs2 m2
    /\ match_codestate fb (MB.State s fb sp (bb'::c) ms' m') cs2).
Proof.
  intros until bdy. intros Hbody Hnobuiltin (* Hnotempty *) Hbb' BSTEP Hpstate Hpbody1 MCS. inv MCS.
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
    eapply exec_straight_body in EXECS. destruct EXECS as (l & Hlbi & EXECB).
    exists rs2, m1, l.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto). remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    assert (Hheadereq: MB.header bb' = MB.header bb). { subst. auto. }
    rewrite <- Hheadereq. subst.
    eapply match_codestate_intro; eauto.
    eapply agree_set_mreg; eauto with asmgen.
    intro Hep. simpl in Hep. inv Hep.
  - (* MBsetstack *)
    simpl in EQ0.
    unfold Mach.store_stack in H.
    assert (Val.lessdef (ms src) (rs1 (preg_of src))). { eapply preg_val; eauto. }
    exploit Mem.storev_extends; eauto. intros [m2' [A B]].
    exploit storeind_correct; eauto with asmgen.
    rewrite (sp_val _ _ _ AG) in A. eauto. intros [rs' [P Q]].

    eapply exec_straight_body in P. destruct P as (l & Hlbi & EXECB).
    exists rs', m2', l.
    eexists. eexists. split. instantiate (1 := x). eauto.
    repeat (split; auto). remember {| MB.header := _; MB.body := _; MB.exit := _ |} as bb'.
    assert (Hheadereq: MB.header bb' = MB.header bb). { subst. auto. }
    rewrite <- Hheadereq. subst.
    eapply match_codestate_intro; eauto.

    eapply agree_undef_regs; eauto with asmgen.
    simpl; intros. rewrite Q; auto with asmgen.
  - (* MBgetparam *)
    destruct TODO.
  - (* MBop *)
    destruct TODO.
  - (* MBload *)
    destruct TODO.
  - (* MBstore *)
    destruct TODO.
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

Lemma step_simu_body:
  forall bb s fb sp c ms m rs1 m1 ms' cs1 m',
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  body_step ge s fb sp (MB.body bb) ms m ms' m' ->
  pstate cs1 = (State rs1 m1) ->
  match_codestate fb (MB.State s fb sp (bb::c) ms m) cs1 ->
  (exists rs2 m2 cs2 ep,
       cs2 = {| pstate := (State rs2 m2); pheader := pheader cs1; pbody1 := nil; pbody2 := pbody2 cs1;
                pctl := pctl cs1; fpok := ep; rem := rem cs1; cur := cur cs1 |}
    /\ exec_body tge (pbody1 cs1) rs1 m1 = Next rs2 m2
    /\ match_codestate fb (MB.State s fb sp (mb_remove_body bb::c) ms' m') cs2).
Proof.
  intros bb. destruct bb as [hd bdy ex]; simpl; auto. induction bdy as [|bi bdy].
  - intros until m'. intros Hnobuiltin BSTEP Hpstate MCS.
    inv BSTEP.
    exists rs1, m1, cs1, (fpok cs1).
    inv MCS. inv Hpstate. simpl in *. monadInv TBC. repeat (split; simpl; auto).
    econstructor; eauto.
  - intros until m'. intros Hnobuiltin BSTEP Hpstate MCS. inv BSTEP.
    rename ms' into ms''. rename m' into m''. rename rs' into ms'. rename m'0 into m'.
    exploit (step_simu_basic); eauto. simpl. eauto. simpl; auto.
    intros (rs2 & m2 & l & cs2 & tbdy' & Hcs2 & Happ & EXEB & MCS').
    simpl in *.
    exploit IHbdy. 2: eapply H6. 3: eapply MCS'. all: eauto. subst; eauto. simpl; auto.
    intros (rs3 & m3 & cs3 & ep & Hcs3 & EXEB' & MCS'').
    exists rs3, m3, cs3, ep.
    repeat (split; simpl; auto). subst. simpl in *. auto.
    rewrite Happ. eapply exec_body_trans; eauto. rewrite Hcs2 in EXEB'; simpl in EXEB'. auto.
Qed.

(* Theorem step_simu_body:
  forall bb s fb sp tbb c ms m rs1 m1 tc ms' m',
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  body_step ge s fb sp (MB.body bb) ms m ms' m' ->
  match_codestate fb (MB.State s fb sp (bb::c) ms m) (Codestate (State rs1 m1) (tbb::tc) (Some tbb)) ->
  (exists rs2 m2 tbb' l,
       body tbb = l ++ body tbb'
    /\ exec_body tge l rs1 m1 = Next rs2 m2
    /\ match_codestate fb (MB.State s fb sp (mb_remove_body bb::c) ms' m')
        (Codestate (State rs2 m2) (tbb'::tc) (Some tbb))
    /\ exit tbb' = exit tbb ).
Proof.
  intros. exploit step_simu_body'; eauto.
  intros (rs2 & m2 & tbb' & l & Hbody & EXEB & MCS & Hexit).
  exists rs2, m2, tbb', l. repeat (split; simpl; auto).
  inv MCS. econstructor; eauto.
Qed. *)

Lemma exec_body_straight:
  forall l rs0 m0 rs1 m1,
  l <> nil ->
  exec_body tge l rs0 m0 = Next rs1 m1 ->
  exec_straight tge l rs0 m0 nil rs1 m1.
Proof.
  induction l as [|i1 l].
    intros. contradict H; auto.
  destruct l as [|i2 l].
  - intros until m1. intros _ EXEB. simpl in EXEB.
    destruct (exec_basic_instr _ _ _) eqn:EBI; try discriminate.
    inv EXEB. econstructor; eauto.
  - intros until m1. intros _ EXEB. simpl in EXEB. simpl in IHl.
    destruct (exec_basic_instr tge i1 rs0 m0) eqn:EBI; try discriminate.
    econstructor; eauto. eapply IHl; eauto. discriminate.
Qed.

Lemma exec_body_pc:
  forall l rs1 m1 rs2 m2,
  exec_body tge l rs1 m1 = Next rs2 m2 ->
  rs2 PC = rs1 PC.
Proof.
  induction l.
  - intros. inv H. auto.
  - intros until m2. intro EXEB.
    inv EXEB. destruct (exec_basic_instr _ _ _) eqn:EBI; try discriminate.
    eapply IHl in H0. rewrite H0.
    erewrite exec_basic_instr_pc; eauto.
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

(* Alternative form of step_simulation_bblock, easier to prove *)
Lemma step_simulation_bblock':
  forall sf f sp bb bb' rs m rs' m' s'' c S1,
  body_step ge sf f sp (Machblock.body bb) rs m rs' m' ->
  bb' = mb_remove_body bb ->
  (forall ef args res, MB.exit bb' <> Some (MBbuiltin ef args res)) ->
  exit_step return_address_offset ge (Machblock.exit bb') (Machblock.State sf f sp (bb' :: c) rs' m') E0 s'' ->
  match_states (Machblock.State sf f sp (bb :: c) rs m) S1 ->
  exists S2 : state, plus step tge S1 E0 S2 /\ match_states s'' S2.
Proof.
  intros until S1. intros BSTEP Hbb' Hbuiltin ESTEP MS.
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
    unfold nextblock. Simpl. unfold Val.offset_ptr. rewrite <- H.
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

    (* step_simu_body part *)
    assert (exists rs1 m1, pstate cs1 = State rs1 m1). { inv MAS. simpl. eauto. }
    destruct H as (rs1 & m1 & Hpstate2). subst.
    assert (f = fb). { inv MCS. auto. }
    subst. exploit step_simu_body.
      2: eapply BSTEP.
      all: eauto.
    intros (rs2 & m2 & cs2 & ep' & Hcs2 & EXEB & MCS'). rename f0 into f.

    (* step_simu_control part *)
    assert (exists tf, Genv.find_funct_ptr tge fb = Some (Internal tf)).
    { exploit functions_translated; eauto. intros (tf & FIND' & TRANSF'). monadInv TRANSF'. eauto. }
    destruct H as (tf & FIND').
    assert (exists tex, pbody2 cs1 = extract_basic tex /\ pctl cs1 = extract_ctl tex).
    { inv MAS. simpl in *. eauto. }
    destruct H as (tex & Hpbody2 & Hpctl).
    subst. exploit step_simu_control.
      9: eapply MCS'.
      all: simpl; eauto.
      rewrite Hpbody2. rewrite Hpctl. rewrite Hcur.
      { inv MAS; simpl in *. inv Hcur. inv Hpstate2. eapply match_asmblock_some; eauto.
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
    assert (exists ofs, rs1 PC = Vptr fb ofs).
    { rewrite Hpstate2 in MAS. inv MAS. simpl in *. eauto. }
    destruct H0 as (ofs & Hrs1pc).
    eapply exec_step_internal; eauto.

    (* proving the initial find_bblock *)
    rewrite Hpstate2 in MAS. inv MAS. simpl in *. 
    assert (f = f0) by congruence. subst f0.
    rewrite PCeq in Hrs1pc. inv Hrs1pc.
    exploit functions_translated; eauto. intros (tf1 & FIND'' & TRANS''). rewrite FIND' in FIND''.
    inv FIND''. monadInv TRANS''. rewrite TRANSF0 in EQ. inv EQ. inv Hcur.
    eapply find_bblock_tail; eauto.
Qed.

Lemma step_simulation_bblock:
  forall sf f sp bb ms m ms' m' S2 c,
  body_step ge sf f sp (Machblock.body bb) ms m ms' m' ->
  (forall ef args res, MB.exit bb <> Some (MBbuiltin ef args res)) ->
  exit_step return_address_offset ge (Machblock.exit bb) (Machblock.State sf f sp (bb :: c) ms' m') E0 S2 ->
  forall S1', match_states (Machblock.State sf f sp (bb :: c) ms m) S1' ->
  exists S2' : state, plus step tge S1' E0 S2' /\ match_states S2 S2'.
Proof.
  intros until c. intros BSTEP Hbuiltin ESTEP S1' MS.
  eapply step_simulation_bblock'; eauto. destruct bb as [hd bdy ex]; simpl in *.
  inv ESTEP.
  - econstructor. inv H; try (econstructor; eauto; fail).
  - econstructor.
Qed.

Definition measure (s: MB.state) : nat :=
  match s with
  | MB.State _ _ _ _ _ _ => 0%nat
  | MB.Callstate _ _ _ _ => 0%nat
  | MB.Returnstate _ _ _ => 1%nat
  end.

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
  + (* MBbuiltin *) destruct TODO.
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
