(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for K1c assembly language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.
Require Import Errors.
Require Export Asmvliw.

Section RELSEM.

(** Execution of arith instructions *)

Variable ge: genv.


Definition exec_arith_instr (ai: ar_instruction) (rs: regset): regset :=
  match ai with
  | PArithR n d => rs#d <- (arith_eval_r ge n)

  | PArithRR n d s => rs#d <- (arith_eval_rr n rs#s)

  | PArithRI32 n d i => rs#d <- (arith_eval_ri32 n i)
  | PArithRI64 n d i => rs#d <- (arith_eval_ri64 n i)
  | PArithRF32 n d i => rs#d <- (arith_eval_rf32 n i)
  | PArithRF64 n d i => rs#d <- (arith_eval_rf64 n i)

  | PArithRRR n d s1 s2 => rs#d <- (arith_eval_rrr n rs#s1 rs#s2)

  | PArithRRI32 n d s i => rs#d <- (arith_eval_rri32 n rs#s i)

  | PArithRRI64 n d s i => rs#d <- (arith_eval_rri64 n rs#s i)

  | PArithARRR n d s1 s2 => rs#d <- (arith_eval_arrr n rs#d rs#s1 rs#s2)

  | PArithARRI32 n d s i => rs#d <- (arith_eval_arri32 n rs#d rs#s i)

  | PArithARRI64 n d s i => rs#d <- (arith_eval_arri64 n rs#d rs#s i)
  end.

(** * load/store *)

(** Auxiliaries for memory accesses *)


Definition exec_load_offset (chunk: memory_chunk) (rs: regset) (m: mem) (d a: ireg) (ofs: offset) :=
  match (eval_offset ge ofs) with
  | OK ptr => match Mem.loadv chunk m (Val.offset_ptr (rs a) ptr) with
              | None => Stuck
              | Some v => Next (rs#d <- v) m
              end
  | _ => Stuck
  end.

Definition exec_load_reg (chunk: memory_chunk) (rs: regset) (m: mem) (d a ro: ireg) :=
  match Mem.loadv chunk m (Val.addl (rs a) (rs ro)) with
  | None => Stuck
  | Some v => Next (rs#d <- v) m
  end.

Definition exec_store_offset (chunk: memory_chunk) (rs: regset) (m: mem) (s a: ireg) (ofs: offset) :=
  match (eval_offset ge ofs) with
  | OK ptr => match Mem.storev chunk m (Val.offset_ptr (rs a) ptr) (rs s) with
              | None => Stuck
              | Some m' => Next rs m'
              end
  | _ => Stuck
  end.

Definition exec_store_reg (chunk: memory_chunk) (rs: regset) (m: mem) (s a ro: ireg) :=
  match Mem.storev chunk m (Val.addl (rs a) (rs ro)) (rs s) with
  | None => Stuck
  | Some m' => Next rs m'
  end.



(** * basic instructions *)

Definition exec_basic_instr (bi: basic) (rs: regset) (m: mem) : outcome :=
  match bi with
  | PArith ai => Next (exec_arith_instr ai rs) m

  | PLoadRRO n d a ofs => exec_load_offset (load_chunk n) rs m d a ofs
  | PLoadRRR n d a ro => exec_load_reg (load_chunk n) rs m d a ro

  | PStoreRRO n s a ofs => exec_store_offset (store_chunk n) rs m s a ofs
  | PStoreRRR n s a ro => exec_store_reg (store_chunk n) rs m s a ro

  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (rs #FP <- (rs SP) #SP <- sp #RTMP <- Vundef) m2
      end

  | Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (rs#SP <- v #RTMP <- Vundef) m'
              end
          | _ => Stuck
          end
      end
  | Pget rd ra =>
    match ra with
    | RA => Next (rs#rd <- (rs#ra)) m
    | _  => Stuck
    end
  | Pset ra rd =>
    match ra with
    | RA => Next (rs#ra <- (rs#rd)) m
    | _  => Stuck
    end
  | Pnop => Next rs m
end.

Fixpoint exec_body (body: list basic) (rs: regset) (m: mem): outcome :=
  match body with
  | nil => Next rs m
  | bi::body' => 
     match exec_basic_instr bi rs m with
     | Next rs' m' => exec_body body' rs' m'
     | Stuck => Stuck
     end
  end.



(** Position corresponding to a label *)



Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) : outcome :=
  match label_pos lbl 0 (fn_blocks f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Evaluating a branch 

Warning: in m PC is assumed to be already pointing on the next instruction !

*)
Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next rs m
    | None => Stuck
  end.


(** Execution of a single control-flow instruction [i] in initial state [rs] and
    [m].  Return updated state.

    As above: PC is assumed to be incremented on the next block before the control-flow instruction

    For instructions that correspond tobuiltin
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition exec_control (f: function) (oc: option control) (rs: regset) (m: mem) : outcome :=
  match oc with
  | Some ic =>
(** Get/Set system registers *)
  match ic with


(** Branch Control Unit instructions *)
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  | Pcall s =>
      Next (rs#RA <- (rs#PC) #PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Picall r =>
      Next (rs#RA <- (rs#PC) #PC <- (rs#r)) m
  | Pgoto s =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pigoto r =>
      Next (rs#PC <- (rs#r)) m
  | Pj_l l =>
      goto_label f l rs m
  | Pjumptable r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #GPR62 <- Vundef #GPR63 <- Vundef) m
          end
      | _ => Stuck
      end
      
  | Pcb bt r l =>
      match cmp_for_btest bt with
      | (Some c, Int)  => eval_branch f l rs m (Val.cmp_bool c rs#r (Vint (Int.repr 0)))
      | (Some c, Long) => eval_branch f l rs m (Val.cmpl_bool c rs#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end
  | Pcbu bt r l => 
      match cmpu_for_btest bt with
      | (Some c, Int) => eval_branch f l rs m (Val_cmpu_bool c rs#r (Vint (Int.repr 0)))
      | (Some c, Long) => eval_branch f l rs m (Val_cmplu_bool c rs#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end

(** Pseudo-instructions *)
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)
  end
  | None => Next rs m
end.

Definition exec_bblock (f: function) (b: bblock) (rs0: regset) (m: mem) : outcome :=
  match exec_body (body b) rs0 m with
  | Next rs' m' =>
    let rs1 := nextblock b rs' in exec_control f (exit b) rs1 m'
  | Stuck => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [X31].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)







(** Execution of the instruction at [rs PC]. *)


(** TODO
 * For now, we consider a builtin is alone in a basic block.
 * Perhaps there is a way to avoid that ?
 *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f bi rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_bblock (Ptrofs.unsigned ofs) (fn_blocks f) = Some bi ->
      exec_bblock f bi rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' bi,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_bblock (Ptrofs.unsigned ofs) f.(fn_blocks) = Some bi ->
      exit bi = Some (PExpand (Pbuiltin ef args res)) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextblock bi
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs#RTMP <- Vundef))) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State rs m) t (State rs' m')
  .



End RELSEM.



Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(* Useless

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  + split. constructor. auto.
  + unfold exec_bblock in H4. destruct (exec_body _ _ _ _); try discriminate.
    rewrite H9 in H4. discriminate.
  + unfold exec_bblock in H13. destruct (exec_body _ _ _ _); try discriminate.
    rewrite H4 in H13. discriminate.
  + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
    exploit external_call_determ. eexact H6. eexact H13. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
    exploit external_call_determ. eexact H3. eexact H8. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.
*)

Definition data_preg (r: preg) : bool :=
  match r with
  | RA  => false
  | IR GPRA => false
  | IR RTMP => false
  | IR _   => true
  | PC     => false
  end.

(** Determinacy of the [Asm] semantics. *)

(* Useless.

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.
*)
