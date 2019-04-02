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
Require Export Asmblock.
Require Import Sorting.Permutation.

Local Open Scope asm.

Section RELSEM.

(** Execution of arith instructions *)

Variable ge: genv.

(* TODO: on pourrait mettre ça dans Asmblock pour factoriser le code
   en définissant 
    exec_arith_instr ai rs := parexec_arith_instr ai rs rs
*)
Definition parexec_arith_instr (ai: ar_instruction) (rsr rsw: regset): regset :=
  match ai with
  | PArithR n d => rsw#d <- (arith_eval_r ge n)

  | PArithRR n d s => rsw#d <- (arith_eval_rr n rsr#s)

  | PArithRI32 n d i => rsw#d <- (arith_eval_ri32 n i)
  | PArithRI64 n d i => rsw#d <- (arith_eval_ri64 n i)
  | PArithRF32 n d i => rsw#d <- (arith_eval_rf32 n i)
  | PArithRF64 n d i => rsw#d <- (arith_eval_rf64 n i)

  | PArithRRR n d s1 s2 => rsw#d <- (arith_eval_rrr n rsr#s1 rsr#s2)
  | PArithRRI32 n d s i => rsw#d <- (arith_eval_rri32 n rsr#s i)
  | PArithRRI64 n d s i => rsw#d <- (arith_eval_rri64 n rsr#s i)

  | PArithARRR n d s1 s2 => rsw#d <- (arith_eval_arrr n rsr#d rsr#s1 rsr#s2)
  | PArithARRI32 n d s i => rsw#d <- (arith_eval_arri32 n rsr#d rsr#s i)
  | PArithARRI64 n d s i => rsw#d <- (arith_eval_arri64 n rsr#d rsr#s i)
  end.

(** * load/store *)

(* TODO: factoriser ? *)
Definition parexec_load (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem)
                     (d: ireg) (a: ireg) (ptr: ptrofs) :=
  match Mem.loadv chunk mr (Val.offset_ptr (rsr a) ptr) with
  | None => Stuck
  | Some v => Next (rsw#d <- v) mw
  end
.

Definition parexec_load_offset (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (d a: ireg) (ofs: offset) :=
  match (eval_offset ge ofs) with
  | OK ptr => parexec_load chunk rsr rsw mr mw d a ptr
  | _ => Stuck
  end.

Definition parexec_load_reg (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (d a ro: ireg) :=
  match (rsr ro) with
  | Vptr _ ofs => parexec_load chunk rsr rsw mr mw d a ofs
  | _ => Stuck
  end.

Definition parexec_store (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem)
                      (s: ireg) (a: ireg) (ptr: ptrofs) :=
  match Mem.storev chunk mr (Val.offset_ptr (rsr a) ptr) (rsr s) with
  | None => Stuck
  | Some m' => Next rsw m'
  end
.

Definition parexec_store_offset (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (s a: ireg) (ofs: offset) :=
  match (eval_offset ge ofs) with
  | OK ptr => parexec_store chunk rsr rsw mr mw s a ptr
  | _ => Stuck
  end.

Definition parexec_store_reg (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (s a ro: ireg) :=
  match (rsr ro) with
  | Vptr _ ofs => parexec_store chunk rsr rsw mr mw s a ofs
  | _ => Stuck
  end.

(* rem: parexec_store = exec_store *)

(** * basic instructions *)

(* TODO: factoriser ? *)
Definition parexec_basic_instr (bi: basic) (rsr rsw: regset) (mr mw: mem) :=
  match bi with
  | PArith ai => Next (parexec_arith_instr ai rsr rsw) mw

  | PLoadRRO n d a ofs => parexec_load_offset (load_chunk n) rsr rsw mr mw d a ofs
  | PLoadRRR n d a ro => parexec_load_reg (load_chunk n) rsr rsw mr mw d a ro

  | PStoreRRO n s a ofs => parexec_store_offset (store_chunk n) rsr rsw mr mw s a ofs
  | PStoreRRR n s a ro => parexec_store_reg (store_chunk n) rsr rsw mr mw s a ro

  | Pallocframe sz pos =>
      let (mw, stk) := Mem.alloc mr 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr mw (Val.offset_ptr sp pos) rsr#SP with
      | None => Stuck
      | Some mw => Next (rsw #FP <- (rsr SP) #SP <- sp #RTMP <- Vundef) mw
      end

  | Pfreeframe sz pos =>
      match Mem.loadv Mptr mr (Val.offset_ptr rsr#SP pos) with
      | None => Stuck
      | Some v =>
          match rsr SP with
          | Vptr stk ofs =>
              match Mem.free mr stk 0 sz with
              | None => Stuck
              | Some mw => Next (rsw#SP <- v #RTMP <- Vundef) mw
              end
          | _ => Stuck
          end
      end
  | Pget rd ra =>
    match ra with
    | RA => Next (rsw#rd <- (rsr#ra)) mw
    | _  => Stuck
    end
  | Pset ra rd =>
    match ra with
    | RA => Next (rsw#ra <- (rsr#rd)) mw
    | _  => Stuck
    end
  | Pnop => Next rsw mw
end.

(* parexec with writes-in-order *)
Fixpoint parexec_wio_body (body: list basic) (rsr rsw: regset) (mr mw: mem) :=
  match body with
  | nil => Next rsw mw
  | bi::body' => 
     match parexec_basic_instr bi rsr rsw mr mw with
     | Next rsw mw => parexec_wio_body body' rsr rsw mr mw
     | Stuck => Stuck
     end
  end.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextblock]) or branching to a label ([goto_label]). *)

(* TODO: factoriser ? *)
Definition par_nextblock size_b (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC size_b).

(* TODO: factoriser ? *)
Definition par_goto_label (f: function) (lbl: label) (rsr rsw: regset) (mw: mem) :=
  match label_pos lbl 0 (fn_blocks f) with
  | None => Stuck
  | Some pos =>
      match rsr#PC with
      | Vptr b ofs => Next (rsw#PC <- (Vptr b (Ptrofs.repr pos))) mw
      | _          => Stuck
      end
  end.

(** Evaluating a branch 

Warning: in m PC is assumed to be already pointing on the next instruction !

*)
(* TODO: factoriser ? *)
Definition par_eval_branch (f: function) (l: label) (rsr rsw: regset) (mw: mem) (res: option bool) :=
  match res with
    | Some true  => par_goto_label f l rsr rsw mw
    | Some false => Next (rsw # PC <- (rsr PC)) mw
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

Definition parexec_control (f: function) (oc: option control) (rsr rsw: regset) (mw: mem) :=
  match oc with
  | Some ic =>
(** Get/Set system registers *)
  match ic with


(** Branch Control Unit instructions *)
  | Pret =>
      Next (rsw#PC <- (rsr#RA)) mw
  | Pcall s =>
      Next (rsw#RA <- (rsr#PC) #PC <- (Genv.symbol_address ge s Ptrofs.zero)) mw
  | Picall r =>
      Next (rsw#RA <- (rsr#PC) #PC <- (rsr#r)) mw
  | Pjumptable r tbl =>
      match rsr#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => par_goto_label f lbl rsr (rsw #GPR62 <- Vundef #GPR63 <- Vundef) mw
          end
      | _ => Stuck
      end
  | Pgoto s =>
      Next (rsw#PC <- (Genv.symbol_address ge s Ptrofs.zero)) mw
  | Pigoto r =>
      Next (rsw#PC <- (rsr#r)) mw
  | Pj_l l =>
      par_goto_label f l rsr rsw mw
  | Pcb bt r l =>
      match cmp_for_btest bt with
      | (Some c, Int)  => par_eval_branch f l rsr rsw mw (Val.cmp_bool c rsr#r (Vint (Int.repr 0)))
      | (Some c, Long) => par_eval_branch f l rsr rsw mw (Val.cmpl_bool c rsr#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end
  | Pcbu bt r l => 
      match cmpu_for_btest bt with
      | (Some c, Int) => par_eval_branch f l rsr rsw mw (Val_cmpu_bool c rsr#r (Vint (Int.repr 0)))
      | (Some c, Long) => par_eval_branch f l rsr rsw mw (Val_cmplu_bool c rsr#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end

(** Pseudo-instructions *)
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)
  end
  | None => Next (rsw#PC <- (rsr#PC)) mw
end.


Definition parexec_wio_bblock_aux (f: function) bdy ext size_b (rsr rsw: regset) (mr mw: mem): outcome :=
  match parexec_wio_body bdy rsr rsw mr mw with
  | Next rsw mw =>
    let rsr := par_nextblock size_b rsr in 
    let rsw := par_nextblock size_b rsw in 
    parexec_control f ext rsr rsw mw
  | Stuck => Stuck
  end.

Definition parexec_wio_bblock (f: function) (b: bblock) (rs: regset) (m: mem): outcome :=
  parexec_wio_bblock_aux f (body b) (exit b) (Ptrofs.repr (size b)) rs rs m m.

Definition parexec_bblock (f: function) (b: bblock) (rs: regset) (m: mem) (o: outcome): Prop :=
   exists bdy1 bdy2, Permutation (bdy1++bdy2) (body b) /\ 
      o=match parexec_wio_bblock_aux f bdy1 (exit b) (Ptrofs.repr (size b)) rs rs m m with
      | Next rsw mw => parexec_wio_body bdy2 rs rsw m mw
      | Stuck => Stuck
      end.

Lemma parexec_bblock_write_in_order f b rs m:
   parexec_bblock f b rs m (parexec_wio_bblock f b rs m).
Proof.
   exists (body b). exists nil.
   constructor 1.
   - rewrite app_nil_r; auto.
   - unfold parexec_wio_bblock.
     destruct (parexec_wio_bblock_aux f _ _ _ _ _); simpl; auto.
Qed.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f bi rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_bblock (Ptrofs.unsigned ofs) (fn_blocks f) = Some bi ->
      parexec_wio_bblock f bi rs m = Next rs' m' ->
      (forall o, parexec_bblock f bi rs m o -> o=(Next rs' m')) ->
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

(** Execution of whole programs. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

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
  + unfold parexec_wio_bblock, parexec_wio_bblock_aux in H4. destruct (parexec_wio_body _ _ _ _ _ _); try discriminate.
    rewrite H10 in H4. discriminate.
  + unfold parexec_wio_bblock, parexec_wio_bblock_aux in H11. destruct (parexec_wio_body _ _ _ _ _ _); try discriminate.
    rewrite H4 in H11. discriminate.
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