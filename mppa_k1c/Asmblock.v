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


(** * Auxiliary utilies on basic blocks *)

(** ** A unified view of Kalray instructions *)

Inductive instruction : Type :=
  | PBasic    (i: basic)
  | PControl  (i: control)
.

Coercion PBasic:    basic >-> instruction.
Coercion PControl:  control >-> instruction.

Definition code := list instruction.
Definition bcode := list basic.

Fixpoint basics_to_code (l: list basic) :=
  match l with
  | nil => nil
  | bi::l => (PBasic bi)::(basics_to_code l)
  end.

Fixpoint code_to_basics (c: code) :=
  match c with
  | (PBasic i)::c =>
    match code_to_basics c with
    | None => None
    | Some l => Some (i::l)
    end
  | _::c => None
  | nil => Some nil
  end.

Lemma code_to_basics_id: forall c, code_to_basics (basics_to_code c) = Some c.
Proof.
  intros. induction c as [|i c]; simpl; auto.
  rewrite IHc. auto.
Qed.

Lemma code_to_basics_dist:
  forall c c' l l',
  code_to_basics c = Some l ->
  code_to_basics c' = Some l' ->
  code_to_basics (c ++ c') = Some (l ++ l').
Proof.
  induction c as [|i c]; simpl; auto.
  - intros. inv H. simpl. auto.
  - intros. destruct i; try discriminate. destruct (code_to_basics c) eqn:CTB; try discriminate.
    inv H. erewrite IHc; eauto. auto.
Qed.

(** 
  Asmblockgen will have to translate a Mach control into a list of instructions of the form
   i1 :: i2 :: i3 :: ctl :: nil ; where i1..i3 are basic instructions, ctl is a control instruction
  These functions provide way to extract the basic / control instructions
*)

Fixpoint extract_basic (c: code) :=
  match c with
  | nil => nil
  | PBasic i :: c => i :: (extract_basic c)
  | PControl i :: c => nil
  end.

Fixpoint extract_ctl (c: code) :=
  match c with
  | nil => None
  | PBasic i :: c => extract_ctl c
  | PControl i :: nil => Some i
  | PControl i :: _ => None (* if the first found control instruction isn't the last *)
  end.

(** ** Wellformness of basic blocks *)

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

Definition non_empty_bblock (body: list basic) (exit: option control): Prop
 := body <> nil \/ exit <> None.

Lemma non_empty_bblock_refl:
  forall body exit,
  non_empty_bblock body exit <->
  Is_true (non_empty_bblockb body exit).
Proof.
  intros. split.
  - destruct body; destruct exit.
    all: simpl; auto. intros. inversion H; contradiction.
  - destruct body; destruct exit.
    all: simpl; auto.
    all: intros; try (right; discriminate); try (left; discriminate).
    contradiction.
Qed.

Definition builtin_alone (body: list basic) (exit: option control) := forall ef args res,
  exit = Some (PExpand (Pbuiltin ef args res)) -> body = nil.


Lemma builtin_alone_refl:
  forall body exit,
  builtin_alone body exit <-> Is_true (builtin_aloneb body exit).
Proof.
  intros. split.
  - destruct body; destruct exit.
    all: simpl; auto.
    all: exploreInst; simpl; auto.
    unfold builtin_alone. intros. assert (Some (Pbuiltin e l b0) = Some (Pbuiltin e l b0)); auto.
    assert (b :: body = nil). eapply H; eauto. discriminate.
  - destruct body; destruct exit.
    all: simpl; auto; try constructor.
    + exploreInst; try discriminate.
        simpl. contradiction.
    + intros. discriminate.
Qed.

Definition wf_bblock (body: list basic) (exit: option control) :=
  non_empty_bblock body exit /\ builtin_alone body exit.

Lemma wf_bblock_refl:
  forall body exit,
  wf_bblock body exit <-> Is_true (wf_bblockb body exit).
Proof.
  intros. split.
  - intros. inv H. apply non_empty_bblock_refl in H0. apply builtin_alone_refl in H1.
    apply andb_prop_intro. auto.
  - intros. apply andb_prop_elim in H. inv H.
    apply non_empty_bblock_refl in H0. apply builtin_alone_refl in H1.
    unfold wf_bblock. split; auto.
Qed.

Ltac bblock_auto_correct := (apply non_empty_bblock_refl; try discriminate; try (left; discriminate); try (right; discriminate)).
(* Local Obligation Tactic := bblock_auto_correct. *)

Lemma Istrue_proof_irrelevant (b: bool): forall (p1 p2:Is_true b), p1=p2.
Proof.
  destruct b; simpl; auto.
  - destruct p1, p2; auto.
  - destruct p1.
Qed.

Lemma bblock_equality bb1 bb2: header bb1=header bb2 -> body bb1 = body bb2 -> exit bb1 = exit bb2 -> bb1 = bb2.
Proof.
  destruct bb1 as [h1 b1 e1 c1], bb2 as [h2 b2 e2 c2]; simpl.
  intros; subst.
  rewrite (Istrue_proof_irrelevant _ c1 c2).
  auto.
Qed.

Program Definition bblock_single_inst (i: instruction) :=
  match i with
  | PBasic b => {| header:=nil; body:=(b::nil); exit:=None |}
  | PControl ctl => {| header:=nil; body:=nil; exit:=(Some ctl) |}
  end.
Next Obligation.
  apply wf_bblock_refl. constructor.
    right. discriminate.
    constructor.
Qed.

Lemma length_nonil {A: Type} : forall l:(list A), l <> nil -> (length l > 0)%nat.
Proof.
  intros. destruct l; try (contradict H; auto; fail).
  simpl. omega.
Qed.

Lemma to_nat_pos : forall z:Z, (Z.to_nat z > 0)%nat -> z > 0.
Proof.
  intros. destruct z; auto.
  - contradict H. simpl. apply gt_irrefl.
  - apply Zgt_pos_0.
  - contradict H. simpl. apply gt_irrefl.
Qed.

Lemma size_positive (b:bblock): size b > 0.
Proof.
  unfold size. destruct b as [hd bdy ex cor]. simpl.
  destruct ex; destruct bdy; try (apply to_nat_pos; rewrite Nat2Z.id; simpl; omega).
  inversion cor; contradict H; simpl; auto.
Qed.


Program Definition no_header (bb : bblock) := {| header := nil; body := body bb; exit := exit bb |}.
Next Obligation.
  destruct bb; simpl. assumption.
Defined.

Lemma no_header_size:
  forall bb, size (no_header bb) = size bb.
Proof.
  intros. destruct bb as [hd bdy ex COR]. unfold no_header. simpl. reflexivity.
Qed.

Program Definition stick_header (h : list label) (bb : bblock) := {| header := h; body := body bb; exit := exit bb |}.
Next Obligation.
  destruct bb; simpl. assumption.
Defined.

Lemma stick_header_size:
  forall h bb, size (stick_header h bb) = size bb.
Proof.
  intros. destruct bb. unfold stick_header. simpl. reflexivity.
Qed.

Lemma stick_header_no_header:
  forall bb, stick_header (header bb) (no_header bb) = bb.
Proof.
  intros. destruct bb as [hd bdy ex COR]. simpl. unfold no_header; unfold stick_header; simpl. reflexivity.
Qed.




(** * Sequential Semantics of basic blocks *)
Section RELSEM.

(** Execution of arith instructions *)

Variable ge: genv.

(* TODO: delete this or define it as [parexec_arith_instr ge ai rs rs] *)
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

(* TODO: delete this or define it as [parexec_load_offset ge chunk rs rs m m d a ofs] *)
Definition exec_load_offset (chunk: memory_chunk) (rs: regset) (m: mem) (d a: ireg) (ofs: offset) :=
  match (eval_offset ge ofs) with
  | OK ptr => match Mem.loadv chunk m (Val.offset_ptr (rs a) ptr) with
              | None => Stuck
              | Some v => Next (rs#d <- v) m
              end
  | _ => Stuck
  end.

(* TODO: delete this or define it as [parexec_load_reg ge chunk rs rs m m d a ro] *)
Definition exec_load_reg (chunk: memory_chunk) (rs: regset) (m: mem) (d a ro: ireg) :=
  match Mem.loadv chunk m (Val.addl (rs a) (rs ro)) with
  | None => Stuck
  | Some v => Next (rs#d <- v) m
  end.

(* TODO: delete this as define it as ... *)
Definition exec_store_offset (chunk: memory_chunk) (rs: regset) (m: mem) (s a: ireg) (ofs: offset) :=
  match (eval_offset ge ofs) with
  | OK ptr => match Mem.storev chunk m (Val.offset_ptr (rs a) ptr) (rs s) with
              | None => Stuck
              | Some m' => Next rs m'
              end
  | _ => Stuck
  end.

(* TODO: delete this as define it as ... *)
Definition exec_store_reg (chunk: memory_chunk) (rs: regset) (m: mem) (s a ro: ireg) :=
  match Mem.storev chunk m (Val.addl (rs a) (rs ro)) (rs s) with
  | None => Stuck
  | Some m' => Next rs m'
  end.



(** * basic instructions *)

(* TODO: define this [parexec_basic_instr ge bi rs rs m m] *)
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

(** * control-flow instructions *)

(* TODO: delete this or define it as [par_goto_label ge f lbl rs rs m] *)
Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) : outcome :=
  match label_pos lbl 0 (fn_blocks f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(* TODO: delete this or define it as [par_eval_branch ge f l rs rs m res] *)
Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next rs m
    | None => Stuck
  end.

(* TODO: delete this or define it as [parexec_control ge f oc rs rs m] *)
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

(* TODO: change [exec_bblock] for a definition like this one: 

Definition exec_exit (f: function) ext size_b (rs: regset) (m: mem) 
  := parexec_exit ge f ext size_b rs rs m.

Definition exec_bblock (f: function) (b: bblock) (rs0: regset) (m: mem) : outcome :=
  match exec_body (body b) rs0 m with
  | Next rs' m' => exec_exit f (exit b) (Ptrofs.repr (size b)) rs' m'
  | Stuck => Stuck
  end.

*)

Definition exec_bblock (f: function) (b: bblock) (rs0: regset) (m: mem) : outcome :=
  match exec_body (body b) rs0 m with
  | Next rs' m' =>
    let rs1 := nextblock b rs' in exec_control f (exit b) rs1 m'
  | Stuck => Stuck
  end.


(** Execution of the instruction at [rs PC]. *)


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


Definition data_preg (r: preg) : bool :=
  match r with
  | RA  => false
  | IR GPRA => false
  | IR RTMP => false
  | IR _   => true
  | PC     => false
  end.

