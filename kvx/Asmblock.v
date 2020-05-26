(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** Sequential block semantics for KVX assembly. The syntax is given in AsmVLIW *)

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

(* Notations necessary to hook Asmvliw definitions *)
Notation undef_caller_save_regs := Asmvliw.undef_caller_save_regs.
Notation regset := Asmvliw.regset.
Notation extcall_arg := Asmvliw.extcall_arg.
Notation extcall_arg_pair := Asmvliw.extcall_arg_pair.
Notation extcall_arguments := Asmvliw.extcall_arguments.
Notation set_res := Asmvliw.set_res.
Notation function := Asmvliw.function.
Notation bblocks := Asmvliw.bblocks.
Notation header := Asmvliw.header.
Notation body := Asmvliw.body.
Notation exit := Asmvliw.exit.
Notation correct := Asmvliw.correct.

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

Definition exec_arith_instr (ai: ar_instruction) (rs: regset): regset := parexec_arith_instr ge ai rs rs.

(** Auxiliaries for memory accesses *)

Definition exec_load_offset (trap: trapping_mode) (chunk: memory_chunk) (rs: regset) (m: mem) (d a: ireg) (ofs: offset) := parexec_load_offset trap chunk rs rs m m d a ofs.

Definition exec_load_reg (trap: trapping_mode) (chunk: memory_chunk) (rs: regset) (m: mem) (d a ro: ireg) := parexec_load_reg trap chunk rs rs m m d a ro.

Definition exec_load_regxs (trap: trapping_mode) (chunk: memory_chunk) (rs: regset) (m: mem) (d a ro: ireg) := parexec_load_regxs trap chunk rs rs m m d a ro.

Definition exec_load_q_offset (rs: regset) (m: mem) (d : gpreg_q) (a: ireg) (ofs: offset) := parexec_load_q_offset rs rs m m d a ofs.

Definition exec_load_o_offset (rs: regset) (m: mem) (d : gpreg_o) (a: ireg) (ofs: offset) := parexec_load_o_offset rs rs m m d a ofs.

Definition exec_store_offset (chunk: memory_chunk) (rs: regset) (m: mem) (s a: ireg) (ofs: offset) := parexec_store_offset chunk rs rs m m s a ofs.

Definition exec_store_q_offset (rs: regset) (m: mem) (s : gpreg_q) (a: ireg) (ofs: offset) := parexec_store_q_offset rs rs m m s a ofs.

Definition exec_store_o_offset (rs: regset) (m: mem) (s : gpreg_o) (a: ireg) (ofs: offset) := parexec_store_o_offset rs rs m m s a ofs.

Definition exec_store_reg (chunk: memory_chunk) (rs: regset) (m: mem) (s a ro: ireg) := parexec_store_reg chunk rs rs m m s a ro.

Definition exec_store_regxs (chunk: memory_chunk) (rs: regset) (m: mem) (s a ro: ireg) := parexec_store_regxs chunk rs rs m m s a ro.

(** * basic instructions *)

Definition exec_basic_instr (bi: basic) (rs: regset) (m: mem) : outcome := bstep ge bi rs rs m m.

Fixpoint exec_body (body: list basic) (rs: regset) (m: mem): outcome :=
  match body with
  | nil => Next rs m
  | bi::body' => 
     match exec_basic_instr bi rs m with
     | Next rs' m' => exec_body body' rs' m'
     | Stuck => Stuck
     end
  end.


Theorem builtin_body_nil:
  forall bb ef args res, exit bb = Some (PExpand (Pbuiltin ef args res)) -> body bb = nil.
Proof.
  intros. destruct bb as [hd bdy ex WF]. simpl in *.
  apply wf_bblock_refl in WF. inv WF. unfold builtin_alone in H1.
  eapply H1; eauto.
Qed.

Theorem exec_body_app:
  forall l l' rs m rs'' m'',
  exec_body (l ++ l') rs m = Next rs'' m'' ->
  exists rs' m',
       exec_body l rs m = Next rs' m'
    /\ exec_body l' rs' m' = Next rs'' m''.
Proof.
  induction l.
  - intros. simpl in H. repeat eexists. auto.
  - intros. rewrite <- app_comm_cons in H. simpl in H.
    destruct (exec_basic_instr a rs m) eqn:EXEBI.
    + apply IHl in H. destruct H as (rs1 & m1 & EXEB1 & EXEB2).
      repeat eexists. simpl. rewrite EXEBI. eauto. auto.
    + discriminate.
Qed.

(** Position corresponding to a label *)

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) : outcome := par_goto_label f lbl rs rs m.

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome := par_eval_branch f l rs rs m res.

Definition exec_control (f: function) (oc: option control) (rs: regset) (m: mem) : outcome := parexec_control ge f oc rs rs m.

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
