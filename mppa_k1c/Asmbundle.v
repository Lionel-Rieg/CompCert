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
Require Export Asmblock.

Section RELSEM.

Variable ge: genv.

(* FIXME: STUB *)
Definition is_bundle (b:bblock):=True. 

Definition bundle_step (s:state) (t:trace) (s':state): Prop := 
  exists obi, stepin ge obi s t s' /\ forall bi, obi = Some bi -> is_bundle bi.

End RELSEM.

Definition bundle_semantics (p: program) :=
  Semantics bundle_step (initial_state p) final_state (Genv.globalenv p).



(*

(** * Instruction dependencies, definition of a bundle 

*)

(** NOTE: in all of these dependencies definitions, we do *not* consider PC.
          PC dependencies are fullfilled by the above separation in bblocks
 *)

(* (writereg i rd) holds if an instruction writes to a single register rd *)
Inductive writereg: instruction -> preg -> Prop :=
  | writereg_set:         forall rd rs,         writereg (Pset rd rs) rd
  | writereg_get:         forall rd rs,         writereg (Pget rd rs) rd
  | writereg_load:        forall i rd ra o,     writereg (PLoadRRO i rd ra o) rd
  | writereg_arith_r:     forall i rd,          writereg (PArithR i rd) rd
  | writereg_arith_rr:    forall i rd rs,       writereg (PArithRR i rd rs) rd
  | writereg_arith_ri32:  forall i rd imm,      writereg (PArithRI32 i rd imm) rd
  | writereg_arith_ri64:  forall i rd imm,      writereg (PArithRI64 i rd imm) rd
  | writereg_arith_rrr:   forall i rd rs1 rs2,  writereg (PArithRRR i rd rs1 rs2) rd
  | writereg_arith_rri32: forall i rd rs imm,   writereg (PArithRRI32 i rd rs imm) rd
  | writereg_arith_rri64: forall i rd rs imm,   writereg (PArithRRI64 i rd rs imm) rd
  .

(* (nowrite i) holds if an instruction doesn't write to any register *)
Inductive nowrite: instruction -> Prop :=
  | nowrite_ret:                      nowrite Pret
  | nowrite_call:   forall l,         nowrite (Pcall l)
  | nowrite_goto:   forall l,         nowrite (Pgoto l)
  | nowrite_jl:     forall l,         nowrite (Pj_l l)
  | nowrite_cb:     forall bt r l,    nowrite (Pcb bt r l)
  | nowrite_cbu:    forall bt r l,    nowrite (Pcbu bt r l)
  | nowrite_store:  forall i rs ra o, nowrite (PStoreRRO i rs ra o)
  | nowrite_label:  forall l,         nowrite (Plabel l)
  .

(* (readregs i lr) holds if an instruction reads from the register list lr, and only from it *)
Inductive readregs: instruction -> list preg -> Prop :=
  | readregs_set:         forall rd rs,         readregs (Pset rd rs) (IR rs::nil)
  | readregs_get:         forall rd rs,         readregs (Pget rd rs) (rs::nil)
  | readregs_cb:          forall bt r l,        readregs (Pcb bt r l) (IR r::nil)
  | readregs_cbu:         forall bt r l,        readregs (Pcbu bt r l) (IR r::nil)
  | readregs_load:        forall i rd ra o,     readregs (PLoadRRO i rd ra o) (IR ra::nil)
  | readregs_store:       forall i rs ra o,     readregs (PStoreRRO i rs ra o) (IR rs::IR ra::nil)
  | readregs_arith_rr:    forall i rd rs,       readregs (PArithRR i rd rs) (IR rs::nil)
  | readregs_arith_rrr:   forall i rd rs1 rs2,  readregs (PArithRRR i rd rs1 rs2) (IR rs1::IR rs2::nil)
  | readregs_arith_rri32: forall i rd rs imm,   readregs (PArithRRI32 i rd rs imm) (IR rs::nil)
  | readregs_arith_rri64: forall i rd rs imm,   readregs (PArithRRI64 i rd rs imm) (IR rs::nil)
  .

(* (noread i) holds if an instruction doesn't read any register *)
Inductive noread: instruction -> Prop :=
  | noread_ret:                           noread Pret
  | noread_call:        forall l,         noread (Pcall l)
  | noread_goto:        forall l,         noread (Pgoto l)
  | noread_jl:          forall l,         noread (Pj_l l)
  | noread_arith_r:     forall i rd,      noread (PArithR i rd)
  | noread_arith_ri32:  forall i rd imm,  noread (PArithRI32 i rd imm)
  | noread_arith_ri64:  forall i rd imm,  noread (PArithRI64 i rd imm)
  | noread_label:       forall l,         noread (Plabel l)
  .

(* (wawfree i i') holds if i::i' has no WAW dependency *)
Inductive wawfree: instruction -> instruction -> Prop :=
  | wawfree_write: forall i rs i' rs',
      writereg i rs -> writereg i' rs' -> rs <> rs' -> wawfree i i'
  | wawfree_free1: forall i i',
      nowrite i -> wawfree i i'
  | wawfree_free2: forall i i',
      nowrite i' -> wawfree i i'
  .

(* (rawfree i i') holds if i::i' has no RAW dependency *)
Inductive rawfree: instruction -> instruction -> Prop :=
  | rawfree_single: forall i rd i' rs,
      writereg i rd -> readregs i' (rs::nil) -> rd <> rs -> rawfree i i'
  | rawfree_double: forall i rd i' rs rs',
      writereg i rd -> readregs i' (rs::rs'::nil) -> rd <> rs -> rd <> rs' -> rawfree i i'
  | rawfree_free1: forall i i',
      nowrite i -> rawfree i i'
  | rawfree_free2: forall i i',
      noread i' -> rawfree i i'
  .

(* (depfree i i') holds if i::i' has no RAW or WAW dependency *)
Inductive depfree: instruction -> instruction -> Prop :=
  | mk_depfree: forall i i', rawfree i i' -> wawfree i i' -> depfree i i'.

(* (depfreelist i c) holds if i::c has no RAW or WAW dependency _in regards to i_ *)
Inductive depfreelist: instruction -> list instruction -> Prop :=
  | depfreelist_nil:  forall i,
      depfreelist i nil
  | depfreelist_cons: forall i i' l,
      depfreelist i l -> depfree i i' -> depfreelist i (i'::l)
  .

(* (depfreeall c) holds if c has no RAW or WAW dependency within itself *)
Inductive depfreeall: list instruction -> Prop :=
  | depfreeall_nil:
      depfreeall nil
  | depfreeall_cons: forall i l,
      depfreeall l -> depfreelist i l -> depfreeall (i::l)
  .

(** NOTE: we do not verify the resource constraints of the bundles,
          since not meeting them causes a failure when invoking the assembler *)

(* A bundle is well formed if his body and exit do not have RAW or WAW dependencies *)
Inductive wf_bundle: bblock -> Prop := 
  | mk_wf_bundle: forall b, depfreeall (body b ++ unfold_exit (exit b)) -> wf_bundle b.

Hint Constructors writereg nowrite readregs noread wawfree rawfree depfree depfreelist depfreeall wf_bundle.

Record bundle := mk_bundle {
  bd_block: bblock;
  bd_correct: wf_bundle bd_block
}.

Definition bundles := list bundle.

Definition unbundlize (lb: list bundle) := map bd_block lb.
Definition unfold_bd (lb: list bundle) := unfold (map bd_block lb).

Lemma unfold_bd_app: forall l l', unfold_bd (l ++ l') = unfold_bd l ++ unfold_bd l'.
Proof.
  intros l l'. unfold unfold_bd. rewrite map_app. rewrite unfold_app. auto.
Qed.

(** Some theorems on bundles construction *)
Lemma bundle_empty_correct: wf_bundle empty_bblock.
Proof.
  constructor. auto.
Qed.

Definition empty_bundle := {| bd_block := empty_bblock; bd_correct := bundle_empty_correct |}.

(** Bundlization. For now, we restrict ourselves to bundles containing 1 instruction *)

Definition single_inst_block (i: instruction) := acc_block i empty_bblock.

Fact single_inst_block_correct: forall i, wf_bundle (hd empty_bblock (single_inst_block i)).
Proof.
  intros i. unfold single_inst_block. unfold acc_block. destruct i.
  all:  simpl; constructor; simpl; auto.
Qed.

Definition bundlize_inst (i: instruction) :=
  {| bd_block := hd empty_bblock (single_inst_block i); bd_correct := single_inst_block_correct i |}.

Lemma bundlize_inst_conserv: forall c, unfold (unbundlize (map bundlize_inst c)) = c.
Proof.
  induction c as [|i c]; simpl; auto.
  rewrite IHc. destruct i; simpl; auto.
Qed.

Definition split_bblock (b: bblock) := map bundlize_inst (unfold_block b).

Fixpoint bundlize (lb: list bblock) :=
  match lb with
  | nil => nil
  | b :: lb => split_bblock b ++ bundlize lb
  end.

Lemma unfold_split_bblock: forall b, unfold_bd (split_bblock b) = unfold_block b.
Proof.
  intros b. unfold unfold_bd. unfold split_bblock. apply bundlize_inst_conserv.
Qed.

Theorem unfold_bundlize: forall lb, unfold_bd (bundlize lb) = unfold lb.
Proof.
  induction lb as [|b lb]; simpl; auto.
  rewrite unfold_bd_app. rewrite IHlb. rewrite unfold_split_bblock. auto.
Qed.

Theorem unfold_bundlize_fold: forall c, unfold_bd (bundlize (fold c)) = c.
Proof.
  intros. rewrite unfold_bundlize. rewrite unfold_fold. auto.
Qed.

Record function : Type := mkfunction { fn_sig: signature; fn_bundles: bundles }.
Definition fn_code := (fun (f: function) => unfold_bd (fn_bundles f)).
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
*)