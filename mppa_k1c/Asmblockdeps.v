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

(** * Translation from Asmblock to AbstractBB 

    We define a specific instance of AbstractBB, named L, translate bblocks from Asmblock into this instance
    AbstractBB will then define two semantics for L : a sequential, and a semantic one
    We prove a bisimulation between the parallel semantics of L and AsmVLIW
    From this, we also deduce a bisimulation between the sequential semantics of L and Asmblock *)

Require Import AST.
Require Import Asmblock.
Require Import Asmblockgenproof0 Asmblockprops.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import ZArith.
Require Import Coqlib.
Require Import ImpSimuTest.
Require Import Axioms.
Require Import Parallelizability.
Require Import Asmvliw Permutation.
Require Import Chunks.

Require Import Lia.

Open Scope impure.

(** Definition of L *)

Module P<: ImpParam.
Module R := Pos.

Section IMPPARAM.

Definition env := Genv.t fundef unit.

Inductive genv_wrap := Genv (ge: env) (fn: function).
Definition genv := genv_wrap.

Variable Ge: genv.

Inductive value_wrap :=
  | Val (v: val)
  | Memstate (m: mem)
.

Definition value := value_wrap.

Inductive control_op :=
  | Oj_l (l: label)
  | Ocb (bt: btest) (l: label)
  | Ocbu (bt: btest) (l: label)
  | Odiv
  | Odivu
  | OError
  | OIncremPC (sz: Z)
  | Ojumptable (l: list label)
.

Inductive arith_op :=
  | OArithR (n: arith_name_r)
  | OArithRR (n: arith_name_rr)
  | OArithRI32 (n: arith_name_ri32) (imm: int)
  | OArithRI64 (n: arith_name_ri64) (imm: int64)
  | OArithRF32 (n: arith_name_rf32) (imm: float32)
  | OArithRF64 (n: arith_name_rf64) (imm: float)
  | OArithRRR (n: arith_name_rrr)
  | OArithRRI32 (n: arith_name_rri32) (imm: int)
  | OArithRRI64 (n: arith_name_rri64) (imm: int64)
  | OArithARRR (n: arith_name_arrr)
  | OArithARR (n: arith_name_arr)
  | OArithARRI32 (n: arith_name_arri32) (imm: int)
  | OArithARRI64 (n: arith_name_arri64) (imm: int64)
.

Coercion OArithR: arith_name_r >-> arith_op.
Coercion OArithRR: arith_name_rr >-> arith_op.
Coercion OArithRI32: arith_name_ri32 >-> Funclass.
Coercion OArithRI64: arith_name_ri64 >-> Funclass.
Coercion OArithRF32: arith_name_rf32 >-> Funclass.
Coercion OArithRF64: arith_name_rf64 >-> Funclass.
Coercion OArithRRR: arith_name_rrr >-> arith_op.
Coercion OArithRRI32: arith_name_rri32 >-> Funclass.
Coercion OArithRRI64: arith_name_rri64 >-> Funclass.

Inductive load_op :=
  | OLoadRRO (n: load_name) (trap: trapping_mode) (ofs: offset)
  | OLoadRRR (n: load_name) (trap: trapping_mode) 
  | OLoadRRRXS (n: load_name) (trap: trapping_mode)
.

Coercion OLoadRRO: load_name >-> Funclass.

Inductive store_op :=
  | OStoreRRO (n: store_name) (ofs: offset)
  | OStoreRRR (n: store_name)
  | OStoreRRRXS (n: store_name)
.

Coercion OStoreRRO: store_name >-> Funclass.

Inductive op_wrap :=
  | Arith (ao: arith_op)
  | Load (lo: load_op)
  | Store (so: store_op)
  | Control (co: control_op)
  | Allocframe (sz: Z) (pos: ptrofs)
  | Allocframe2 (sz: Z) (pos: ptrofs)
  | Freeframe (sz: Z) (pos: ptrofs)
  | Freeframe2 (sz: Z) (pos: ptrofs)
  | Constant (v: val)
  | Fail
.

Coercion Arith: arith_op >-> op_wrap.
Coercion Load: load_op >-> op_wrap.
Coercion Store: store_op >-> op_wrap.
Coercion Control: control_op >-> op_wrap.

Definition op := op_wrap.

Definition arith_eval (ao: arith_op) (l: list value) :=
  let (ge, fn) := Ge in
  match ao, l with
  | OArithR n, [] => Some (Val (arith_eval_r ge n))

  | OArithRR n, [Val v] => Some (Val (arith_eval_rr n v))

  | OArithRI32 n i, [] => Some (Val (arith_eval_ri32 n i))
  | OArithRI64 n i, [] => Some (Val (arith_eval_ri64 n i))
  | OArithRF32 n i, [] => Some (Val (arith_eval_rf32 n i))
  | OArithRF64 n i, [] => Some (Val (arith_eval_rf64 n i))

  | OArithRRR n, [Val v1; Val v2] => Some (Val (arith_eval_rrr n v1 v2))
  | OArithRRI32 n i, [Val v] => Some (Val (arith_eval_rri32 n v i))
  | OArithRRI64 n i, [Val v] => Some (Val (arith_eval_rri64 n v i))

  | OArithARR n, [Val v1; Val v2] => Some (Val (arith_eval_arr n v1 v2))
  | OArithARRR n, [Val v1; Val v2; Val v3] => Some (Val (arith_eval_arrr n v1 v2 v3))
  | OArithARRI32 n i, [Val v1; Val v2] => Some (Val (arith_eval_arri32 n v1 v2 i))
  | OArithARRI64 n i, [Val v1; Val v2] => Some (Val (arith_eval_arri64 n v1 v2 i))

  | _, _ => None
  end.

Definition exec_incorrect_load trap chunk :=
  match trap with
  | TRAP => None
  | NOTRAP => Some (Val (concrete_default_notrap_load_value chunk))
  end.

Definition exec_load_deps_offset (trap: trapping_mode) (chunk: memory_chunk) (m: mem) (v: val) (ofs: offset) :=
  let (ge, fn) := Ge in
  match (eval_offset ofs) with
  | OK ptr => match Mem.loadv chunk m (Val.offset_ptr v ptr) with 
              | None => exec_incorrect_load trap chunk
              | Some vl => Some (Val vl)
              end
  | _ => None
  end.

Definition exec_load_deps_reg (trap: trapping_mode) (chunk: memory_chunk) (m: mem) (v vo: val) :=
  match Mem.loadv chunk m (Val.addl v vo) with
  | None => exec_incorrect_load trap chunk
  | Some vl => Some (Val vl)
  end.

Definition exec_load_deps_regxs (trap: trapping_mode) (chunk: memory_chunk) (m: mem) (v vo: val) :=
  match Mem.loadv chunk m (Val.addl v (Val.shll vo (scale_of_chunk chunk))) with
  | None => exec_incorrect_load trap chunk
  | Some vl => Some (Val vl)
  end.

Definition load_eval (lo: load_op) (l: list value) :=
  match lo, l with
  | OLoadRRO n trap ofs, [Val v; Memstate m] => exec_load_deps_offset trap (load_chunk n) m v ofs
  | OLoadRRR n trap, [Val v; Val vo; Memstate m] => exec_load_deps_reg trap (load_chunk n) m v vo
  | OLoadRRRXS n trap, [Val v; Val vo; Memstate m] => exec_load_deps_regxs trap (load_chunk n) m v vo
  | _, _ => None
  end.

Definition exec_store_deps_offset (chunk: memory_chunk) (m: mem) (vs va: val) (ofs: offset) :=
  let (ge, fn) := Ge in
  match (eval_offset ofs) with
  | OK ptr => match Mem.storev chunk m (Val.offset_ptr va ptr) vs with
              | None => None
              | Some m' => Some (Memstate m')
              end
  | _ => None
  end.

Definition exec_store_deps_reg (chunk: memory_chunk) (m: mem) (vs va vo: val) :=
  match Mem.storev chunk m (Val.addl va vo) vs with
  | None => None
  | Some m' => Some (Memstate m')
  end.

Definition exec_store_deps_regxs (chunk: memory_chunk) (m: mem) (vs va vo: val) :=
  match Mem.storev chunk m (Val.addl va (Val.shll vo (scale_of_chunk chunk))) vs with
  | None => None
  | Some m' => Some (Memstate m')
  end.

Definition store_eval (so: store_op) (l: list value) :=
  match so, l with
  | OStoreRRO n ofs, [Val vs; Val va; Memstate m] => exec_store_deps_offset (store_chunk n) m vs va ofs
  | OStoreRRR n, [Val vs; Val va; Val vo; Memstate m] => exec_store_deps_reg (store_chunk n) m vs va vo
  | OStoreRRRXS n, [Val vs; Val va; Val vo; Memstate m] => exec_store_deps_regxs (store_chunk n) m vs va vo
  | _, _ => None
  end.

Local Open Scope Z.

Remark size_chunk_positive: forall chunk,
    (size_chunk chunk) > 0.
Proof.
  destruct chunk; simpl; lia.
Qed.

Remark size_chunk_small: forall chunk,
    (size_chunk chunk) <= 8.
Proof.
  destruct chunk; simpl; lia.
Qed.

Definition disjoint_chunks
           (ofs1 : offset) (chunk1 : memory_chunk)
           (ofs2 : offset) (chunk2 : memory_chunk) :=
  Intv.disjoint ((Ptrofs.unsigned ofs1),
                 ((Ptrofs.unsigned ofs1) + (size_chunk chunk1)))
                ((Ptrofs.unsigned ofs2),
                 ((Ptrofs.unsigned ofs2) + (size_chunk chunk2))).

Definition small_offset_threshold := 18446744073709551608.

Lemma store_store_disjoint_offsets :
  forall n1 n2 ofs1 ofs2 vs1 vs2 va m0 m1 m2 m1' m2',
    (disjoint_chunks ofs1 (store_chunk n1) ofs2 (store_chunk n2)) ->
    (Ptrofs.unsigned ofs1) < small_offset_threshold ->
    (Ptrofs.unsigned ofs2) < small_offset_threshold ->
    store_eval (OStoreRRO n1 ofs1) [vs1; va; Memstate m0] = Some (Memstate m1) ->
    store_eval (OStoreRRO n2 ofs2) [vs2; va; Memstate m1] = Some (Memstate m2) ->
    store_eval (OStoreRRO n2 ofs2) [vs2; va; Memstate m0] = Some (Memstate m1') ->
    store_eval (OStoreRRO n1 ofs1) [vs1; va; Memstate m1'] = Some (Memstate m2') ->
    m2 = m2'.
Proof.
  intros until m2'.
  intros DISJOINT SMALL1 SMALL2 STORE0 STORE1 STORE0' STORE1'.
  unfold disjoint_chunks in DISJOINT.
  destruct vs1 as [v1 | ]; simpl in STORE0, STORE1'; try congruence.
  destruct vs2 as [v2 | ]; simpl in STORE1, STORE0'; try congruence.
  destruct va as [base | ]; try congruence.
  unfold exec_store_deps_offset in *.
  destruct Ge.
  unfold eval_offset in *; simpl in *.
  unfold Mem.storev in *.
  unfold Val.offset_ptr in *.
  destruct base as [ | | | | | wblock wpofs] in * ; try congruence.
  destruct (Mem.store _ _ _ _ _) eqn:E0; try congruence.
  inv STORE0.
  destruct (Mem.store (store_chunk n2) _ _ _ _) eqn:E1; try congruence.
  inv STORE1.
  destruct (Mem.store (store_chunk n2) m0 _ _ _) eqn:E0'; try congruence.
  inv STORE0'.
  destruct (Mem.store _ m1' _ _ _) eqn:E1'; try congruence.
  inv STORE1'.
  assert (Some m2 = Some m2').
  2: congruence.
  rewrite <- E1.
  rewrite <- E1'.
  eapply Mem.store_store_other.
  2, 3: eassumption.

  right.
  pose proof (size_chunk_positive (store_chunk n1)).
  pose proof (size_chunk_positive (store_chunk n2)).
  pose proof (size_chunk_small (store_chunk n1)).
  pose proof (size_chunk_small (store_chunk n2)).
  destruct (Intv.range_disjoint _ _ DISJOINT) as [DIS | [DIS | DIS]];
    unfold Intv.empty in DIS; simpl in DIS.
  1, 2: lia.
  pose proof (Ptrofs.unsigned_range ofs1).
  pose proof (Ptrofs.unsigned_range ofs2).
  unfold small_offset_threshold in *.
  destruct (Ptrofs.unsigned_add_either wpofs ofs1) as [R1 | R1]; rewrite R1;
    destruct (Ptrofs.unsigned_add_either wpofs ofs2) as [R2 | R2]; rewrite R2;
      change Ptrofs.modulus with 18446744073709551616 in *; 
      lia.
Qed.

Lemma load_store_disjoint_offsets :
  forall n1 n2 tm ofs1 ofs2 vs va m0 m1,
    (disjoint_chunks ofs1 (store_chunk n1) ofs2 (load_chunk n2)) ->
    (Ptrofs.unsigned ofs1) < small_offset_threshold ->
    (Ptrofs.unsigned ofs2) < small_offset_threshold ->
    store_eval (OStoreRRO n1 ofs1) [vs; va; Memstate m0] = Some (Memstate m1) ->
    load_eval (OLoadRRO n2 tm ofs2) [va; Memstate m1] =
    load_eval (OLoadRRO n2 tm ofs2) [va; Memstate m0].
Proof.
  intros until m1.
  intros DISJOINT SMALL1 SMALL2 STORE0.
  destruct vs as [v | ]; simpl in STORE0; try congruence.
  destruct va as [base | ]; try congruence.
  unfold exec_store_deps_offset in *.
  unfold eval_offset in *; simpl in *.
  unfold exec_load_deps_offset.
  unfold Mem.storev, Mem.loadv in *.
  destruct Ge in *.
  unfold eval_offset in *.
  unfold Val.offset_ptr in *.
  destruct base as [ | | | | | wblock wpofs] in * ; try congruence.
  destruct (Mem.store _ _ _ _) eqn:E0; try congruence.
  inv STORE0.
  assert (
    (Mem.load (load_chunk n2) m1 wblock
      (Ptrofs.unsigned (Ptrofs.add wpofs ofs2))) =
    (Mem.load (load_chunk n2) m0 wblock
              (Ptrofs.unsigned (Ptrofs.add wpofs ofs2))) ) as LOADS.
  {
    eapply Mem.load_store_other.
    eassumption.
    right.
    pose proof (size_chunk_positive (store_chunk n1)).
    pose proof (size_chunk_positive (load_chunk n2)).
    pose proof (size_chunk_small (store_chunk n1)).
    pose proof (size_chunk_small (load_chunk n2)).
    destruct (Intv.range_disjoint _ _ DISJOINT) as [DIS | [DIS | DIS]];
      unfold Intv.empty in DIS; simpl in DIS.
    1,2: lia.
    
    pose proof (Ptrofs.unsigned_range ofs1).
    pose proof (Ptrofs.unsigned_range ofs2).
    unfold small_offset_threshold in *.
    destruct (Ptrofs.unsigned_add_either wpofs ofs1) as [R1 | R1]; rewrite R1;
      destruct (Ptrofs.unsigned_add_either wpofs ofs2) as [R2 | R2]; rewrite R2;
        change Ptrofs.modulus with 18446744073709551616 in *; 
        lia.
  }
  destruct (Mem.load _ m1 _ _) in *; destruct (Mem.load _ m0 _ _) in *; congruence.
Qed.

Definition goto_label_deps (f: function) (lbl: label) (vpc: val) :=
  match label_pos lbl 0 (fn_blocks f) with
  | None => None
  | Some pos =>
      match vpc with
      | Vptr b ofs => Some (Val (Vptr b (Ptrofs.repr pos)))
      | _          => None
      end
  end.

Definition eval_branch_deps (f: function) (l: label) (vpc: val) (res: option bool) :=
  match res with
    | Some true  => goto_label_deps f l vpc
    | Some false => Some (Val vpc)
    | None => None
  end.

Definition control_eval (o: control_op) (l: list value) :=
  let (ge, fn) := Ge in
  match o, l with
  | (Ojumptable tbl), [Val index; Val vpc] =>
    match index with
    | Vint n => 
      match list_nth_z tbl (Int.unsigned n) with
      | None => None
      | Some lbl => goto_label_deps fn lbl vpc
      end
    | _ => None
    end
  | Oj_l l, [Val vpc] => goto_label_deps fn l vpc
  | Ocb bt l, [Val v; Val vpc] =>
    match cmp_for_btest bt with
    | (Some c, Int)  => eval_branch_deps fn l vpc (Val.cmp_bool c v (Vint (Int.repr 0)))
    | (Some c, Long) => eval_branch_deps fn l vpc (Val.cmpl_bool c v (Vlong (Int64.repr 0)))
    | (None, _) => None
    end
  | Ocbu bt l, [Val v; Val vpc] =>
    match cmpu_for_btest bt with
    | (Some c, Int) => eval_branch_deps fn l vpc (Val_cmpu_bool c v (Vint (Int.repr 0)))
    | (Some c, Long) => eval_branch_deps fn l vpc (Val_cmplu_bool c v (Vlong (Int64.repr 0)))
    | (None, _) => None
    end
  | Odiv, [Val v1; Val v2] => 
    match Val.divs v1 v2 with
    | Some v => Some (Val v)
    | None => None
    end
  | Odivu, [Val v1; Val v2] =>
    match Val.divu v1 v2 with
    | Some v => Some (Val v)
    | None => None
    end
  | OIncremPC sz, [Val vpc] => Some (Val (Val.offset_ptr vpc (Ptrofs.repr sz)))
  | OError, _ => None
  | _, _ => None
  end.

Definition op_eval (o: op) (l: list value) :=
  match o, l with
  | Arith o, l => arith_eval o l
  | Load o, l => load_eval o l
  | Store o, l => store_eval o l
  | Control o, l => control_eval o l
  | Allocframe sz pos, [Val spv; Memstate m] => 
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) spv with
      | None => None
      | Some m => Some (Memstate m)
      end
  | Allocframe2 sz pos, [Val spv; Memstate m] => 
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) spv with
      | None => None
      | Some m => Some (Val sp)
      end
  | Freeframe sz pos, [Val spv; Memstate m] =>
      match Mem.loadv Mptr m (Val.offset_ptr spv pos) with
      | None => None
      | Some v =>
          match spv with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => None
              | Some m' => Some (Memstate m')
              end
          | _ => None
          end
      end
  | Freeframe2 sz pos, [Val spv; Memstate m] =>
      match Mem.loadv Mptr m (Val.offset_ptr spv pos) with
      | None => None
      | Some v =>
          match spv with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => None
              | Some m' => Some (Val v)
              end
          | _ => None
          end
      end
  | Constant v, [] => Some (Val v)
  | Fail, _ => None
  | _, _ => None
  end.


Definition arith_op_eq (o1 o2: arith_op): ?? bool :=
  match o1 with
  | OArithR n1 =>
     match o2 with OArithR n2 => struct_eq n1 n2 | _ => RET false end
  | OArithRR n1 => 
     match o2 with OArithRR n2 => phys_eq n1 n2 | _ => RET false end
  | OArithRI32 n1 i1 =>
     match o2 with OArithRI32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithRI64 n1 i1 =>
     match o2 with OArithRI64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithRF32 n1 i1 =>
     match o2 with OArithRF32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithRF64 n1 i1 =>
     match o2 with OArithRF64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithRRR n1 =>
     match o2 with OArithRRR n2 => phys_eq n1 n2 | _ => RET false end
  | OArithRRI32 n1 i1 =>
     match o2 with OArithRRI32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithRRI64 n1 i1 =>
     match o2 with OArithRRI64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithARRR n1 =>
     match o2 with OArithARRR n2 => phys_eq n1 n2 | _ => RET false end
  | OArithARR n1 =>
     match o2 with OArithARR n2 => phys_eq n1 n2 | _ => RET false end
  | OArithARRI32 n1 i1 =>
     match o2 with OArithARRI32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  | OArithARRI64 n1 i1 =>
     match o2 with OArithARRI64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2) | _ => RET false end
  end.

Ltac my_wlp_simplify := wlp_xsimplify ltac:(intros; subst; simpl in * |- *; congruence || intuition eauto with wlp).

Lemma arith_op_eq_correct o1 o2:
  WHEN arith_op_eq o1 o2 ~> b THEN b = true -> o1 = o2.
Proof.
  destruct o1, o2; my_wlp_simplify; try congruence.
Qed.
Hint Resolve arith_op_eq_correct: wlp.
Opaque arith_op_eq_correct.

Definition offset_eq (ofs1 ofs2 : offset): ?? bool :=
  RET (Ptrofs.eq ofs1 ofs2).

Lemma offset_eq_correct ofs1 ofs2:
  WHEN offset_eq ofs1 ofs2 ~> b THEN b = true -> ofs1 = ofs2.
Proof.
  wlp_simplify.
  pose (Ptrofs.eq_spec ofs1 ofs2).
  rewrite H in *.
  trivial.
Qed.
Hint Resolve offset_eq_correct: wlp.

Definition trapping_mode_eq trap1 trap2 :=
  RET (match trap1, trap2 with
       | TRAP, TRAP | NOTRAP, NOTRAP => true
       | TRAP, NOTRAP | NOTRAP, TRAP => false
      end).
Lemma trapping_mode_eq_correct t1 t2:
  WHEN trapping_mode_eq t1 t2 ~> b THEN b = true -> t1 = t2.
Proof.
  wlp_simplify.
  destruct t1; destruct t2; trivial; discriminate.
Qed.
Hint Resolve trapping_mode_eq_correct: wlp.

Definition load_op_eq (o1 o2: load_op): ?? bool :=
  match o1 with
  | OLoadRRO n1 trap ofs1 =>
    match o2 with
    | OLoadRRO n2 trap2 ofs2 => iandb (phys_eq n1 n2) (iandb (offset_eq ofs1 ofs2) (trapping_mode_eq trap trap2))
    | _ => RET false
    end
  | OLoadRRR n1 trap =>
    match o2 with
    | OLoadRRR n2 trap2 => iandb (phys_eq n1 n2) (trapping_mode_eq trap trap2) 
    | _ => RET false
    end
  | OLoadRRRXS n1 trap =>
    match o2 with
    | OLoadRRRXS n2 trap2 => iandb (phys_eq n1 n2) (trapping_mode_eq trap trap2)
    | _ => RET false
    end
  end.

Lemma load_op_eq_correct o1 o2:
  WHEN load_op_eq o1 o2 ~> b THEN b = true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify; try discriminate.
  { f_equal.
    destruct trap, trap0; simpl in *; trivial; discriminate.
    pose (Ptrofs.eq_spec ofs ofs0).
    rewrite H in *. trivial. }
  all: destruct trap, trap0; simpl in *; trivial; discriminate.
Qed.
Hint Resolve load_op_eq_correct: wlp.
Opaque load_op_eq_correct.

Definition store_op_eq (o1 o2: store_op): ?? bool :=
  match o1 with
  | OStoreRRO n1 ofs1 =>
     match o2 with OStoreRRO n2 ofs2 => iandb (phys_eq n1 n2) (offset_eq ofs1 ofs2) | _ => RET false end
  | OStoreRRR n1 =>
     match o2 with OStoreRRR n2 => phys_eq n1 n2 | _ => RET false end
  | OStoreRRRXS n1 =>
     match o2 with OStoreRRRXS n2 => phys_eq n1 n2 | _ => RET false end
  end.

Lemma store_op_eq_correct o1 o2:
  WHEN store_op_eq o1 o2 ~> b THEN b = true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify; try discriminate.
  - f_equal. pose (Ptrofs.eq_spec ofs ofs0).
    rewrite H in *. trivial.
  - congruence.
  - congruence.
Qed.
Hint Resolve store_op_eq_correct: wlp.
Opaque store_op_eq_correct.

Definition control_op_eq (c1 c2: control_op): ?? bool :=
  match c1 with
  | Oj_l l1 =>
     match c2 with Oj_l l2 => phys_eq l1 l2 | _ => RET false end
  | Ocb bt1 l1 =>
     match c2 with Ocb bt2 l2 => iandb (phys_eq bt1 bt2) (phys_eq l1 l2) | _ => RET false end
  | Ocbu bt1 l1 =>
     match c2 with Ocbu bt2 l2 => iandb (phys_eq bt1 bt2) (phys_eq l1 l2) | _ => RET false end
  | Ojumptable tbl1 =>
     match c2 with Ojumptable tbl2 => phys_eq tbl1 tbl2 | _ => RET false end
  | Odiv =>
     match c2 with Odiv => RET true | _ => RET false end
  | Odivu =>
     match c2 with Odivu => RET true | _ => RET false end
  | OIncremPC sz1 =>
     match c2 with OIncremPC sz2 => RET (Z.eqb sz1 sz2) | _ => RET false end
  | OError =>
     match c2 with OError => RET true | _ => RET false end
  end.

Lemma control_op_eq_correct c1 c2:
  WHEN control_op_eq c1 c2 ~> b THEN b = true -> c1 = c2.
Proof.
  destruct c1, c2; wlp_simplify; try rewrite Z.eqb_eq in * |-; try congruence.
Qed.
Hint Resolve control_op_eq_correct: wlp.
Opaque control_op_eq_correct.

Definition op_eq (o1 o2: op): ?? bool :=
  match o1 with
  | Arith i1 =>
    match o2 with Arith i2 => arith_op_eq i1 i2 | _ => RET false end
  | Load i1 =>
    match o2 with Load i2 => load_op_eq i1 i2 | _ => RET false end
  | Store i1 =>
    match o2 with Store i2 => store_op_eq i1 i2 | _ => RET false end
  | Control i1 =>
    match o2 with Control i2 => control_op_eq i1 i2 | _ => RET false end
  | Allocframe sz1 pos1 =>
    match o2 with Allocframe sz2 pos2 => iandb (RET (Z.eqb sz1 sz2)) (phys_eq pos1 pos2) | _ => RET false end
  | Allocframe2 sz1 pos1 =>
    match o2 with Allocframe2 sz2 pos2 => iandb (RET (Z.eqb sz1 sz2)) (phys_eq pos1 pos2) | _ => RET false end
  | Freeframe sz1 pos1 =>
    match o2 with Freeframe sz2 pos2 => iandb (RET (Z.eqb sz1 sz2)) (phys_eq pos1 pos2) | _ => RET false end
  | Freeframe2 sz1 pos1 =>
    match o2 with Freeframe2 sz2 pos2 => iandb (RET (Z.eqb sz1 sz2)) (phys_eq pos1 pos2) | _ => RET false end
  | Constant c1 =>
    match o2 with Constant c2 => phys_eq c1 c2 | _ => RET false end
  | Fail =>
    match o2 with Fail => RET true | _ => RET false end
  end.

Theorem op_eq_correct o1 o2: 
 WHEN op_eq o1 o2 ~> b THEN b=true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify; try rewrite Z.eqb_eq in * |- ; try congruence.
Qed.
Hint Resolve op_eq_correct: wlp.
Global Opaque op_eq_correct.

End IMPPARAM.

End P.

Module L <: ISeqLanguage with Module LP:=P.

Module LP:=P.

Include MkSeqLanguage P.

End L.

Module IST := ImpSimu L ImpPosDict.

Import L.
Import P.

(** Compilation from Asmblock to L *)

Local Open Scope positive_scope.

Definition pmem : R.t := 1.

Definition ireg_to_pos (ir: ireg) : R.t :=
  match ir with
  | GPR0  =>  1 | GPR1  =>  2 | GPR2  =>  3 | GPR3  =>  4 | GPR4  =>  5 | GPR5  =>  6 | GPR6  =>  7 | GPR7  =>  8 | GPR8  =>  9 | GPR9  => 10
  | GPR10 => 11 | GPR11 => 12 | GPR12 => 13 | GPR13 => 14 | GPR14 => 15 | GPR15 => 16 | GPR16 => 17 | GPR17 => 18 | GPR18 => 19 | GPR19 => 20
  | GPR20 => 21 | GPR21 => 22 | GPR22 => 23 | GPR23 => 24 | GPR24 => 25 | GPR25 => 26 | GPR26 => 27 | GPR27 => 28 | GPR28 => 29 | GPR29 => 30
  | GPR30 => 31 | GPR31 => 32 | GPR32 => 33 | GPR33 => 34 | GPR34 => 35 | GPR35 => 36 | GPR36 => 37 | GPR37 => 38 | GPR38 => 39 | GPR39 => 40
  | GPR40 => 41 | GPR41 => 42 | GPR42 => 43 | GPR43 => 44 | GPR44 => 45 | GPR45 => 46 | GPR46 => 47 | GPR47 => 48 | GPR48 => 49 | GPR49 => 50
  | GPR50 => 51 | GPR51 => 52 | GPR52 => 53 | GPR53 => 54 | GPR54 => 55 | GPR55 => 56 | GPR56 => 57 | GPR57 => 58 | GPR58 => 59 | GPR59 => 60
  | GPR60 => 61 | GPR61 => 62 | GPR62 => 63 | GPR63 => 64
  end
.

Lemma ireg_to_pos_discr: forall r r', r <> r' -> ireg_to_pos r <> ireg_to_pos r'.
Proof.
  destruct r; destruct r'; try contradiction; discriminate.
Qed.

Definition ppos (r: preg) : R.t :=
  match r with
  | RA => 2
  | PC => 3
  | IR ir => 3 + ireg_to_pos ir
  end
.

Notation "# r" := (ppos r) (at level 100, right associativity).

Lemma not_eq_add:
  forall k n n', n <> n' -> k + n <> k + n'.
Proof.
  intros k n n' H1 H2. apply H1; clear H1. eapply Pos.add_reg_l; eauto.
Qed.

Lemma ppos_discr: forall r r', r <> r' -> ppos r <> ppos r'.
Proof.
  destruct r; destruct r'.
  all: try discriminate; try contradiction.
  - intros. apply not_eq_add. apply ireg_to_pos_discr. congruence.
  - intros. unfold ppos. cutrewrite (3 + ireg_to_pos g = (1 + ireg_to_pos g) + 2). apply Pos.add_no_neutral.
    apply eq_sym. rewrite Pos.add_comm. rewrite Pos.add_assoc. reflexivity.
  - intros. unfold ppos. rewrite Pos.add_comm. apply Pos.add_no_neutral.
  - intros. unfold ppos. apply not_eq_sym.
    cutrewrite (3 + ireg_to_pos g = (1 + ireg_to_pos g) + 2). apply Pos.add_no_neutral.
    apply eq_sym. rewrite Pos.add_comm. rewrite Pos.add_assoc. reflexivity.
  - intros. unfold ppos. apply not_eq_sym. rewrite Pos.add_comm. apply Pos.add_no_neutral.
Qed.

Lemma ppos_pmem_discr: forall r, pmem <> ppos r.
Proof.
  intros. destruct r.
  - unfold ppos. unfold pmem. apply not_eq_sym. rewrite Pos.add_comm. cutrewrite (3 = 2 + 1). rewrite Pos.add_assoc. apply Pos.add_no_neutral.
    reflexivity.
  - unfold ppos. unfold pmem. discriminate.
  - unfold ppos. unfold pmem. discriminate.
Qed.

(** Inversion functions, used for debug traces *)

Definition pos_to_ireg (p: R.t) : option gpreg :=
  match p with
  | 1 => Some GPR0 | 2 => Some GPR1 | 3 => Some GPR2 | 4 => Some GPR3 | 5 => Some GPR4 | 6 => Some GPR5 | 7 => Some GPR6 | 8 => Some GPR7 | 9 => Some GPR8 | 10 => Some GPR9
  | 11 => Some GPR10 | 12 => Some GPR11 | 13 => Some GPR12 | 14 => Some GPR13 | 15 => Some GPR14 | 16 => Some GPR15 | 17 => Some GPR16 | 18 => Some GPR17 | 19 => Some GPR18 | 20 => Some GPR19
  | 21 => Some GPR20 | 22 => Some GPR21 | 23 => Some GPR22 | 24 => Some GPR23 | 25 => Some GPR24 | 26 => Some GPR25 | 27 => Some GPR26 | 28 => Some GPR27 | 29 => Some GPR28 | 30 => Some GPR29
  | 31 => Some GPR30 | 32 => Some GPR31 | 33 => Some GPR32 | 34 => Some GPR33 | 35 => Some GPR34 | 36 => Some GPR35 | 37 => Some GPR36 | 38 => Some GPR37 | 39 => Some GPR38 | 40 => Some GPR39
  | 41 => Some GPR40 | 42 => Some GPR41 | 43 => Some GPR42 | 44 => Some GPR43 | 45 => Some GPR44 | 46 => Some GPR45 | 47 => Some GPR46 | 48 => Some GPR47 | 49 => Some GPR48 | 50 => Some GPR49
  | 51 => Some GPR50 | 52 => Some GPR51 | 53 => Some GPR52 | 54 => Some GPR53 | 55 => Some GPR54 | 56 => Some GPR55 | 57 => Some GPR56 | 58 => Some GPR57 | 59 => Some GPR58 | 60 => Some GPR59
  | 61 => Some GPR60 | 62 => Some GPR61 | 63 => Some GPR62 | 64 => Some GPR63
  | _ => None
  end.

Definition inv_ppos (p: R.t) : option preg :=
  match p with
  | 1 => None
  | 2 => Some RA | 3 => Some PC
  | n => match pos_to_ireg (n-3) with
       | None => None
       | Some gpr => Some (IR gpr)
       end
  end.

Notation "a @ b" := (Econs a b) (at level 102, right associativity).

Definition trans_control (ctl: control) : inst :=
  match ctl with
  | Pret => [(#PC, PReg(#RA))]
  | Pcall s => [(#RA, PReg(#PC)); (#PC, Op (Arith (OArithR (Ploadsymbol s Ptrofs.zero))) Enil)]
  | Picall r => [(#RA, PReg(#PC)); (#PC, PReg(#r))]
  | Pgoto s => [(#PC, Op (Arith (OArithR (Ploadsymbol s Ptrofs.zero))) Enil)]
  | Pigoto r => [(#PC, PReg(#r))]
  | Pj_l l => [(#PC, Op (Control (Oj_l l)) (PReg(#PC) @ Enil))]
  | Pcb bt r l => [(#PC, Op (Control (Ocb bt l)) (PReg(#r) @ PReg(#PC) @ Enil))]
  | Pcbu bt r l => [(#PC, Op (Control (Ocbu bt l)) (PReg(#r) @ PReg(#PC) @ Enil))]
  | Pjumptable r labels => [(#PC, Op (Control (Ojumptable labels)) (PReg(#r) @ PReg(#PC) @ Enil));
                            (#GPR62, Op (Constant Vundef) Enil);
                            (#GPR63, Op (Constant Vundef) Enil) ]
  | Pbuiltin ef args res => [(#PC, Op (Control (OError)) Enil)]
  end.

Definition trans_exit (ex: option control) : L.inst :=
  match ex with
  | None => []
  | Some ctl => trans_control ctl
  end
.

Definition trans_arith (ai: ar_instruction) : inst :=
  match ai with
  | PArithR n d => [(#d, Op (Arith (OArithR n)) Enil)]
  | PArithRR n d s => [(#d, Op (Arith (OArithRR n)) (PReg(#s) @ Enil))]
  | PArithRI32 n d i => [(#d, Op (Arith (OArithRI32 n i)) Enil)]
  | PArithRI64 n d i => [(#d, Op (Arith (OArithRI64 n i)) Enil)]
  | PArithRF32 n d i => [(#d, Op (Arith (OArithRF32 n i)) Enil)]
  | PArithRF64 n d i => [(#d, Op (Arith (OArithRF64 n i)) Enil)]
  | PArithRRR n d s1 s2 => [(#d, Op (Arith (OArithRRR n)) (PReg(#s1) @ PReg(#s2) @ Enil))]
  | PArithRRI32 n d s i => [(#d, Op (Arith (OArithRRI32 n i)) (PReg(#s) @ Enil))]
  | PArithRRI64 n d s i => [(#d, Op (Arith (OArithRRI64 n i)) (PReg(#s) @ Enil))]
  | PArithARRR n d s1 s2 => [(#d, Op (Arith (OArithARRR n)) (PReg(#d) @ PReg(#s1) @ PReg(#s2) @ Enil))]
  | PArithARR n d s => [(#d, Op (Arith (OArithARR n)) (PReg(#d) @ PReg(#s) @ Enil))]
  | PArithARRI32 n d s i => [(#d, Op (Arith (OArithARRI32 n i)) (PReg(#d) @ PReg(#s) @ Enil))]
  | PArithARRI64 n d s i => [(#d, Op (Arith (OArithARRI64 n i)) (PReg(#d) @ PReg(#s) @ Enil))]
  end.


Definition trans_basic (b: basic) : inst :=
  match b with
  | PArith ai => trans_arith ai
  | PLoadRRO trap n d a ofs => [(#d, Op (Load (OLoadRRO n trap ofs)) (PReg (#a) @ PReg pmem @ Enil))]
  | PLoadRRR trap n d a ro =>  [(#d, Op (Load (OLoadRRR n trap)) (PReg (#a) @ PReg (#ro) @ PReg pmem @ Enil))]
  | PLoadRRRXS trap n d a ro =>  [(#d, Op (Load (OLoadRRRXS n trap)) (PReg (#a) @ PReg (#ro) @ PReg pmem @ Enil))]
  | PStoreRRO n s a ofs => [(pmem, Op (Store (OStoreRRO n ofs)) (PReg (#s) @ PReg (#a) @ PReg pmem @ Enil))]
  | PLoadQRRO qd a ofs =>
    let (d0, d1) := gpreg_q_expand qd in
      [(#d0, Op (Load (OLoadRRO Pld_a TRAP ofs)) (PReg (#a) @ PReg pmem @ Enil));
       (#d1, Op (Load (OLoadRRO Pld_a TRAP (Ptrofs.add ofs (Ptrofs.repr 8)))) (Old(PReg (#a)) @ PReg pmem @ Enil))]
  | PLoadORRO od a ofs =>
    match gpreg_o_expand od with
    | (d0, d1, d2, d3) =>
        [(#d0, Op (Load (OLoadRRO Pld_a TRAP ofs)) (PReg (#a) @ PReg pmem @ Enil));
         (#d1, Op (Load (OLoadRRO Pld_a TRAP (Ptrofs.add ofs (Ptrofs.repr 8)))) (Old(PReg (#a)) @ PReg pmem @ Enil));
         (#d2, Op (Load (OLoadRRO Pld_a TRAP (Ptrofs.add ofs (Ptrofs.repr 16)))) (Old(PReg (#a)) @ PReg pmem @ Enil));
         (#d3, Op (Load (OLoadRRO Pld_a TRAP (Ptrofs.add ofs (Ptrofs.repr 24)))) (Old(PReg (#a)) @ PReg pmem @ Enil))]
    end
  | PStoreRRR n s a ro => [(pmem, Op (Store (OStoreRRR n)) (PReg (#s) @ PReg (#a) @ PReg (#ro) @ PReg pmem @ Enil))]
  | PStoreRRRXS n s a ro => [(pmem, Op (Store (OStoreRRRXS n)) (PReg (#s) @ PReg (#a) @ PReg (#ro) @ PReg pmem @ Enil))]
  | PStoreQRRO qs a ofs =>
    let (s0, s1) := gpreg_q_expand qs in 
    [(pmem, Op (Store (OStoreRRO Psd_a ofs)) (PReg (#s0) @ PReg (#a) @ PReg pmem @ Enil));
     (pmem, Op (Store (OStoreRRO Psd_a (Ptrofs.add ofs (Ptrofs.repr 8)))) (PReg (#s1) @ PReg (#a) @ PReg pmem @ Enil))]
  | PStoreORRO os a ofs =>
    match gpreg_o_expand os with
    | (s0, s1, s2, s3) =>
      [(pmem, Op (Store (OStoreRRO Psd_a ofs)) (PReg (#s0) @ PReg (#a) @ PReg pmem @ Enil));
       (pmem, Op (Store (OStoreRRO Psd_a (Ptrofs.add ofs (Ptrofs.repr 8)))) (PReg (#s1) @ PReg (#a) @ PReg pmem @ Enil));
       (pmem, Op (Store (OStoreRRO Psd_a (Ptrofs.add ofs (Ptrofs.repr 16)))) (PReg (#s2) @ PReg (#a) @ PReg pmem @ Enil));
       (pmem, Op (Store (OStoreRRO Psd_a (Ptrofs.add ofs (Ptrofs.repr 24)))) (PReg (#s3) @ PReg (#a) @ PReg pmem @ Enil))]
    end
  | Pallocframe sz pos => [(#FP, PReg (#SP)); (#SP, Op (Allocframe2 sz pos) (PReg (#SP) @ PReg pmem @ Enil)); (#RTMP, Op (Constant Vundef) Enil);
                           (pmem, Op (Allocframe sz pos) (Old (PReg (#SP)) @ PReg pmem @ Enil))]
  | Pfreeframe sz pos => [(pmem, Op (Freeframe sz pos) (PReg (#SP) @ PReg pmem @ Enil));
                          (#SP, Op (Freeframe2 sz pos) (PReg (#SP) @ Old (PReg pmem) @ Enil));
                          (#RTMP, Op (Constant Vundef) Enil)]
  | Pget rd ra => match ra with
                  | RA => [(#rd, PReg(#ra))]
                  | _ => [(#rd, Op Fail Enil)]
                  end
  | Pset ra rd => match ra with
                  | RA => [(#ra, PReg(#rd))]
                  | _ => [(#rd, Op Fail Enil)]
                  end
  | Pnop => []
  end.

Fixpoint trans_body (b: list basic) : list L.inst :=
  match b with
  | nil => nil
  | b :: lb => (trans_basic b) :: (trans_body lb)
  end.

Definition trans_pcincr (sz: Z) (k: L.inst) := (#PC, Op (Control (OIncremPC sz)) (PReg(#PC) @ Enil)) :: k.

Definition trans_block (b: Asmvliw.bblock) : L.bblock :=
  trans_body (body b) ++ (trans_pcincr (size b) (trans_exit (exit b)) :: nil).

Theorem trans_block_noheader_inv: forall bb, trans_block (no_header bb) = trans_block bb.
Proof.
  intros. destruct bb as [hd bdy ex COR]; unfold no_header; simpl. unfold trans_block. simpl. reflexivity.
Qed.

Theorem trans_block_header_inv: forall bb hd, trans_block (stick_header hd bb) = trans_block bb.
Proof.
  intros. destruct bb as [hdr bdy ex COR]; unfold no_header; simpl. unfold trans_block. simpl. reflexivity.
Qed.

Definition state := L.mem.
Definition exec := L.run.

Definition match_states (s: Asmvliw.state) (s': state) :=
  let (rs, m) := s in
     s' pmem = Memstate m
  /\ forall r, s' (#r) = Val (rs r).

Definition match_outcome (o:outcome) (s: option state) :=
  match o with
  | Next rs m => exists s', s=Some s' /\ match_states (State rs m) s'
  | Stuck => s=None
  end.
 
Notation "a <[ b <- c ]>" := (assign a b c) (at level 102, right associativity).

Definition trans_state (s: Asmvliw.state) : state :=
  let (rs, m) := s in
  fun x => if (Pos.eq_dec x pmem) then Memstate m
           else match (inv_ppos x) with
           | Some r => Val (rs r)
           | None => Val Vundef
           end.

Lemma not_eq_IR:
  forall r r', r <> r' -> IR r <> IR r'.
Proof.
  intros. congruence.
Qed.

(** Parallelizability test of a bblock (bundle), and bisimulation of the Asmblock and L parallel semantics *)

Module PChk := ParallelChecks L PosPseudoRegSet.

Definition bblock_para_check (p: Asmvliw.bblock) : bool :=
  PChk.is_parallelizable (trans_block p).

Section SECT_PAR.

Import PChk.

Ltac Simplif :=
  ((rewrite nextblock_inv by eauto with asmgen)
  || (rewrite nextblock_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextblock_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)
  || (rewrite assign_diff by (auto; try discriminate; try (apply ppos_discr; try discriminate; congruence); try (apply ppos_pmem_discr); 
                                    try (apply not_eq_sym; apply ppos_discr; try discriminate; congruence); try (apply not_eq_sym; apply ppos_pmem_discr); auto))
  || (rewrite assign_eq)
  ); auto with asmgen.

Ltac Simpl := repeat Simplif.

Arguments Pos.add: simpl never.
Arguments ppos: simpl never.

Variable Ge: genv.

Lemma trans_arith_par_correct ge fn rsr mr sr rsw mw sw rsw' i:
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_states (State rsw mw) sw ->
  parexec_arith_instr ge i rsr rsw = rsw' ->
  exists sw',
     inst_prun Ge (trans_arith i) sw sr sr = Some sw'
  /\ match_states (State rsw' mw) sw'.
Proof.
  intros GENV MSR MSW PARARITH. subst. inv MSR. inv MSW.
  unfold parexec_arith_instr. destruct i.
(* Ploadsymbol *)
  - destruct i. eexists; split; [| split].
    * simpl. reflexivity.
    * Simpl.
    * simpl. intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRR *)
  - eexists; split; [| split].
    * simpl. rewrite (H0 rs). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRI32 *)
  - eexists; split; [|split].
    * simpl. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRI64 *)
  - eexists; split; [|split].
    * simpl. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRF32 *)
  - eexists; split; [|split].
    * simpl. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRF64 *)
  - eexists; split; [|split].
    * simpl. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRRR *)
  - eexists; split; [|split].
    * simpl. rewrite (H0 rs1). rewrite (H0 rs2). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRRI32 *)
  - eexists; split; [|split].
    * simpl. rewrite (H0 rs). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRRI64 *)
  - eexists; split; [|split].
    * simpl. rewrite (H0 rs). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithARRR *)
  - eexists; split; [|split].
    * simpl. rewrite (H0 rd). rewrite (H0 rs1). rewrite (H0 rs2). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithARR *)
  -  eexists; split; [|split].
    * simpl. rewrite (H0 rd).  rewrite (H0 rs). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.      
(* PArithARRI32 *)
  - eexists; split; [|split].
    * simpl. rewrite (H0 rd).  rewrite (H0 rs). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithARRI64 *)
  - eexists; split; [|split].
    * simpl. rewrite (H0 rd).  rewrite (H0 rs). reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
Qed.



Theorem bisimu_par_wio_basic ge fn rsr rsw mr mw sr sw bi:
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_states (State rsw mw) sw ->
  match_outcome (bstep ge bi rsr rsw mr mw) (inst_prun Ge (trans_basic bi) sw sr sr).
Proof.

(* a little tactic to automate reasoning on preg_eq *)
Local Hint Resolve not_eq_sym ppos_pmem_discr ppos_discr: core.
Local Ltac preg_eq_discr r rd :=
  destruct (preg_eq r rd); try (subst r; rewrite assign_eq, Pregmap.gss; auto);
  rewrite (assign_diff _ (#rd) (#r) _); auto;
  rewrite Pregmap.gso; auto.

  intros GENV MSR MSW; inversion MSR as (H & H0); inversion MSW as (H1 & H2).
  destruct bi; simpl.
(* Arith *)
  - exploit trans_arith_par_correct. 5: eauto. all: eauto.
(* Load *)
  - destruct i.
    (* Load Offset *)
    + destruct i; simpl load_chunk. all:
      unfold parexec_load_offset; simpl; unfold exec_load_deps_offset; erewrite GENV, H, H0;
      unfold eval_offset;
      simpl; auto;
      destruct (Mem.loadv _ _ _) eqn:MEML; destruct trap; simpl; auto;
      eexists; split; try split; Simpl;
      intros rr; destruct rr; Simpl; destruct (ireg_eq g rd); subst; Simpl.

    (* Load Reg *)
    + destruct i; simpl load_chunk. all:
      unfold parexec_load_reg; simpl; unfold exec_load_deps_reg; rewrite H, H0; rewrite (H0 rofs);
      destruct (Mem.loadv _ _ _) eqn:MEML; destruct trap; simpl; auto;
      eexists; split; try split; Simpl;
      intros rr; destruct rr; Simpl; destruct (ireg_eq g rd); subst; Simpl.

    (* Load Reg XS *)
    + destruct i; simpl load_chunk. all:
      unfold parexec_load_regxs; simpl; unfold exec_load_deps_regxs; rewrite H, H0; rewrite (H0 rofs);
      destruct (Mem.loadv _ _ _) eqn:MEML; destruct trap; simpl; auto;
      eexists; split; try split; Simpl;
      intros rr; destruct rr; Simpl; destruct (ireg_eq g rd); subst; Simpl.

    (* Load Quad word *)
    + unfold parexec_load_q_offset.
      destruct (gpreg_q_expand rd) as [rd0 rd1]; destruct Ge; simpl.
      rewrite H0, H.
      destruct (Mem.loadv Many64 mr _) as [load0 | ]; simpl; auto.
      rewrite !(assign_diff _ _ pmem), H; auto.
      destruct (Mem.loadv Many64 mr (_ _ (Ptrofs.add ofs (Ptrofs.repr 8)))) as [load1| ]; simpl; auto.
      eexists; intuition eauto.
      { rewrite !(assign_diff _ _ pmem); auto. }
      { preg_eq_discr r rd1.
        preg_eq_discr r rd0. }

    (* Load Octuple word *)
    + Local Hint Resolve not_eq_sym ppos_pmem_discr ppos_discr: core.
      unfold parexec_load_o_offset.
      destruct (gpreg_o_expand rd) as [[[rd0 rd1] rd2] rd3]; destruct Ge; simpl.
      rewrite H0, H.
      destruct (Mem.loadv Many64 mr (Val.offset_ptr (rsr ra) ofs)) as [load0 | ]; simpl; auto.
      rewrite !(assign_diff _ _ pmem), !H; auto.
      destruct (Mem.loadv Many64 mr (_ _ (Ptrofs.add ofs (Ptrofs.repr 8)))) as [load1| ]; simpl; auto.
      rewrite !(assign_diff _ _ pmem), !H; auto.
      destruct (Mem.loadv Many64 mr (_ _ (Ptrofs.add ofs (Ptrofs.repr 16)))) as [load2| ]; simpl; auto.
      rewrite !(assign_diff _ _ pmem), !H; auto.
      destruct (Mem.loadv Many64 mr (_ _ (Ptrofs.add ofs (Ptrofs.repr 24)))) as [load3| ]; simpl; auto.
      eexists; intuition eauto.
      { rewrite !(assign_diff _ _ pmem); auto. }
      { preg_eq_discr r rd3.
        preg_eq_discr r rd2.
        preg_eq_discr r rd1.
        preg_eq_discr r rd0. }

(* Store *)
  - destruct i.
    (* Store Offset *)
    + destruct i; simpl store_chunk. all:
      unfold parexec_store_offset; simpl; unfold exec_store_deps_offset; erewrite GENV, H, H0; rewrite (H0 ra);
      unfold eval_offset; simpl; auto;
      destruct (Mem.storev _ _ _ _) eqn:MEML; simpl; auto;
      eexists; split; try split; Simpl;
      intros rr; destruct rr; Simpl.

    (* Store Reg *)
    + destruct i; simpl store_chunk. all:
      unfold parexec_store_reg; simpl; unfold exec_store_deps_reg; rewrite H, H0; rewrite (H0 ra); rewrite (H0 rofs);
      destruct (Mem.storev _ _ _ _) eqn:MEML; simpl; auto;
      eexists; split; try split; Simpl;
      intros rr; destruct rr; Simpl.

    (* Store Reg XS *)
    + destruct i; simpl store_chunk. all:
      unfold parexec_store_regxs; simpl; unfold exec_store_deps_regxs; rewrite H, H0; rewrite (H0 ra); rewrite (H0 rofs);
      destruct (Mem.storev _ _ _ _) eqn:MEML; simpl; auto;
      eexists; split; try split; Simpl;
      intros rr; destruct rr; Simpl.

    (* Store Quad Word *)
    + unfold parexec_store_q_offset.
      destruct (gpreg_q_expand rs) as [s0 s1]; destruct Ge; simpl.
      rewrite !H0, !H.
      destruct (Mem.storev _ _ _ (rsr s0)) as [mem0 | ]; simpl; auto.
      rewrite !assign_diff, !H0; auto.
      destruct (Mem.storev _ _ _ (rsr s1)) as [mem1 | ]; simpl; auto.
      eexists; intuition eauto.
      rewrite !assign_diff; auto.

    (* Store Ocuple Word *)
    + unfold parexec_store_o_offset.
      destruct (gpreg_o_expand rs) as [[[s0 s1] s2] s3]; destruct Ge; simpl.
      rewrite !H0, !H.
      destruct (Mem.storev _ _ _ (rsr s0)) as [store0 | ]; simpl; auto.
      rewrite !assign_diff, !H0; auto.
      destruct (Mem.storev _ _ _ (rsr s1)) as [store1 | ]; simpl; auto.
      rewrite !assign_diff, !H0; auto.
      destruct (Mem.storev _ _ _ (rsr s2)) as [store2 | ]; simpl; auto.
      rewrite !assign_diff, !H0; auto.
      destruct (Mem.storev _ _ _ (rsr s3)) as [store3 | ]; simpl; auto.
      eexists; intuition eauto.
      rewrite !assign_diff; auto.

  (* Allocframe *)
  - destruct (Mem.alloc _ _ _) eqn:MEMAL. destruct (Mem.store _ _ _ _) eqn:MEMS.
    * eexists; repeat split.
      { Simpl. erewrite !H0, H, MEMAL, MEMS. Simpl.
      rewrite H, MEMAL. rewrite MEMS. reflexivity. }
      { Simpl. }
      { intros rr; destruct rr; Simpl.
        destruct (ireg_eq g GPR32); [| destruct (ireg_eq g GPR12); [| destruct (ireg_eq g GPR17)]]; subst; Simpl. }
    * simpl; Simpl; erewrite !H0, H, MEMAL, MEMS; auto.
  (* Freeframe *)
  - erewrite !H0, H.
    destruct (Mem.loadv _ _ _) eqn:MLOAD; simpl; auto.
    destruct (rsr GPR12) eqn:SPeq; simpl; auto.
    destruct (Mem.free _ _ _ _) eqn:MFREE; simpl; auto.
    eexists; repeat split.
    * simpl. Simpl. erewrite H0, SPeq, MLOAD, MFREE. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl. destruct (ireg_eq g GPR32); [| destruct (ireg_eq g GPR12); [| destruct (ireg_eq g GPR17)]]; subst; Simpl.
(* Pget *)
  - destruct rs eqn:rseq; simpl; auto.
    eexists. repeat split. Simpl. intros rr; destruct rr; Simpl.
    destruct (ireg_eq g rd); subst; Simpl.
(* Pset *)
  - destruct rd eqn:rdeq; simpl; auto.
    eexists. repeat split. Simpl. intros rr; destruct rr; Simpl.
(* Pnop *)
  - eexists. repeat split; assumption.
Qed.


Theorem bisimu_par_body:
  forall bdy ge fn rsr mr sr rsw mw sw,
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_states (State rsw mw) sw ->
  match_outcome (parexec_wio_body ge bdy rsr rsw mr mw) (prun_iw Ge (trans_body bdy) sw sr).
Proof.
  induction bdy as [|i bdy]; simpl; eauto. 
  intros.
  exploit (bisimu_par_wio_basic ge fn rsr rsw mr mw sr sw i); eauto.
  destruct (bstep _ _ _ _ _ _); simpl.
  - intros (s' & X1 & X2). rewrite X1; simpl; eauto.
  - intros X; rewrite X; simpl; auto.
Qed.

Theorem bisimu_par_control ex sz aux ge fn rsr rsw mr mw sr sw:
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_states (State rsw mw) sw ->
  match_outcome (parexec_control ge fn ex (incrPC (Ptrofs.repr sz) rsr) (rsw#PC <- aux) mw) (inst_prun Ge (trans_pcincr sz (trans_exit ex)) sw sr sr).
Proof.
  intros GENV MSR MSW; unfold estep.
  simpl in *. inv MSR. inv MSW.
  destruct ex.
  - destruct c; destruct i; try discriminate; simpl.
    all: try (rewrite (H0 PC); eexists; split; try split; Simpl; intros rr; destruct rr; unfold incrPC; Simpl).

    (* Pjumptable *)
    + rewrite (H0 PC). Simpl. rewrite (H0 r). unfold incrPC. Simpl.
      destruct (rsr r); simpl; auto. destruct (list_nth_z _ _); simpl; auto.
      unfold par_goto_label. unfold goto_label_deps. destruct (label_pos _ _ _); simpl; auto. Simpl.
      destruct (Val.offset_ptr _ _); simpl; auto.
      eexists; split; try split; Simpl. intros rr; destruct rr; unfold incrPC; Simpl.
      destruct (preg_eq g GPR62). rewrite e. Simpl.
      destruct (preg_eq g GPR63). rewrite e. Simpl. Simpl.

    (* Pj_l *)
    + rewrite (H0 PC). Simpl. unfold par_goto_label. unfold goto_label_deps. destruct (label_pos _ _ _); simpl; auto.
      unfold incrPC. Simpl. destruct (Val.offset_ptr _ _); simpl; auto.
      eexists; split; try split; Simpl. intros rr; destruct rr; unfold incrPC; Simpl.

    (* Pcb *)
    + rewrite (H0 PC). Simpl. rewrite (H0 r). destruct (cmp_for_btest _); simpl; auto. destruct o; simpl; auto.
      unfold par_eval_branch. unfold eval_branch_deps. unfold incrPC. Simpl. destruct i.
      ++ destruct (Val.cmp_bool _ _ _); simpl; auto. destruct b.
         +++ unfold par_goto_label. unfold goto_label_deps. destruct (label_pos _ _ _); simpl; auto. Simpl.
             destruct (Val.offset_ptr _ _); simpl; auto. eexists; split; try split; Simpl.
             intros rr; destruct rr; Simpl.
         +++ repeat (econstructor; eauto). intros rr; destruct rr; Simpl.
      ++ destruct (Val.cmpl_bool _ _ _); simpl; auto. destruct b.
         +++ unfold par_goto_label. unfold goto_label_deps. destruct (label_pos _ _ _); simpl; auto. Simpl.
             destruct (Val.offset_ptr _ _); simpl; auto. eexists; split; try split; Simpl.
             intros rr; destruct rr; Simpl.
         +++ repeat (econstructor; eauto). intros rr; destruct rr; Simpl.

    (* Pcbu *)
    + rewrite (H0 PC). Simpl. rewrite (H0 r). destruct (cmpu_for_btest _); simpl; auto. destruct o; simpl; auto.
      unfold par_eval_branch. unfold eval_branch_deps. unfold incrPC. Simpl. destruct i.
      ++ destruct (Val_cmpu_bool _ _ _); simpl; auto. destruct b.
         +++ unfold par_goto_label. unfold goto_label_deps. destruct (label_pos _ _ _); simpl; auto. Simpl.
             destruct (Val.offset_ptr _ _); simpl; auto. eexists; split; try split; Simpl.
             intros rr; destruct rr; Simpl.
         +++ repeat (econstructor; eauto). intros rr; destruct rr; Simpl.
      ++ destruct (Val_cmplu_bool _ _ _); simpl; auto. destruct b.
         +++ unfold par_goto_label. unfold goto_label_deps. destruct (label_pos _ _ _); simpl; auto. Simpl.
             destruct (Val.offset_ptr _ _); simpl; auto. eexists; split; try split; Simpl.
             intros rr; destruct rr; Simpl.
         +++ repeat (econstructor; eauto). intros rr; destruct rr; Simpl.

  - simpl in *. rewrite (H0 PC). eexists; split; try split; Simpl.
    intros rr; destruct rr; unfold incrPC; Simpl.
Qed.

Theorem bisimu_par_exit ex sz ge fn rsr rsw mr mw sr sw:
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_states (State rsw mw) sw ->
  match_outcome (estep ge fn ex (Ptrofs.repr sz) rsr rsw mw) (inst_prun Ge (trans_pcincr sz (trans_exit ex)) sw sr sr).
Proof.
  intros; unfold estep.
  exploit (bisimu_par_control ex sz rsw#PC ge fn rsr rsw mr mw sr sw); eauto.
  cutrewrite (rsw # PC <- (rsw PC) = rsw); auto.
  apply extensionality. intros; destruct x; simpl; auto.
Qed.

Definition trans_block_aux bdy sz ex := (trans_body bdy) ++ (trans_pcincr sz (trans_exit ex) :: nil).

Theorem bisimu_par_wio ge fn rsr mr sr bdy ex sz:
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_outcome (parexec_wio ge fn bdy ex (Ptrofs.repr sz) rsr mr) (prun_iw Ge (trans_block_aux bdy sz ex) sr sr).
Proof.
  intros GENV MSR. unfold parexec_wio, trans_block_aux.
  exploit (bisimu_par_body bdy ge fn rsr mr sr rsr mr sr); eauto.
  destruct (parexec_wio_body _ _ _ _ _ _); simpl.
  - intros (s' & X1 & X2).
    erewrite prun_iw_app_Some; eauto.
    exploit (bisimu_par_exit ex sz ge fn rsr rs mr m sr s'); eauto.
    subst Ge; simpl. destruct MSR as (Y1 & Y2). erewrite Y2; simpl.
    destruct (inst_prun _ _ _ _ _); simpl; auto.
  - intros X; erewrite prun_iw_app_None; eauto.
Qed.

Theorem bisimu_par_wio_bblock ge fn rsr mr sr bdy1 bdy2 ex sz:
  Ge = Genv ge fn ->
  match_states (State rsr mr) sr ->
  match_outcome 
   match parexec_wio ge fn bdy1 ex (Ptrofs.repr sz) rsr mr with
   | Next rs' m' => parexec_wio_body ge bdy2 rsr rs' mr m'
   | Stuck => Stuck
   end
   (prun_iw Ge ((trans_block_aux bdy1 sz ex)++(trans_body bdy2)) sr sr).
Proof.
  intros.
  exploit (bisimu_par_wio ge fn rsr mr sr bdy1 ex sz); eauto.
  destruct (parexec_wio _ _ _ _ _ _); simpl.
  - intros (s' & X1 & X2).
    erewrite prun_iw_app_Some; eauto.
    eapply bisimu_par_body; eauto.
  - intros; erewrite prun_iw_app_None; eauto.
Qed.

Lemma trans_body_perserves_permutation bdy1 bdy2:
  Permutation bdy1 bdy2 ->
  Permutation (trans_body bdy1) (trans_body bdy2).
Proof.
  induction 1; simpl; econstructor; eauto.
Qed.

Lemma trans_body_app bdy1: forall bdy2,
   trans_body (bdy1++bdy2) = (trans_body bdy1) ++ (trans_body bdy2).
Proof.
  induction bdy1; simpl; congruence.
Qed.

Theorem trans_block_perserves_permutation bdy1 bdy2 b:
  Permutation (bdy1 ++ bdy2) (body b) ->
  Permutation (trans_block b) ((trans_block_aux bdy1 (size b) (exit b))++(trans_body bdy2)).
Proof.
  intro H; unfold trans_block, trans_block_aux.
  eapply perm_trans.
  - eapply Permutation_app_tail. 
    apply trans_body_perserves_permutation.
    apply Permutation_sym; eapply H.
  - rewrite trans_body_app. rewrite <-! app_assoc.
    apply Permutation_app_head.
    apply Permutation_app_comm.
Qed.

Theorem bisimu_par rs1 m1 s1' b ge fn o2:
    Ge = Genv ge fn ->
    match_states (State rs1 m1) s1' -> 
    parexec_bblock ge fn b rs1 m1 o2 ->
  exists o2',
     prun Ge (trans_block b) s1' o2'
  /\ match_outcome o2 o2'.
Proof.
  intros GENV MS PAREXEC.
  inversion PAREXEC as (bdy1 & bdy2 & PERM & WIO).
  exploit trans_block_perserves_permutation; eauto.
  intros Perm.
  exploit (bisimu_par_wio_bblock ge fn rs1 m1 s1' bdy1 bdy2 (exit b) (size b)); eauto.
  rewrite <- WIO. clear WIO.
  intros H; eexists; split. 2: eapply H.
  unfold prun; eexists; split; eauto. 
  destruct (prun_iw _ _ _ _); simpl; eauto.
Qed.

(** sequential execution *)
Theorem bisimu_basic ge fn bi rs m s:
  Ge = Genv ge fn ->
  match_states (State rs m) s ->
  match_outcome (exec_basic_instr ge bi rs m) (inst_run Ge (trans_basic bi) s s).
Proof.
  intros; unfold exec_basic_instr. rewrite inst_run_prun.
  eapply bisimu_par_wio_basic; eauto.
Qed.

Lemma bisimu_body:
  forall bdy ge fn rs m s,
  Ge = Genv ge fn ->
  match_states (State rs m) s ->
  match_outcome (exec_body ge bdy rs m) (exec Ge (trans_body bdy) s).
Proof.
  induction bdy as [|i bdy]; simpl; eauto. 
  intros.
  exploit (bisimu_basic ge fn i rs m s); eauto.
  destruct (exec_basic_instr _ _ _ _); simpl.
  - intros (s' & X1 & X2). rewrite X1; simpl; eauto.
  - intros X; rewrite X; simpl; auto.
Qed.

Theorem bisimu_exit ge fn b rs m s:
  Ge = Genv ge fn ->
  match_states (State rs m) s ->
  match_outcome (exec_control ge fn (exit b) (nextblock b rs) m) (inst_run Ge (trans_pcincr (size b) (trans_exit (exit b))) s s).
Proof.
  intros; unfold exec_control, nextblock. rewrite inst_run_prun. 
  apply (bisimu_par_control (exit b) (size b) (Val.offset_ptr (rs PC) (Ptrofs.repr (size b))) ge fn rs rs m m s s); auto.
Qed.

Theorem bisimu rs m b ge fn s:
    Ge = Genv ge fn ->
    match_states (State rs m) s -> 
    match_outcome (exec_bblock ge fn b rs m) (exec Ge (trans_block b) s).
Proof.
  intros GENV MS. unfold exec_bblock.
  exploit (bisimu_body (body b) ge fn rs m s); eauto.
  unfold exec, trans_block; simpl.
  destruct (exec_body _ _ _ _); simpl.
  - intros (s' & X1 & X2).
    erewrite run_app_Some; eauto.
    exploit (bisimu_exit ge fn b rs0 m0 s'); eauto.
    subst Ge; simpl. destruct X2 as (Y1 & Y2). erewrite Y2; simpl.
    destruct (inst_run _ _ _); simpl; auto.
  - intros X; erewrite run_app_None; eauto.
Qed.


Theorem trans_state_match: forall S, match_states S (trans_state S).
Proof.
  intros. destruct S as (rs & m). simpl.
  split. reflexivity.
  intro. destruct r; try reflexivity.
  destruct g; reflexivity.
Qed.


Lemma state_eq_decomp:
  forall rs1 m1 rs2 m2, rs1 = rs2 -> m1 = m2 -> State rs1 m1 = State rs2 m2.
Proof.
  intros. congruence.
Qed.

Theorem state_equiv S1 S2 S': match_states S1 S' -> match_states S2 S' -> S1 = S2.
Proof.
  unfold match_states; intros H0 H1. destruct S1 as (rs1 & m1). destruct S2 as (rs2 & m2). inv H0. inv H1.
  apply state_eq_decomp.
  - apply functional_extensionality. intros. assert (Val (rs1 x) = Val (rs2 x)) by congruence. congruence.
  - congruence.
Qed.

Lemma bblock_para_check_correct ge fn bb rs m rs' m':
  Ge = Genv ge fn ->
  exec_bblock ge fn bb rs m = Next rs' m' ->
  bblock_para_check bb = true ->
  det_parexec ge fn bb rs m rs' m'.
Proof.
  intros H H0 H1 o H2. unfold bblock_para_check in H1.
  exploit (bisimu rs m bb ge fn); eauto. eapply trans_state_match.
  rewrite H0; simpl.
  intros (s2' & EXEC & MS).
  exploit bisimu_par. 2: apply (trans_state_match (State rs m)). all: eauto.
  intros (o2' & PRUN & MO).
  exploit parallelizable_correct. apply is_para_correct_aux. eassumption.
  intro. eapply H3 in PRUN. clear H3. destruct o2'.
  - inv PRUN. inv H3. unfold exec in EXEC; unfold trans_state in H.
    assert (x = s2') by congruence. subst. clear H.
    assert (m0 = s2') by (apply functional_extensionality; auto). subst. clear H4.
    destruct o; try discriminate. inv MO. inv H. assert (s2' = x) by congruence. subst.
    exploit (state_equiv (State rs' m') (State rs0 m0)).
    2: eapply H4. eapply MS. intro H. inv H. reflexivity.
  - unfold match_outcome in MO. destruct o.
    + inv MO. inv H3. discriminate.
    + clear MO. unfold exec in EXEC.
      unfold trans_state in PRUN; rewrite EXEC in PRUN. discriminate.
Qed.

End SECT_PAR.

Section SECT_BBLOCK_EQUIV.

Variable Ge: genv.

Local Hint Resolve trans_state_match: core.

Lemma bblock_simu_reduce:
  forall p1 p2 ge fn,
  Ge = Genv ge fn ->
  L.bblock_simu Ge (trans_block p1) (trans_block p2) ->
  Asmblockprops.bblock_simu ge fn p1 p2.
Proof.
  unfold bblock_simu, res_eq; intros p1 p2 ge fn H1 H2 rs m DONTSTUCK.
  generalize (H2 (trans_state (State rs m))); clear H2.
  intro H2. 
  exploit (bisimu Ge rs m p1 ge fn (trans_state (State rs m))); eauto.
  exploit (bisimu Ge rs m p2 ge fn (trans_state (State rs m))); eauto.
  destruct (exec_bblock ge fn p1 rs m); try congruence.
  intros H3 (s2' & exp2 & MS'). unfold exec in exp2, H3. rewrite exp2 in H2.
  destruct H2 as (m2' & H2 & H4). discriminate. rewrite H2 in H3.
  destruct (exec_bblock ge fn p2 rs m); simpl in H3.
  * destruct H3 as (s' & H3 & H5 & H6). inv H3. inv MS'.
    cutrewrite (rs0=rs1).
    - cutrewrite (m0=m1); auto. congruence.
    - apply functional_extensionality. intros r.
      generalize (H0 r). intros Hr. congruence.
  * discriminate.
Qed.

(** Used for debug traces *)

Definition gpreg_name (gpr: gpreg) :=
  match gpr with
  | GPR0 => Str ("GPR0") | GPR1 => Str ("GPR1") | GPR2 => Str ("GPR2") | GPR3 => Str ("GPR3") | GPR4 => Str ("GPR4")
  | GPR5 => Str ("GPR5") | GPR6 => Str ("GPR6") | GPR7 => Str ("GPR7") | GPR8 => Str ("GPR8") | GPR9 => Str ("GPR9")
  | GPR10 => Str ("GPR10") | GPR11 => Str ("GPR11") | GPR12 => Str ("GPR12") | GPR13 => Str ("GPR13") | GPR14 => Str ("GPR14")
  | GPR15 => Str ("GPR15") | GPR16 => Str ("GPR16") | GPR17 => Str ("GPR17") | GPR18 => Str ("GPR18") | GPR19 => Str ("GPR19")
  | GPR20 => Str ("GPR20") | GPR21 => Str ("GPR21") | GPR22 => Str ("GPR22") | GPR23 => Str ("GPR23") | GPR24 => Str ("GPR24")
  | GPR25 => Str ("GPR25") | GPR26 => Str ("GPR26") | GPR27 => Str ("GPR27") | GPR28 => Str ("GPR28") | GPR29 => Str ("GPR29")
  | GPR30 => Str ("GPR30") | GPR31 => Str ("GPR31") | GPR32 => Str ("GPR32") | GPR33 => Str ("GPR33") | GPR34 => Str ("GPR34")
  | GPR35 => Str ("GPR35") | GPR36 => Str ("GPR36") | GPR37 => Str ("GPR37") | GPR38 => Str ("GPR38") | GPR39 => Str ("GPR39")
  | GPR40 => Str ("GPR40") | GPR41 => Str ("GPR41") | GPR42 => Str ("GPR42") | GPR43 => Str ("GPR43") | GPR44 => Str ("GPR44")
  | GPR45 => Str ("GPR45") | GPR46 => Str ("GPR46") | GPR47 => Str ("GPR47") | GPR48 => Str ("GPR48") | GPR49 => Str ("GPR49")
  | GPR50 => Str ("GPR50") | GPR51 => Str ("GPR51") | GPR52 => Str ("GPR52") | GPR53 => Str ("GPR53") | GPR54 => Str ("GPR54")
  | GPR55 => Str ("GPR55") | GPR56 => Str ("GPR56") | GPR57 => Str ("GPR57") | GPR58 => Str ("GPR58") | GPR59 => Str ("GPR59")
  | GPR60 => Str ("GPR60") | GPR61 => Str ("GPR61") | GPR62 => Str ("GPR62") | GPR63 => Str ("GPR63")
  end.

Definition string_of_name (x: P.R.t): ?? pstring := 
  if (Pos.eqb x pmem) then 
    RET (Str "MEM")
  else
    match inv_ppos x with
         | Some RA => RET (Str ("RA"))
         | Some PC => RET (Str ("PC"))
         | Some (IR gpr) => RET (gpreg_name gpr)
         | _ => RET (Str ("UNDEFINED"))
    end.

Definition string_of_name_r (n: arith_name_r): pstring :=
  match n with
  | Ploadsymbol _ _ => "Ploadsymbol"
  end.

Definition string_of_name_rr (n: arith_name_rr): pstring :=
  match n with
    Pmv => "Pmv"
  | Pnegw => "Pnegw"
  | Pnegl => "Pnegl"
  | Pcvtl2w => "Pcvtl2w"
  | Psxwd => "Psxwd"
  | Pzxwd => "Pzxwd"
  | Pextfz _ _ => "Pextfz"
  | Pextfs _ _ => "Pextfs"
  | Pextfzl _ _ => "Pextfzl"
  | Pextfsl _ _ => "Pextfsl"
  | Pfabsd => "Pfabsd"
  | Pfabsw => "Pfabsw"
  | Pfnegd => "Pfnegd"
  | Pfnegw => "Pfnegw"
  | Pfinvw => "Pfinvw"
  | Pfnarrowdw => "Pfnarrowdw"
  | Pfwidenlwd => "Pfwidenlwd"
  | Pfloatwrnsz => "Pfloatwrnsz"
  | Pfloatuwrnsz => "Pfloatuwrnsz"
  | Pfloatudrnsz => "Pfloatudrnsz"
  | Pfloatdrnsz => "Pfloatdrnsz"
  | Pfixedwrzz => "Pfixedwrzz"
  | Pfixeduwrzz => "Pfixeduwrzz"
  | Pfixeddrzz => "Pfixeddrzz"
  | Pfixedudrzz => "Pfixedudrzz"
  | Pfixeddrzz_i32 => "Pfixeddrzz_i32"
  | Pfixedudrzz_i32 => "Pfixedudrzz_i32"
  end.

Definition string_of_name_ri32 (n: arith_name_ri32): pstring :=
  match n with
  | Pmake => "Pmake"
  end.

Definition string_of_name_ri64 (n: arith_name_ri64): pstring :=
  match n with
  | Pmakel => "Pmakel"
  end.

Definition string_of_name_rf32 (n: arith_name_rf32): pstring :=
  match n with
  | Pmakefs => "Pmakefs"
  end.

Definition string_of_name_rf64 (n: arith_name_rf64): pstring :=
  match n with
  | Pmakef => "Pmakef"
  end.

Definition string_of_name_rrr (n: arith_name_rrr): pstring :=
  match n with
  | Pcompw _ => "Pcompw"
  | Pcompl _ => "Pcompl"
  | Pfcompw _ => "Pfcompw"
  | Pfcompl _ => "Pfcompl"
  | Paddw => "Paddw"
  | Paddxw _ => "Paddxw"
  | Psubw => "Psubw"
  | Prevsubxw _ => "Prevsubxw"
  | Pmulw => "Pmulw"
  | Pandw => "Pandw"
  | Pnandw => "Pnandw"
  | Porw => "Porw"
  | Pnorw => "Pnorw"
  | Pxorw => "Pxorw"
  | Pnxorw => "Pnxorw"
  | Pandnw => "Pandnw"
  | Pornw => "Pornw"
  | Psraw => "Psraw"
  | Psrlw => "Psrlw"
  | Psrxw => "Psrxw"
  | Psllw => "Psllw"
  | Paddl => "Paddl"
  | Paddxl _ => "Paddxl"
  | Psubl => "Psubl"
  | Prevsubxl _ => "Prevsubxl"
  | Pandl => "Pandl"
  | Pnandl => "Pnandl"
  | Porl => "Porl"
  | Pnorl => "Pnorl"
  | Pxorl => "Pxorl"
  | Pnxorl => "Pnxorl"
  | Pandnl => "Pandnl"
  | Pornl => "Pornl"
  | Pmull => "Pmull"
  | Pslll => "Pslll"
  | Psrll => "Psrll"
  | Psrxl => "Psrxl"
  | Psral => "Psral"
  | Pfaddd => "Pfaddd"
  | Pfaddw => "Pfaddw"
  | Pfsbfd => "Pfsbfd"
  | Pfsbfw => "Pfsbfw"
  | Pfmuld => "Pfmuld"
  | Pfmulw => "Pfmulw"
  | Pfmind => "Pfmind"
  | Pfminw => "Pfminw"
  | Pfmaxd => "Pfmaxd"
  | Pfmaxw => "Pfmaxw"
  end.

Definition string_of_name_rri32 (n: arith_name_rri32): pstring :=
  match n with
    Pcompiw _ => "Pcompiw"
  | Paddiw => "Paddiw"
  | Paddxiw _ => "Paddxiw"
  | Prevsubiw => "Prevsubiw"
  | Prevsubxiw _ => "Prevsubxiw"
  | Pmuliw => "Pmuliw"
  | Pandiw => "Pandiw"
  | Pnandiw => "Pnandiw"
  | Poriw => "Poriw"
  | Pnoriw => "Pnoriw"
  | Pxoriw => "Pxoriw"
  | Pnxoriw => "Pnxoriw"
  | Pandniw => "Pandniw"
  | Porniw => "Porniw"
  | Psraiw => "Psraiw"
  | Psrliw => "Psrliw"
  | Psrxiw => "Psrxiw"
  | Pslliw => "Pslliw"
  | Proriw => "Proriw"
  | Psllil => "Psllil"
  | Psrlil => "Psrlil"
  | Psrail => "Psrail"
  | Psrxil => "Psrxil"
  end.

Definition string_of_name_rri64 (n: arith_name_rri64): pstring :=
  match n with
    Pcompil _ => "Pcompil"
  | Paddil => "Paddil"
  | Prevsubil => "Prevsubil"
  | Paddxil _ => "Paddxil"
  | Prevsubxil _ => "Prevsubxil"
  | Pmulil => "Pmulil"
  | Pandil => "Pandil"
  | Pnandil => "Pnandil"
  | Poril => "Poril"
  | Pnoril => "Pnoril"
  | Pxoril => "Pxoril"
  | Pnxoril => "Pnxoril"
  | Pandnil => "Pandnil"
  | Pornil => "Pornil"
  end.

Definition string_of_name_arrr (n: arith_name_arrr): pstring :=
  match n with
  | Pmaddw  => "Pmaddw"
  | Pmaddl  => "Pmaddl"
  | Pmsubw  => "Pmsubw"
  | Pmsubl  => "Pmsubl"
  | Pcmove _ => "Pcmove"
  | Pcmoveu _ => "Pcmoveu"
  | Pfmaddfw  => "Pfmaddfw"
  | Pfmaddfl  => "Pfmaddfl"
  | Pfmsubfw  => "Pfmsubfw"
  | Pfmsubfl  => "Pfmsubfl"
  end.

Definition string_of_name_arr (n: arith_name_arr): pstring :=
  match n with
  | Pinsf _ _ => "Pinsf"
  | Pinsfl _ _ => "Pinsfl"
  end.

Definition string_of_name_arri32 (n: arith_name_arri32): pstring :=
  match n with
  | Pmaddiw => "Pmaddw"
  | Pcmoveiw _ => "Pcmoveiw"
  | Pcmoveuiw _ => "Pcmoveuiw"
  end.

Definition string_of_name_arri64 (n: arith_name_arri64): pstring :=
  match n with
  | Pmaddil => "Pmaddl"
  | Pcmoveil _ => "Pcmoveil"
  | Pcmoveuil _ => "Pcmoveuil"
  end.

Definition string_of_arith (op: arith_op): pstring :=
  match op with
  | OArithR n => string_of_name_r n
  | OArithRR n => string_of_name_rr n
  | OArithRI32 n _ => string_of_name_ri32 n
  | OArithRI64 n _ => string_of_name_ri64 n
  | OArithRF32 n _ => string_of_name_rf32 n
  | OArithRF64 n _ => string_of_name_rf64 n
  | OArithRRR n => string_of_name_rrr n
  | OArithRRI32 n _ => string_of_name_rri32 n
  | OArithRRI64 n _ => string_of_name_rri64 n
  | OArithARRR n => string_of_name_arrr n
  | OArithARR n => string_of_name_arr n
  | OArithARRI32 n _ => string_of_name_arri32 n
  | OArithARRI64 n _ => string_of_name_arri64 n
  end.

Definition string_of_load_name (n: load_name) : pstring :=
  match n with
    Plb => "Plb"
  | Plbu => "Plbu"
  | Plh => "Plh"
  | Plhu => "Plhu"
  | Plw => "Plw"
  | Plw_a => "Plw_a"
  | Pld => "Pld"
  | Pld_a => "Pld_a"
  | Pfls => "Pfls"
  | Pfld => "Pfld"
  end.

Definition string_of_load (op: load_op): pstring :=
  match op with
  | OLoadRRO n _ _ => string_of_load_name n
  | OLoadRRR n _ => string_of_load_name n
  | OLoadRRRXS n _ => string_of_load_name n
  end.

Definition string_of_store_name (n: store_name) : pstring :=
  match n with
    Psb => "Psb"
  | Psh => "Psh"
  | Psw => "Psw"
  | Psw_a => "Psw_a"
  | Psd => "Psd"
  | Psd_a => "Psd_a"
  | Pfss => "Pfss"
  | Pfsd => "Pfsd"
  end.

Definition string_of_store (op: store_op) : pstring :=
  match op with
  | OStoreRRO n _ => string_of_store_name n
  | OStoreRRR n => string_of_store_name n
  | OStoreRRRXS n => string_of_store_name n
  end.

Definition string_of_control (op: control_op) : pstring :=
  match op with
  | Oj_l _ => "Oj_l"
  | Ocb _ _ => "Ocb"
  | Ocbu _ _ => "Ocbu"
  | Odiv => "Odiv"
  | Odivu => "Odivu"
  | Ojumptable _ => "Ojumptable"
  | OError => "OError"
  | OIncremPC _ => "OIncremPC"
  end.

Definition string_of_op (op: P.op): ?? pstring := 
  match op with
  | Arith op => RET (string_of_arith op)
  | Load op => RET (string_of_load op)
  | Store op => RET (string_of_store op)
  | Control op => RET (string_of_control op)
  | Allocframe _ _ => RET (Str "Allocframe")
  | Allocframe2 _ _ => RET (Str "Allocframe2")
  | Freeframe _ _ => RET (Str "Freeframe")
  | Freeframe2 _ _ => RET (Str "Freeframe2")
  | Constant _ => RET (Str "Constant")
  | Fail => RET (Str "Fail")
  end.

End SECT_BBLOCK_EQUIV.

(** REWRITE RULES *)

Definition is_constant (o: op): bool :=
  match o with
  | Constant _ | OArithR _ | OArithRI32 _ _ | OArithRI64 _ _ | OArithRF32 _ _ | OArithRF64 _ _ => true
  | _ => false
  end.

Lemma is_constant_correct ge o: is_constant o = true -> op_eval ge o [] <> None.
Proof.
  destruct o; simpl in * |- *; try congruence.
  destruct ao; simpl in * |- *; try congruence;
  destruct n; simpl in * |- *; try congruence;
  unfold arith_eval; destruct ge; simpl in * |- *; try congruence.
Qed.

Definition main_reduce (t: Terms.term):= RET (Terms.nofail is_constant t).

Local Hint Resolve is_constant_correct: wlp.

Lemma main_reduce_correct t:
 WHEN main_reduce t ~> pt THEN Terms.match_pt t pt.
Proof.
  wlp_simplify.
Qed.

Definition reduce := {| Terms.result := main_reduce; Terms.result_correct := main_reduce_correct |}.

Definition bblock_simu_test (verb: bool) (p1 p2: Asmvliw.bblock) : ?? bool :=
  if verb then
    IST.verb_bblock_simu_test reduce string_of_name string_of_op (trans_block p1) (trans_block p2)
  else
    IST.bblock_simu_test reduce (trans_block p1) (trans_block p2).

Local Hint Resolve IST.bblock_simu_test_correct bblock_simu_reduce IST.verb_bblock_simu_test_correct: wlp.

Theorem bblock_simu_test_correct verb p1 p2 :
  WHEN bblock_simu_test verb p1 p2 ~> b THEN b=true -> forall ge fn, Asmblockprops.bblock_simu ge fn p1 p2.
Proof.
  wlp_simplify.
Qed.
Hint Resolve bblock_simu_test_correct: wlp.

(* Coerce bblock_simu_test into a pure function (this is a little unsafe like all oracles in CompCert). *)

Import UnsafeImpure.

Definition pure_bblock_simu_test (verb: bool) (p1 p2: Asmvliw.bblock): bool := 
  match unsafe_coerce (bblock_simu_test verb p1 p2) with
  | Some b => b
  | None => false
  end.

Theorem pure_bblock_simu_test_correct verb p1 p2 ge fn: pure_bblock_simu_test verb p1 p2 = true -> Asmblockprops.bblock_simu ge fn p1 p2.
Proof.
   unfold pure_bblock_simu_test. 
   destruct (unsafe_coerce (bblock_simu_test verb p1 p2)) eqn: UNSAFE; try discriminate.
   intros; subst. eapply bblock_simu_test_correct; eauto.
   apply unsafe_coerce_not_really_correct; eauto.
Qed.

Definition bblock_simub: Asmvliw.bblock -> Asmvliw.bblock -> bool := pure_bblock_simu_test true.

Lemma bblock_simub_correct p1 p2 ge fn: bblock_simub p1 p2 = true -> Asmblockprops.bblock_simu ge fn p1 p2.
Proof.
 eapply (pure_bblock_simu_test_correct true).
Qed.
