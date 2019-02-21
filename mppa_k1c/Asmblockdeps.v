Require Import AST.
Require Import Asmblock.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import ZArith.
Require Import ImpDep.

Open Scope impure.

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
  | OError
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
  | OLoadRRO (n: load_name_rro) (ofs: offset)
.

Coercion OLoadRRO: load_name_rro >-> Funclass.

Inductive store_op :=
  | OStoreRRO (n: store_name_rro) (ofs: offset)
.

Coercion OStoreRRO: store_name_rro >-> Funclass.

Inductive op_wrap :=
  | Arith (ao: arith_op)
  | Load (lo: load_op)
  | Store (so: store_op)
  | Control (co: control_op)
  | Allocframe (sz: Z) (pos: ptrofs)
  | Freeframe (sz: Z) (pos: ptrofs)
  | Freeframe2 (sz: Z) (pos: ptrofs)
  | Constant (v: val)
.

Coercion Arith: arith_op >-> op_wrap.
Coercion Load: load_op >-> op_wrap.
Coercion Store: store_op >-> op_wrap.
Coercion Control: control_op >-> op_wrap.

Definition op := op_wrap.

Definition arith_eval (ao: arith_op) (l: list value) :=
  let (ge, fn) := Ge in
  match ao, l with
  | OArithR n, [] =>
      match n with
      | Ploadsymbol s ofs => Some (Val (Genv.symbol_address ge s ofs))
      end

  | OArithRR n, [Val v] =>
      match n with
      | Pmv => Some (Val v)
      | Pnegw => Some (Val (Val.neg v))
      | Pnegl => Some (Val (Val.negl v))
      | Pcvtl2w => Some (Val (Val.loword v))
      | Psxwd => Some (Val (Val.longofint v))
      | Pzxwd => Some (Val (Val.longofintu v))
      | Pfnegd => Some (Val (Val.negf v))
      | Pfnegw => Some (Val (Val.negfs v))
      | Pfabsd => Some (Val (Val.absf v))
      | Pfabsw => Some (Val (Val.absfs v))
      | Pfnarrowdw => Some (Val (Val.singleoffloat v))
      | Pfwidenlwd => Some (Val (Val.floatofsingle v))
      | Pfloatwrnsz => Some (Val (match Val.singleofint v with Some f => f | _ => Vundef end))
      | Pfloatudrnsz => Some (Val (match Val.floatoflongu v with Some f => f | _ => Vundef end))
      | Pfloatdrnsz => Some (Val (match Val.floatoflong v with Some f => f | _ => Vundef end))
      | Pfixedwrzz => Some (Val (match Val.intofsingle v with Some i => i | _ => Vundef end))
      | Pfixeddrzz => Some (Val (match Val.longoffloat v with Some i => i | _ => Vundef end))
      end

  | OArithRI32 n i, [] =>
      match n with
      | Pmake => Some (Val (Vint i))
      end

  | OArithRI64 n i, [] =>
      match n with
      | Pmakel => Some (Val (Vlong i))
      end

  | OArithRF32 n i, [] =>
      match n with
      | Pmakefs => Some (Val (Vsingle i))
      end

  | OArithRF64 n i, [] =>
      match n with
      | Pmakef => Some (Val (Vfloat i))
      end

  | OArithRRR n, [Val v1; Val v2; Memstate m] =>
      match n with
      | Pcompw c => Some (Val (compare_int c v1 v2 m))
      | Pcompl c => Some (Val (compare_long c v1 v2 m))
      | _ => None
      end

  | OArithRRR n, [Val v1; Val v2] =>
      match n with
      | Paddw  => Some (Val (Val.add  v1 v2))
      | Psubw  => Some (Val (Val.sub  v1 v2))
      | Pmulw  => Some (Val (Val.mul  v1 v2))
      | Pandw  => Some (Val (Val.and  v1 v2))
      | Porw   => Some (Val (Val.or   v1 v2))
      | Pxorw  => Some (Val (Val.xor  v1 v2))
      | Psrlw  => Some (Val (Val.shru v1 v2))
      | Psraw  => Some (Val (Val.shr  v1 v2))
      | Psllw  => Some (Val (Val.shl  v1 v2))

      | Paddl => Some (Val (Val.addl v1 v2))
      | Psubl => Some (Val (Val.subl v1 v2))
      | Pandl => Some (Val (Val.andl v1 v2))
      | Porl  => Some (Val (Val.orl  v1 v2))
      | Pxorl  => Some (Val (Val.xorl  v1 v2))
      | Pmull => Some (Val (Val.mull v1 v2))
      | Pslll => Some (Val (Val.shll v1 v2))
      | Psrll => Some (Val (Val.shrlu v1 v2))
      | Psral => Some (Val (Val.shrl v1 v2))

      | Pfaddd => Some (Val (Val.addf v1 v2))
      | Pfaddw => Some (Val (Val.addfs v1 v2))
      | Pfsbfd => Some (Val (Val.subf v1 v2))
      | Pfsbfw => Some (Val (Val.subfs v1 v2))
      | Pfmuld => Some (Val (Val.mulf v1 v2))
      | Pfmulw => Some (Val (Val.mulfs v1 v2))

      | _ => None
      end

  | OArithRRI32 n i, [Val v; Memstate m] =>
      match n with
      | Pcompiw c => Some (Val (compare_int c v (Vint i) m))
      | _ => None
      end

  | OArithRRI32 n i, [Val v] =>
      match n with
      | Paddiw  => Some (Val (Val.add   v (Vint i)))
      | Pandiw  => Some (Val (Val.and   v (Vint i)))
      | Poriw   => Some (Val (Val.or    v (Vint i)))
      | Pxoriw  => Some (Val (Val.xor   v (Vint i)))
      | Psraiw  => Some (Val (Val.shr   v (Vint i)))
      | Psrliw  => Some (Val (Val.shru  v (Vint i)))
      | Pslliw  => Some (Val (Val.shl   v (Vint i)))
      | Psllil  => Some (Val (Val.shll  v (Vint i)))
      | Psrlil  => Some (Val (Val.shrlu v (Vint i)))
      | Psrail  => Some (Val (Val.shrl  v (Vint i)))
      | _ => None
      end

  | OArithRRI64 n i, [Val v; Memstate m] =>
      match n with
      | Pcompil c => Some (Val (compare_long c v (Vlong i) m))
      | _ => None
      end

  | OArithRRI64 n i, [Val v] =>
      match n with
      | Paddil  => Some (Val (Val.addl v (Vlong i)))
      | Pandil  => Some (Val (Val.andl v (Vlong i)))
      | Poril   => Some (Val (Val.orl  v (Vlong i)))
      | Pxoril  => Some (Val (Val.xorl  v (Vlong i)))
      | _ => None
      end

  | _, _ => None
  end.

Definition exec_load_deps (chunk: memory_chunk) (m: mem)
                     (v: val) (ofs: offset) :=
  let (ge, fn) := Ge in
  match (eval_offset ge ofs) with
  | OK ptr =>
    match Mem.loadv chunk m (Val.offset_ptr v ptr) with
    | None => None
    | Some vl => Some (Val vl)
    end
  | _ => None
  end.

Definition load_eval (lo: load_op) (l: list value) :=
  match lo, l with
  | OLoadRRO n ofs, [Val v; Memstate m] =>
      match n with
        | Plb => exec_load_deps Mint8signed m v ofs
        | Plbu => exec_load_deps Mint8unsigned m v ofs
        | Plh => exec_load_deps Mint16signed m v ofs
        | Plhu => exec_load_deps Mint16unsigned m v ofs
        | Plw => exec_load_deps Mint32 m v ofs
        | Plw_a => exec_load_deps Many32 m v ofs
        | Pld => exec_load_deps Mint64 m v ofs
        | Pld_a => exec_load_deps Many64 m v ofs
        | Pfls => exec_load_deps Mfloat32 m v ofs
        | Pfld => exec_load_deps Mfloat64 m v ofs
      end
  | _, _ => None
  end.

Definition exec_store_deps (chunk: memory_chunk) (m: mem)
                      (vs va: val) (ofs: offset) :=
  let (ge, fn) := Ge in
  match (eval_offset ge ofs) with
  | OK ptr => 
    match Mem.storev chunk m (Val.offset_ptr va ptr) vs with
    | None => None
    | Some m' => Some (Memstate m')
    end
  | _ => None
  end.

Definition store_eval (so: store_op) (l: list value) :=
  match so, l with
  | OStoreRRO n ofs, [Val vs; Val va; Memstate m] =>
      match n with
        | Psb => exec_store_deps Mint8unsigned m vs va ofs
        | Psh => exec_store_deps Mint16unsigned m vs va ofs
        | Psw => exec_store_deps Mint32 m vs va ofs
        | Psw_a => exec_store_deps Many32 m vs va ofs
        | Psd => exec_store_deps Mint64 m vs va ofs
        | Psd_a => exec_store_deps Many64 m vs va ofs
        | Pfss => exec_store_deps Mfloat32 m vs va ofs
        | Pfsd => exec_store_deps Mfloat64 m vs va ofs
      end
  | _, _ => None
  end.

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
  | Oj_l l, [Val vpc] => goto_label_deps fn l vpc
  | Ocb bt l, [Val v; Val vpc] =>
    match cmp_for_btest bt with
    | (Some c, Int)  => eval_branch_deps fn l vpc (Val.cmp_bool c v (Vint (Int.repr 0)))
    | (Some c, Long) => eval_branch_deps fn l vpc (Val.cmpl_bool c v (Vlong (Int64.repr 0)))
    | (None, _) => None
    end
  | Ocbu bt l, [Val v; Val vpc; Memstate m] =>
    match cmpu_for_btest bt with
    | (Some c, Int) => eval_branch_deps fn l vpc (Val.cmpu_bool (Mem.valid_pointer m) c v (Vint (Int.repr 0)))
    | (Some c, Long) => eval_branch_deps fn l vpc (Val.cmplu_bool (Mem.valid_pointer m) c v (Vlong (Int64.repr 0)))
    | (None, _) => None
    end
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
  | _, _ => None
  end.

Definition iandb (ib1 ib2: ?? bool): ?? bool :=
  DO b1 <~ ib1;;
  DO b2 <~ ib2;;
  RET (andb b1 b2).

Definition arith_op_eq (o1 o2: arith_op): ?? bool :=
  match o1, o2 with
  | OArithR n1, OArithR n2 => phys_eq n1 n2
  | OArithRR n1, OArithRR n2 => phys_eq n1 n2
  | OArithRI32 n1 i1, OArithRI32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2)
  | OArithRI64 n1 i1, OArithRI64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2)
  | OArithRF32 n1 i1, OArithRF32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2)
  | OArithRF64 n1 i1, OArithRF64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2)
  | OArithRRR n1, OArithRRR n2 => phys_eq n1 n2
  | OArithRRI32 n1 i1, OArithRRI32 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2)
  | OArithRRI64 n1 i1, OArithRRI64 n2 i2 => iandb (phys_eq n1 n2) (phys_eq i1 i2)
  | _, _ => RET false
  end.

Lemma arith_op_eq_correct o1 o2:
  WHEN arith_op_eq o1 o2 ~> b THEN b = true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify; try discriminate.
  all: try congruence.
  all: apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
Qed.


Definition load_op_eq (o1 o2: load_op): ?? bool :=
  match o1, o2 with
  | OLoadRRO n1 ofs1, OLoadRRO n2 ofs2 => iandb (phys_eq n1 n2) (phys_eq ofs1 ofs2)
  end.

Lemma load_op_eq_correct o1 o2:
  WHEN load_op_eq o1 o2 ~> b THEN b = true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify.
  apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
Qed.


Definition store_op_eq (o1 o2: store_op): ?? bool :=
  match o1, o2 with
  | OStoreRRO n1 ofs1, OStoreRRO n2 ofs2 => iandb (phys_eq n1 n2) (phys_eq ofs1 ofs2)
  end.

Lemma store_op_eq_correct o1 o2:
  WHEN store_op_eq o1 o2 ~> b THEN b = true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify.
  apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
Qed.


Definition control_op_eq (c1 c2: control_op): ?? bool :=
  match c1, c2 with
  | Oj_l l1, Oj_l l2 => phys_eq l1 l2
  | Ocb bt1 l1, Ocb bt2 l2 => iandb (phys_eq bt1 bt2) (phys_eq l1 l2)
  | Ocbu bt1 l1, Ocbu bt2 l2 => iandb (phys_eq bt1 bt2) (phys_eq l1 l2)
  | _, _ => RET false
  end.

Lemma control_op_eq_correct c1 c2:
  WHEN control_op_eq c1 c2 ~> b THEN b = true -> c1 = c2.
Proof.
  destruct c1, c2; wlp_simplify; try discriminate.
  - congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
Qed.


Definition op_eq (o1 o2: op): ?? bool :=
  match o1, o2 with
  | Arith i1, Arith i2 => arith_op_eq i1 i2
  | Load i1, Load i2 => load_op_eq i1 i2
  | Store i1, Store i2 => store_op_eq i1 i2
  | Control i1, Control i2 => control_op_eq i1 i2
  | Allocframe sz1 pos1, Allocframe sz2 pos2 => iandb (phys_eq sz1 sz2) (phys_eq pos1 pos2)
  | Freeframe sz1 pos1, Freeframe sz2 pos2 => iandb (phys_eq sz1 sz2) (phys_eq pos1 pos2)
  | Freeframe2 sz1 pos1, Freeframe2 sz2 pos2 => iandb (phys_eq sz1 sz2) (phys_eq pos1 pos2)
  | Constant c1, Constant c2 => phys_eq c1 c2
  | _, _ => RET false
  end.

Theorem op_eq_correct o1 o2: 
 WHEN op_eq o1 o2 ~> b THEN b=true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify; try discriminate.
  - simpl in Hexta. exploit arith_op_eq_correct. eassumption. eauto. congruence.
  - simpl in Hexta. exploit load_op_eq_correct. eassumption. eauto. congruence.
  - simpl in Hexta. exploit store_op_eq_correct. eassumption. eauto. congruence.
  - simpl in Hexta. exploit control_op_eq_correct. eassumption. eauto. congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
  - congruence.
Qed.

End IMPPARAM.
End P.

Module L <: ISeqLanguage with Module LP:=P.

Module LP:=P.

Include MkSeqLanguage P.

End L.

Module IDT := ImpDepTree L ImpPosDict.

Import L.
Import P.

(** Compilation from Asmblock to L *)

Section SECT.
Variable Ge: genv.

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

Local Open Scope positive_scope.

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

Definition ppos (r: preg) : R.t :=
  match r with
  | RA => 2
  | PC => 3
  | IR ir => 3 + ireg_to_pos ir
  end
.

Definition inv_ppos (p: R.t) : option preg :=
  match p with
  | 1 => None
  | 2 => Some RA | 3 => Some PC
  | n => match pos_to_ireg (n-3) with
       | None => None
       | Some gpr => Some (IR gpr)
       end
  end.

Notation "# r" := (ppos r) (at level 100, right associativity).

Notation "a @ b" := (Econs a b) (at level 102, right associativity).

Definition trans_control (ctl: control) : macro :=
  match ctl with
  | Pret => [(#PC, Name (#RA))]
  | Pcall s => [(#RA, Name (#PC)); (#PC, Op (Arith (OArithR (Ploadsymbol s Ptrofs.zero))) Enil)]
  | Picall r => [(#RA, Name (#PC)); (#PC, Name (#r))]
  | Pgoto s => [(#PC, Op (Arith (OArithR (Ploadsymbol s Ptrofs.zero))) Enil)]
  | Pigoto r => [(#PC, Name (#r))]
  | Pj_l l => [(#PC, Op (Control (Oj_l l)) (Name (#PC) @ Enil))]
  | Pcb bt r l => [(#PC, Op (Control (Ocb bt l)) (Name (#r) @ Name (#PC) @ Enil))]
  | Pcbu bt r l => [(#PC, Op (Control (Ocbu bt l)) (Name (#r) @ Name (#PC) @ Name pmem @ Enil))]
  | Pbuiltin ef args res => [(#PC, Op (Control (OError)) Enil)]
  end.

Definition trans_exit (ex: option control) : list L.macro :=
  match ex with
  | None => nil
  | Some ctl => trans_control ctl :: nil
  end
.

Definition trans_arith (ai: ar_instruction) : macro :=
  match ai with
  | PArithR n d => [(#d, Op (Arith (OArithR n)) Enil)]
  | PArithRR n d s => [(#d, Op (Arith (OArithRR n)) (Name (#s) @ Enil))]
  | PArithRI32 n d i => [(#d, Op (Arith (OArithRI32 n i)) Enil)]
  | PArithRI64 n d i => [(#d, Op (Arith (OArithRI64 n i)) Enil)]
  | PArithRF32 n d i => [(#d, Op (Arith (OArithRF32 n i)) Enil)]
  | PArithRF64 n d i => [(#d, Op (Arith (OArithRF64 n i)) Enil)]
  | PArithRRR n d s1 s2 => [(#d, Op (Arith (OArithRRR n)) (Name (#s1) @ Name (#s2) @ Enil))]
  | PArithRRI32 n d s i => [(#d, Op (Arith (OArithRRI32 n i)) (Name (#s) @ Enil))]
  | PArithRRI64 n d s i => [(#d, Op (Arith (OArithRRI64 n i)) (Name (#s) @ Enil))]
  end.


Definition trans_basic (b: basic) : macro :=
  match b with
  | PArith ai => trans_arith ai
  | PLoadRRO n d a ofs => [(#d, Op (Load (OLoadRRO n ofs)) (Name (#a) @ Name pmem @ Enil))]
  | PStoreRRO n s a ofs => [(pmem, Op (Store (OStoreRRO n ofs)) (Name (#s) @ Name (#a) @ Name pmem @ Enil))]
  | Pallocframe sz pos => [(pmem, Op (Allocframe sz pos) (Name (#SP) @ Name pmem @ Enil));
                           (#FP, Name (#SP)); (#SP, Name (#RTMP)); (#RTMP, Op (Constant Vundef) Enil)]
  | Pfreeframe sz pos => [(pmem, Op (Freeframe sz pos) (Name (#SP) @ Name pmem @ Enil));
                          (#SP, Op (Freeframe2 sz pos) (Name (#SP) @ Name pmem @ Enil));
                          (#RTMP, Op (Constant Vundef) Enil)]
  | Pget rd ra => [(#rd, Name (#ra))]
  | Pset ra rd => [(#ra, Name (#rd))]
  | Pnop => []
  end.

Fixpoint trans_body (b: list basic) : list L.macro :=
  match b with
  | nil => nil
  | b :: lb => (trans_basic b) :: (trans_body lb)
  end.

Definition trans_block (b: Asmblock.bblock) : L.bblock :=
  trans_body (body b) ++ trans_exit (exit b).

Definition state := L.mem.
Definition exec := L.run.

Definition match_states (s: Asmblock.state) (s': state) :=
  let (rs, m) := s in
     s' pmem = Memstate m
  /\ forall r, s' (#r) = Val (rs r).

Notation "a <[ b <- c ]>" := (assign a b c) (at level 102, right associativity).

Definition empty_state : state := (fun _ => Val Vundef).

Definition trans_state (s: Asmblock.state) : state :=
  let (rs, m) := s in
  fun x => if (Pos.eq_dec x pmem) then Memstate m
           else match (inv_ppos x) with
           | Some r => Val (rs r)
           | None => Val Vundef
           end.

Theorem trans_state_match: forall S, match_states S (trans_state S).
Proof.
  intros. destruct S as (rs & m). simpl.
  split. reflexivity.
  intro. destruct r; try reflexivity.
  destruct g; reflexivity.
Qed.

Lemma exec_match_app:
  forall c c' s s' s'',
  exec Ge c s = Some s' ->
  exec Ge c' s' = Some s'' ->
  exec Ge (c ++ c') s = Some s''.
Proof.
Admitted.

Lemma forward_simu_body:
  forall ge bdy rs m rs' m' fn s,
  Ge = Genv ge fn ->
  exec_body ge bdy rs m = Next rs' m' ->
  match_states (State rs m) s ->
  exists s',
     exec Ge (trans_body bdy) s = Some s'
  /\ match_states (State rs' m') s'.
Proof.
Admitted.

Theorem forward_simu:
  forall rs1 m1 rs2 m2 s1' b ge fn,
    Ge = Genv ge fn ->
    exec_bblock ge fn b rs1 m1 = Next rs2 m2 ->
    match_states (State rs1 m1) s1' ->
    exists s2',
       exec Ge (trans_block b) s1' = Some s2'
    /\ match_states (State rs2 m2) s2'.
Proof.
  intros until fn. intros GENV EXECB MS. unfold exec_bblock in EXECB. destruct (exec_body _ _ _) eqn:EXEB; try discriminate.
  exploit forward_simu_body; eauto. intros (s' & EXETRANSB & MS').

  eexists. split.
  unfold trans_block. eapply exec_match_app. eassumption.
Admitted.

End SECT.
