Require Import AST.
Require Import Asmblock.
Require Import Asmblockgenproof0.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import ZArith.
Require Import Coqlib.
Require Import ImpDep.
Require Import Axioms.

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
  | OIncremPC (sz: Z)
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
      | Pfloatuwrnsz => Some (Val (match Val.singleofintu v with Some f => f | _ => Vundef end))
      | Pfloatudrnsz => Some (Val (match Val.floatoflongu v with Some f => f | _ => Vundef end))
      | Pfloatdrnsz => Some (Val (match Val.floatoflong v with Some f => f | _ => Vundef end))
      | Pfloatudrnsz_i32 => Some (Val (match Val.floatofintu v with Some f => f | _ => Vundef end))
      | Pfloatdrnsz_i32 => Some (Val (match Val.floatofint v with Some f => f | _ => Vundef end))
      | Pfixedwrzz => Some (Val (match Val.intofsingle v with Some i => i | _ => Vundef end))
      | Pfixeduwrzz => Some (Val (match Val.intuofsingle v with Some i => i | _ => Vundef end))
      | Pfixeddrzz => Some (Val (match Val.longoffloat v with Some i => i | _ => Vundef end))
      | Pfixedudrzz => Some (Val (match Val.longuoffloat v with Some i => i | _ => Vundef end))
      | Pfixeddrzz_i32 => Some (Val (match Val.intoffloat v with Some i => i | _ => Vundef end))
      | Pfixedudrzz_i32 => Some (Val (match Val.intuoffloat v with Some i => i | _ => Vundef end))
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
      | Pfcompw c => Some (Val (compare_single c v1 v2))
      | Pfcompl c => Some (Val (compare_float c v1 v2))

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


Definition is_constant (o: op): bool := 
 (* FIXME

   => répondre "true" autant que possible mais en satisfaisant [is_constant_correct] ci-dessous.

   ATTENTION, is_constant ne doit pas dépendre de [ge].
   Sinon, on aurait une implémentation facile: [match op_eval o nil with Some _ => true | _ => false end]

   => REM: il n'est pas sûr que ce soit utile de faire qqchose de très exhaustif en pratique...
   (ça sert juste à une petite optimisation du vérificateur de scheduling).
  *)
  match o with
  | Constant _ => true
  | _ => false
  end.

Lemma is_constant_correct o: is_constant o = true -> op_eval o nil <> None.
Proof.
  destruct o; simpl; try congruence.
Qed.


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
  | OIncremPC sz1, OIncremPC sz2 => phys_eq sz1 sz2
  | OError, OError => RET true
  | _, _ => RET false
  end.

Lemma control_op_eq_correct c1 c2:
  WHEN control_op_eq c1 c2 ~> b THEN b = true -> c1 = c2.
Proof.
  destruct c1, c2; wlp_simplify; try discriminate.
  - congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
  - apply andb_prop in H1; inversion H1; apply H in H2; apply H0 in H3; congruence.
  - congruence.
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
  | Fail, Fail => RET true
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
  | PArithRRR n d s1 s2 => 
      match n with
      | Pcompw _ | Pcompl _ => [(#d, Op (Arith (OArithRRR n)) (Name (#s1) @ Name (#s2) @ Name pmem @ Enil))]
      | _ => [(#d, Op (Arith (OArithRRR n)) (Name (#s1) @ Name (#s2) @ Enil))]
      end
  | PArithRRI32 n d s i =>
      match n with
      | Pcompiw _ => [(#d, Op (Arith (OArithRRI32 n i)) (Name (#s) @ Name pmem @ Enil))]
      | _ => [(#d, Op (Arith (OArithRRI32 n i)) (Name (#s) @ Enil))]
      end
  | PArithRRI64 n d s i => 
      match n with
      | Pcompil _ => [(#d, Op (Arith (OArithRRI64 n i)) (Name (#s) @ Name pmem @ Enil))]
      | _ => [(#d, Op (Arith (OArithRRI64 n i)) (Name (#s) @ Enil))]
      end
  end.


Definition trans_basic (b: basic) : macro :=
  match b with
  | PArith ai => trans_arith ai
  | PLoadRRO n d a ofs => [(#d, Op (Load (OLoadRRO n ofs)) (Name (#a) @ Name pmem @ Enil))]
  | PStoreRRO n s a ofs => [(pmem, Op (Store (OStoreRRO n ofs)) (Name (#s) @ Name (#a) @ Name pmem @ Enil))]
  | Pallocframe sz pos => [(#FP, Name (#SP)); (#SP, Op (Allocframe2 sz pos) (Name (#SP) @ Name pmem @ Enil)); (#RTMP, Op (Constant Vundef) Enil);
                           (pmem, Op (Allocframe sz pos) (Old (Name (#SP)) @ Name pmem @ Enil))]
  | Pfreeframe sz pos => [(pmem, Op (Freeframe sz pos) (Name (#SP) @ Name pmem @ Enil));
                          (#SP, Op (Freeframe2 sz pos) (Name (#SP) @ Old (Name pmem) @ Enil));
                          (#RTMP, Op (Constant Vundef) Enil)]
  | Pget rd ra => match ra with
                  | RA => [(#rd, Name (#ra))]
                  | _ => [(#rd, Op Fail Enil)]
                  end
  | Pset ra rd => match ra with
                  | RA => [(#ra, Name (#rd))]
                  | _ => [(#rd, Op Fail Enil)]
                  end
  | Pnop => []
  end.

Fixpoint trans_body (b: list basic) : list L.macro :=
  match b with
  | nil => nil
  | b :: lb => (trans_basic b) :: (trans_body lb)
  end.

Definition trans_pcincr (sz: Z) := [(#PC, Op (Control (OIncremPC sz)) (Name (#PC) @ Enil))] :: nil.

Definition trans_block (b: Asmblock.bblock) : L.bblock :=
  trans_body (body b) ++ trans_pcincr (size b) ++ trans_exit (exit b).

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

Definition match_states (s: Asmblock.state) (s': state) :=
  let (rs, m) := s in
     s' pmem = Memstate m
  /\ forall r, s' (#r) = Val (rs r).

Definition match_outcome (o:outcome) (s: option state) :=
  match o with
  | Next rs m => exists s', s=Some s' /\ match_states (State rs m) s'
  | Stuck => s=None
  end.
 
Notation "a <[ b <- c ]>" := (assign a b c) (at level 102, right associativity).

Definition trans_state (s: Asmblock.state) : state :=
  let (rs, m) := s in
  fun x => if (Pos.eq_dec x pmem) then Memstate m
           else match (inv_ppos x) with
           | Some r => Val (rs r)
           | None => Val Vundef
           end.

Lemma pos_gpreg_not: forall g: gpreg, pmem <> (#g) /\ 2 <> (#g) /\ 3 <> (#g).
Proof.
  intros. split; try split. all: destruct g; try discriminate.
Qed.

Lemma not_3_plus_n:
  forall n, 3 + n <> pmem /\ 3 + n <> (# RA) /\ 3 + n <> (# PC).
Proof.
  intros. split; try split.
  all: destruct n; simpl; try (destruct n; discriminate); try discriminate.
Qed.

Lemma not_eq_add:
  forall k n n', n <> n' -> k + n <> k + n'.
Proof.
  intros k n n' H1 H2. apply H1; clear H1. eapply Pos.add_reg_l; eauto.
Qed.

Lemma not_eq_ireg_to_pos:
  forall n r r', r' <> r -> n + ireg_to_pos r <> n + ireg_to_pos r'.
Proof.
  intros. destruct r; destruct r'; try contradiction; apply not_eq_add; discriminate.
Qed.

Lemma not_eq_ireg_ppos: 
  forall r r', r <> r' -> (# r') <> (# r).
Proof.
  intros. unfold ppos. destruct r.
  - destruct r'; try discriminate.
    + apply not_eq_ireg_to_pos; congruence.
    + destruct g; discriminate.
    + destruct g; discriminate.
  - destruct r'; try discriminate; try contradiction.
    destruct g; discriminate.
  - destruct r'; try discriminate; try contradiction.
    destruct g; discriminate.
Qed.

Lemma not_eq_ireg_to_pos_ppos:
  forall r r', r' <> r -> 3 + ireg_to_pos r <> # r'.
Proof.
  intros. unfold ppos. apply not_eq_ireg_to_pos. assumption.
Qed.

Lemma not_eq_IR:
  forall r r', r <> r' -> IR r <> IR r'.
Proof.
  intros. congruence.
Qed.

Ltac Simplif :=
  ((rewrite nextblock_inv by eauto with asmgen)
  || (rewrite nextblock_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextblock_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)
  || (rewrite assign_diff by (try discriminate; try (apply pos_gpreg_not); try (apply not_3_plus_n); try (apply not_eq_ireg_ppos; apply not_eq_IR; auto); try (apply not_eq_ireg_to_pos_ppos; auto)))
  || (rewrite assign_eq)
  ); auto with asmgen.

Ltac Simpl := repeat Simplif.

Arguments Pos.add: simpl never.

Theorem trans_state_match: forall S, match_states S (trans_state S).
Proof.
  intros. destruct S as (rs & m). simpl.
  split. reflexivity.
  intro. destruct r; try reflexivity.
  destruct g; reflexivity.
Qed.

Lemma exec_app_some:
  forall c c' s s' s'',
  exec Ge c s = Some s' ->
  exec Ge c' s' = Some s'' ->
  exec Ge (c ++ c') s = Some s''.
Proof.
  induction c.
  - simpl. intros. congruence.
  - intros. simpl in *. destruct (macro_run _ _ _ _); auto. eapply IHc; eauto. discriminate.
Qed.

Lemma exec_app_none:
  forall c c' s,
  exec Ge c s = None ->
  exec Ge (c ++ c') s = None.
Proof.
  induction c.
  - simpl. discriminate.
  - intros. simpl. simpl in H. destruct (macro_run _ _ _ _); auto.
Qed.

Lemma trans_arith_correct:
  forall ge fn i rs m rs' s,
  exec_arith_instr ge i rs m = rs' ->
  match_states (State rs m) s ->
  exists s',
     macro_run (Genv ge fn) (trans_arith i) s s = Some s'
  /\ match_states (State rs' m) s'.
Proof.
  intros. unfold exec_arith_instr in H. destruct i.
(* Ploadsymbol *)
  - destruct i. inv H. inv H0.
    eexists; split; try split.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRR *)
  - destruct i.
    all: inv H; inv H0;
    eexists; split; try split;
    [ simpl; pose (H1 rs0); simpl in e; rewrite e; reflexivity |
      Simpl |
      intros rr; destruct rr; Simpl;
      destruct (ireg_eq g rd); subst; Simpl ].
(* PArithRI32 *)
  - destruct i. inv H. inv H0.
    eexists; split; try split.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRI64 *)
  - destruct i. inv H. inv H0.
    eexists; split; try split.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRF32 *)
  - destruct i. inv H. inv H0.
    eexists; split; try split.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRF64 *)
  - destruct i. inv H. inv H0.
    eexists; split; try split.
    * Simpl.
    * intros rr; destruct rr; Simpl.
      destruct (ireg_eq g rd); subst; Simpl.
(* PArithRRR *)
  - destruct i.
    all: inv H; inv H0;
    eexists; split; try split;
    [ simpl; pose (H1 rs1); simpl in e; rewrite e; pose (H1 rs2); simpl in e0; rewrite e0; try (rewrite H); reflexivity
    | Simpl
    | intros rr; destruct rr; Simpl;
      destruct (ireg_eq g rd); subst; Simpl ].
(* PArithRRI32 *)
  - destruct i.
    all: inv H; inv H0;
    eexists; split; try split;
    [ simpl; pose (H1 rs0); simpl in e; rewrite e; try (rewrite H); reflexivity
    | Simpl
    | intros rr; destruct rr; Simpl;
      destruct (ireg_eq g rd); subst; Simpl ].
(* PArithRRI64 *)
  - destruct i.
    all: inv H; inv H0;
    eexists; split; try split;
    [ simpl; pose (H1 rs0); simpl in e; rewrite e; try (rewrite H); reflexivity
    | Simpl
    | intros rr; destruct rr; Simpl;
      destruct (ireg_eq g rd); subst; Simpl ].
Qed.

Lemma forward_simu_basic:
  forall ge fn b rs m rs' m' s,
  exec_basic_instr ge b rs m = Next rs' m' ->
  match_states (State rs m) s ->
  exists s',
     macro_run (Genv ge fn) (trans_basic b) s s = Some s'
  /\ match_states (State rs' m') s'.
Proof.
  intros. destruct b.
(* Arith *)
  - simpl in H. inv H. simpl macro_run. eapply trans_arith_correct; eauto.
(* Load *)
  - simpl in H. destruct i; destruct i.
    all: unfold exec_load in H; destruct (eval_offset _ _) eqn:EVALOFF; try discriminate;
    destruct (Mem.loadv _ _ _) eqn:MEML; try discriminate; inv H; inv H0;
    eexists; split; try split;
    [ simpl; rewrite EVALOFF; rewrite H; pose (H1 ra); simpl in e; rewrite e; rewrite MEML; reflexivity|
     Simpl|
     intros rr; destruct rr; Simpl;
      destruct (ireg_eq g rd); [
       subst; Simpl|
       Simpl; rewrite assign_diff; pose (H1 g); simpl in e; try assumption; Simpl; unfold ppos; apply not_eq_ireg_to_pos; assumption]].
(* Store *)
  - simpl in H. destruct i; destruct i.
    all: unfold exec_store in H; destruct (eval_offset _ _) eqn:EVALOFF; try discriminate;
    destruct (Mem.storev _ _ _ _) eqn:MEML; try discriminate; inv H; inv H0;
    eexists; split; try split;
    [ simpl; rewrite EVALOFF; rewrite H; pose (H1 ra); simpl in e; rewrite e; pose (H1 rs0); simpl in e0; rewrite e0; rewrite MEML; reflexivity
    | Simpl
    | intros rr; destruct rr; Simpl].
(* Allocframe *)
  - simpl in H. destruct (Mem.alloc _ _ _) eqn:MEMAL. destruct (Mem.store _ _ _ _) eqn:MEMS; try discriminate.
    inv H. inv H0. eexists. split; try split.
    * simpl. Simpl. pose (H1 GPR12); simpl in e; rewrite e. rewrite H. rewrite MEMAL. rewrite MEMS. Simpl.
      rewrite H. rewrite MEMAL. rewrite MEMS. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl. destruct (ireg_eq g GPR32); [| destruct (ireg_eq g GPR12); [| destruct (ireg_eq g GPR14)]].
      ** subst. Simpl.
      ** subst. Simpl.
      ** subst. Simpl.
      ** Simpl. repeat (rewrite assign_diff). auto.
         pose (not_eq_ireg_to_pos_ppos GPR14 g). simpl ireg_to_pos in n2. auto.
         pose (not_eq_ireg_to_pos_ppos GPR12 g). simpl ireg_to_pos in n2. auto.
         pose (not_eq_ireg_to_pos_ppos GPR32 g). simpl ireg_to_pos in n2. auto.
(* Freeframe *)
  - simpl in H. destruct (Mem.loadv _ _ _) eqn:MLOAD; try discriminate. destruct (rs GPR12) eqn:SPeq; try discriminate.
    destruct (Mem.free _ _ _ _) eqn:MFREE; try discriminate. inv H. inv H0.
    eexists. split; try split.
    * simpl. pose (H1 GPR12); simpl in e; rewrite e. rewrite H. rewrite SPeq. rewrite MLOAD. rewrite MFREE.
      Simpl. rewrite e. rewrite SPeq. rewrite MLOAD. rewrite MFREE. reflexivity.
    * Simpl.
    * intros rr; destruct rr; Simpl. destruct (ireg_eq g GPR32); [| destruct (ireg_eq g GPR12); [| destruct (ireg_eq g GPR14)]].
      ** subst. Simpl.
      ** subst. Simpl.
      ** subst. Simpl.
      ** Simpl. repeat (rewrite assign_diff). auto.
         unfold ppos. pose (not_3_plus_n (ireg_to_pos g)). destruct a as (A & _ & _). auto.
         pose (not_eq_ireg_to_pos_ppos GPR12 g). simpl ireg_to_pos in n2. auto.
         pose (not_eq_ireg_to_pos_ppos GPR32 g). simpl ireg_to_pos in n2. auto.
(* Pget *)
  - simpl in H. destruct rs0 eqn:rs0eq; try discriminate. inv H. inv H0.
    eexists. split; try split. Simpl. intros rr; destruct rr; Simpl.
    destruct (ireg_eq g rd).
    * subst. Simpl.
    * Simpl.
(* Pset *)
  - simpl in H. destruct rd eqn:rdeq; try discriminate. inv H. inv H0.
    eexists. split; try split. Simpl. intros rr; destruct rr; Simpl.
(* Pnop *)
  - simpl in H. inv H. inv H0. eexists. split; try split. assumption. assumption.
Qed.

Lemma forward_simu_body:
  forall bdy ge rs m rs' m' fn s,
  Ge = Genv ge fn ->
  exec_body ge bdy rs m = Next rs' m' ->
  match_states (State rs m) s ->
  exists s',
     exec Ge (trans_body bdy) s = Some s'
  /\ match_states (State rs' m') s'.
Proof.
  induction bdy.
  - intros. inv H1. simpl in *. inv H0. eexists. repeat (split; auto).
  - intros until s. intros GE EXEB MS. simpl in EXEB. destruct (exec_basic_instr _ _ _ _) eqn:EBI; try discriminate.
    exploit forward_simu_basic; eauto. intros (s' & MRUN & MS'). subst Ge.
    eapply IHbdy in MS'; eauto. destruct MS' as (s'' & EXECB & MS').
    eexists. split.
    * simpl. rewrite MRUN. eassumption.
    * eassumption.
Qed.

Lemma forward_simu_control:
  forall ge fn ex b rs m rs2 m2 s,
  Ge = Genv ge fn ->
  exec_control ge fn ex (nextblock b rs) m = Next rs2 m2 ->
  match_states (State rs m) s ->
  exists s',
     exec Ge (trans_pcincr (size b) ++ trans_exit ex) s = Some s'
  /\ match_states (State rs2 m2) s'.
Proof.
  intros. destruct ex.
  - simpl in *. inv H1. destruct c; destruct i; try discriminate.
    all: try (inv H0; eexists; split; try split; [ simpl control_eval; pose (H3 PC); simpl in e; rewrite e; reflexivity | Simpl | intros rr; destruct rr; Simpl]).
    (* Pj_l *)
    + unfold goto_label in H0. destruct (label_pos _ _ _) eqn:LPOS; try discriminate. destruct (nextblock _ _ _) eqn:NB; try discriminate. inv H0.
      eexists; split; try split.
      * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl. unfold goto_label_deps. rewrite LPOS. rewrite nextblock_pc in NB.
        rewrite NB. reflexivity.
      * Simpl.
      * intros rr; destruct rr; Simpl.
    (* Pcb *)
    + destruct (cmp_for_btest _) eqn:CFB. destruct o; try discriminate. destruct i.
      ++ unfold eval_branch in H0. destruct (Val.cmp_bool _ _ _) eqn:VALCMP; try discriminate. destruct b0.
        +++ unfold goto_label in H0. destruct (label_pos _ _ _) eqn:LPOS; try discriminate. destruct (nextblock b rs PC) eqn:NB; try discriminate.
            inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              unfold goto_label_deps. rewrite LPOS. rewrite nextblock_pc in NB. rewrite NB. reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
        +++ inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
      ++ unfold eval_branch in H0. destruct (Val.cmpl_bool _ _ _) eqn:VALCMP; try discriminate. destruct b0.
        +++ unfold goto_label in H0. destruct (label_pos _ _ _) eqn:LPOS; try discriminate. destruct (nextblock b rs PC) eqn:NB; try discriminate.
            inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              unfold goto_label_deps. rewrite LPOS. rewrite nextblock_pc in NB. rewrite NB. reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
        +++ inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
    (* Pcbu *)
    + destruct (cmpu_for_btest _) eqn:CFB. destruct o; try discriminate. destruct i.
      ++ unfold eval_branch in H0. destruct (Val.cmpu_bool _ _ _) eqn:VALCMP; try discriminate. destruct b0.
        +++ unfold goto_label in H0. destruct (label_pos _ _ _) eqn:LPOS; try discriminate. destruct (nextblock b rs PC) eqn:NB; try discriminate.
            inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. rewrite H2. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              unfold goto_label_deps. rewrite LPOS. rewrite nextblock_pc in NB. rewrite NB. reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
        +++ inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. rewrite H2. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
      ++ unfold eval_branch in H0. destruct (Val.cmplu_bool _ _ _) eqn:VALCMP; try discriminate. destruct b0.
        +++ unfold goto_label in H0. destruct (label_pos _ _ _) eqn:LPOS; try discriminate. destruct (nextblock b rs PC) eqn:NB; try discriminate.
            inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. rewrite H2. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              unfold goto_label_deps. rewrite LPOS. rewrite nextblock_pc in NB. rewrite NB. reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
        +++ inv H0. eexists; split; try split.
            * simpl control_eval. pose (H3 PC); simpl in e; rewrite e. simpl.
              rewrite CFB. Simpl. rewrite H2. pose (H3 r). simpl in e0. rewrite e0.
              unfold eval_branch_deps. unfold nextblock in VALCMP. rewrite Pregmap.gso in VALCMP; try discriminate. rewrite VALCMP.
              reflexivity.
            * Simpl.
            * intros rr; destruct rr; Simpl.
  - simpl in *. inv H1. inv H0. eexists. split.
    pose (H3 PC). simpl in e. rewrite e. simpl. reflexivity.
    split. Simpl.
    intros. unfold nextblock. destruct r; Simpl.
Qed. 

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
  exploit forward_simu_control; eauto. intros (s'' & EXETRANSEX & MS'').

  eexists. split.
  unfold trans_block. eapply exec_app_some. eassumption. eassumption.
  eassumption.
Qed.

Lemma exec_bblock_stuck_nec:
  forall ge fn b rs m,
     exec_body ge (body b) rs m = Stuck
  \/ (exists rs' m', exec_body ge (body b) rs m = Next rs' m' /\ exec_control ge fn (exit b) (nextblock b rs') m' = Stuck)
  <-> exec_bblock ge fn b rs m = Stuck.
Proof.
  intros. split.
  + intros. destruct H.
    - unfold exec_bblock. rewrite H. reflexivity.
    - destruct H as (rs' & m' & EXEB & EXEC). unfold exec_bblock. rewrite EXEB. assumption.
  + intros. unfold exec_bblock in H. destruct (exec_body _ _ _ _) eqn:EXEB.
    - right. repeat eexists. assumption.
    - left. reflexivity.
Qed.

Lemma exec_basic_instr_next_exec:
  forall ge fn i rs m rs' m' s tc,
  Ge = Genv ge fn ->
  exec_basic_instr ge i rs m = Next rs' m' ->
  match_states (State rs m) s ->
  exists s',
     exec Ge (trans_basic i :: tc) s = exec Ge tc s'
  /\ match_states (State rs' m') s'.
Proof.
  intros. exploit forward_simu_basic; eauto.
  intros (s' & MRUN & MS').
  simpl exec. exists s'. subst. rewrite MRUN. split; auto.
Qed.

Lemma exec_body_next_exec:
  forall c ge fn rs m rs' m' s tc,
  Ge = Genv ge fn ->
  exec_body ge c rs m = Next rs' m' ->
  match_states (State rs m) s ->
  exists s',
     exec Ge (trans_body c ++ tc) s = exec Ge tc s'
  /\ match_states (State rs' m') s'.
Proof.
  induction c.
  - intros. simpl in H0. inv H0. simpl. exists s. split; auto.
  - intros. simpl in H0. destruct (exec_basic_instr _ _ _ _) eqn:EBI; try discriminate.
    exploit exec_basic_instr_next_exec; eauto. intros (s' & EXEGEBASIC & MS').
    simpl trans_body. rewrite <- app_comm_cons. rewrite EXEGEBASIC.
    eapply IHc; eauto.
Qed.

Lemma exec_trans_pcincr_exec:
  forall rs m s b,
  match_states (State rs m) s ->
  exists s',
     exec Ge (trans_pcincr (size b) ++ trans_exit (exit b)) s = exec Ge (trans_exit (exit b)) s'
  /\ match_states (State (nextblock b rs) m) s'.
Proof.
  intros. inv H. eexists. split. simpl.
  unfold control_eval. pose (H1 PC); simpl in e; rewrite e. destruct Ge. reflexivity.
  simpl. split.
  - Simpl.
  - intros rr; destruct rr; Simpl.
Qed.

Lemma exec_exit_none:
  forall ge fn rs m s ex,
  Ge = Genv ge fn ->
  match_states (State rs m) s ->
  exec Ge (trans_exit ex) s = None ->
  exec_control ge fn ex rs m = Stuck.
Proof.
  intros. inv H0. destruct ex as [ctl|]; try discriminate.
  destruct ctl; destruct i; try reflexivity; try discriminate.
(* Pj_l *)
  - simpl in *. pose (H3 PC); simpl in e; rewrite e in H1. clear e.
    unfold goto_label_deps in H1. unfold goto_label.
    destruct (label_pos _ _ _); auto. destruct (rs PC); auto. discriminate.
(* Pcb *)
  - simpl in *. destruct (cmp_for_btest bt). destruct i.
    + pose (H3 PC); simpl in e; rewrite e in H1; clear e.
      destruct o; auto. pose (H3 r); simpl in e; rewrite e in H1; clear e.
      unfold eval_branch_deps in H1; unfold eval_branch.
      destruct (Val.cmp_bool _ _ _); auto. destruct b; try discriminate.
      unfold goto_label_deps in H1; unfold goto_label. destruct (label_pos _ _ _); auto.
      destruct (rs PC); auto. discriminate.
    + pose (H3 PC); simpl in e; rewrite e in H1; clear e.
      destruct o; auto. pose (H3 r); simpl in e; rewrite e in H1; clear e.
      unfold eval_branch_deps in H1; unfold eval_branch.
      destruct (Val.cmpl_bool _ _ _); auto. destruct b; try discriminate.
      unfold goto_label_deps in H1; unfold goto_label. destruct (label_pos _ _ _); auto.
      destruct (rs PC); auto. discriminate.
(* Pcbu *)
  - simpl in *. destruct (cmpu_for_btest bt). destruct i.
    + pose (H3 PC); simpl in e; rewrite e in H1; clear e.
      destruct o; auto. rewrite H2 in H1.
      pose (H3 r); simpl in e; rewrite e in H1; clear e.
      unfold eval_branch_deps in H1; unfold eval_branch.
      destruct (Val.cmpu_bool _ _ _ _); auto. destruct b; try discriminate.
      unfold goto_label_deps in H1; unfold goto_label. destruct (label_pos _ _ _); auto.
      destruct (rs PC); auto. discriminate.
    + pose (H3 PC); simpl in e; rewrite e in H1; clear e.
      destruct o; auto. rewrite H2 in H1.
      pose (H3 r); simpl in e; rewrite e in H1; clear e.
      unfold eval_branch_deps in H1; unfold eval_branch.
      destruct (Val.cmplu_bool _ _ _); auto. destruct b; try discriminate.
      unfold goto_label_deps in H1; unfold goto_label. destruct (label_pos _ _ _); auto.
      destruct (rs PC); auto. discriminate.
Qed.

Theorem trans_block_reverse_stuck:
  forall ge fn b rs m s,
  Ge = Genv ge fn ->
  exec Ge (trans_block b) s = None ->
  match_states (State rs m) s ->
  exec_bblock ge fn b rs m = Stuck.
Proof.
  intros until s. intros Geq EXECBK MS.
  apply exec_bblock_stuck_nec.
  destruct (exec_body _ _ _ _) eqn:EXEB.
  - right. repeat eexists.
    exploit exec_body_next_exec; eauto.
    intros (s' & EXECBK' & MS'). unfold trans_block in EXECBK. rewrite EXECBK' in EXECBK. clear EXECBK'. clear EXEB MS.
    exploit exec_trans_pcincr_exec; eauto. intros (s'' & EXECINCR' & MS''). rewrite EXECINCR' in EXECBK. clear EXECINCR' MS'.
    eapply exec_exit_none; eauto.
  - left. reflexivity.
Qed.

Lemma forward_simu_basic_instr_stuck:
  forall i ge fn rs m s,
  Ge = Genv ge fn ->
  exec_basic_instr ge i rs m = Stuck ->
  match_states (State rs m) s ->
  exec Ge [trans_basic i] s = None.
Proof.
  intros. inv H1. unfold exec_basic_instr in H0. destruct i; try discriminate.
(* PLoad *)
  - destruct i; destruct i.
    all: simpl; rewrite H2; pose (H3 ra); simpl in e; rewrite e; clear e;
    unfold exec_load in H0; destruct (eval_offset _ _); auto; destruct (Mem.loadv _ _ _); auto; discriminate.
(* PStore *)
  - destruct i; destruct i;
    simpl; rewrite H2; pose (H3 ra); simpl in e; rewrite e; clear e; pose (H3 rs0); simpl in e; rewrite e; clear e;
    unfold exec_store in H0; destruct (eval_offset _ _); auto; destruct (Mem.storev _ _ _); auto; discriminate.
(* Pallocframe *)
  - simpl. Simpl. pose (H3 SP); simpl in e; rewrite e; clear e. rewrite H2. destruct (Mem.alloc _ _ _). simpl in H0.
    destruct (Mem.store _ _ _ _); try discriminate. reflexivity.
(* Pfreeframe *)
  - simpl. Simpl. pose (H3 SP); simpl in e; rewrite e; clear e. rewrite H2.
    destruct (Mem.loadv _ _ _); auto. destruct (rs GPR12); auto. destruct (Mem.free _ _ _ _); auto.
    discriminate.
(* Pget *)
  - simpl. destruct rs0; subst; try discriminate.
    all: simpl; auto.
  - simpl. destruct rd; subst; try discriminate.
    all: simpl; auto.
Qed.

Lemma forward_simu_body_stuck:
  forall bdy ge fn rs m s,
  Ge = Genv ge fn ->
  exec_body ge bdy rs m = Stuck ->
  match_states (State rs m) s ->
  exec Ge (trans_body bdy) s = None.
Proof.
  induction bdy.
  - simpl. discriminate.
  - intros. simpl trans_body. simpl in H0.
    destruct (exec_basic_instr _ _ _ _) eqn:EBI.
    + exploit exec_basic_instr_next_exec; eauto. intros (s' & EXEGEB & MS'). rewrite EXEGEB. eapply IHbdy; eauto.
    + cutrewrite (trans_basic a :: trans_body bdy = (trans_basic a :: nil) ++ trans_body bdy); try reflexivity. apply exec_app_none.
      eapply forward_simu_basic_instr_stuck; eauto.
Qed.


Lemma forward_simu_exit_stuck:
  forall ex ge fn rs m s,
  Ge = Genv ge fn ->
  exec_control ge fn ex rs m = Stuck ->
  match_states (State rs m) s ->
  exec Ge (trans_exit ex) s = None.
Proof.
  intros. inv H1. destruct ex as [ctl|]; try discriminate.
  destruct ctl; destruct i; try discriminate; try (simpl; reflexivity).
(* Pj_l *)
  - simpl in *. pose (H3 PC); simpl in e; rewrite e. unfold goto_label_deps. unfold goto_label in H0.
    destruct (label_pos _ _ _); auto. clear e. destruct (rs PC); auto. discriminate.
(* Pcb *)
  - simpl in *. destruct (cmp_for_btest bt). destruct i.
    -- destruct o.
      + unfold eval_branch in H0; unfold eval_branch_deps.
        pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. destruct (Val.cmp_bool _ _ _); auto.
        destruct b; try discriminate. unfold goto_label_deps; unfold goto_label in H0. clear e0.
        destruct (label_pos _ _ _); auto. destruct (rs PC); auto. discriminate.
      + pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. reflexivity.
    -- destruct o.
      + unfold eval_branch in H0; unfold eval_branch_deps.
        pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. destruct (Val.cmpl_bool _ _ _); auto.
        destruct b; try discriminate. unfold goto_label_deps; unfold goto_label in H0. clear e0.
        destruct (label_pos _ _ _); auto. destruct (rs PC); auto. discriminate.
      + pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. reflexivity.
(* Pcbu *)
  - simpl in *. destruct (cmpu_for_btest bt). destruct i.
    -- destruct o.
      + rewrite H2. unfold eval_branch in H0; unfold eval_branch_deps.
        pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. destruct (Val.cmpu_bool _ _ _); auto.
        destruct b; try discriminate. unfold goto_label_deps; unfold goto_label in H0. clear e0.
        destruct (label_pos _ _ _); auto. destruct (rs PC); auto. discriminate.
      + rewrite H2. pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. reflexivity.
    -- destruct o.
      + rewrite H2. unfold eval_branch in H0; unfold eval_branch_deps.
        pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. destruct (Val.cmplu_bool _ _ _); auto.
        destruct b; try discriminate. unfold goto_label_deps; unfold goto_label in H0. clear e0.
        destruct (label_pos _ _ _); auto. destruct (rs PC); auto. discriminate.
      + rewrite H2. pose (H3 r); simpl in e; rewrite e. pose (H3 PC); simpl in e0; rewrite e0. reflexivity.
Qed.


Theorem forward_simu_stuck:
  forall rs1 m1 s1' b ge fn,
    Ge = Genv ge fn ->
    exec_bblock ge fn b rs1 m1 = Stuck ->
    match_states (State rs1 m1) s1' ->
    exec Ge (trans_block b) s1' = None.
Proof.
  intros until fn. intros GENV EXECB MS. apply exec_bblock_stuck_nec in EXECB. destruct EXECB.
  - unfold trans_block. apply exec_app_none. eapply forward_simu_body_stuck; eauto.
  - destruct H as (rs' & m' & EXEB & EXEC). unfold trans_block. exploit exec_body_next_exec; eauto.
    intros (s' & EXEGEBODY & MS'). rewrite EXEGEBODY. exploit exec_trans_pcincr_exec; eauto.
    intros (s'' & EXEGEPC & MS''). rewrite EXEGEPC. eapply forward_simu_exit_stuck; eauto.
Qed.


Lemma state_eq_decomp:
  forall rs1 m1 rs2 m2, rs1 = rs2 -> m1 = m2 -> State rs1 m1 = State rs2 m2.
Proof.
  intros. congruence.
Qed.

Theorem state_equiv:
  forall S1 S2 S', match_states S1 S' /\ match_states S2 S' -> S1 = S2.
Proof.
  intros. inv H. unfold match_states in H0, H1. destruct S1 as (rs1 & m1). destruct S2 as (rs2 & m2). inv H0. inv H1.
  apply state_eq_decomp.
  - apply functional_extensionality. intros. assert (Val (rs1 x) = Val (rs2 x)) by congruence. congruence.
  - congruence.
Qed.

Theorem forward_simu_alt:
  forall rs1 m1 s1' b ge fn,
    Ge = Genv ge fn ->
    match_states (State rs1 m1) s1' -> 
    match_outcome (exec_bblock ge fn b rs1 m1) (exec Ge (trans_block b) s1').
Proof.
  intros until fn. intros GENV MS. destruct (exec_bblock _ _ _ _ _) eqn:EXEB.
  - eapply forward_simu; eauto.
  - eapply forward_simu_stuck; eauto.
Qed.

Local Hint Resolve trans_state_match.

Lemma bblock_equiv_reduce: 
  forall p1 p2 ge fn,
  Ge = Genv ge fn ->
  L.bblock_equiv Ge (trans_block p1) (trans_block p2) ->
  Asmblockgenproof0.bblock_equiv ge fn p1 p2.
Proof.
  unfold bblock_equiv, res_eq; intros p1 p2 ge fn H1 H2; constructor.
  intros rs m.
  generalize (H2 (trans_state (State rs m))); clear H2.
  intro H2. 
  exploit (forward_simu_alt rs m (trans_state (State rs m)) p1 ge fn); eauto.
  exploit (forward_simu_alt rs m (trans_state (State rs m)) p2 ge fn); eauto.
  remember (exec_bblock ge fn p1 rs m) as exp1.
  destruct exp1.
  + (* Next *) 
    intros H3 (s2' & exp2 & MS'). unfold exec in exp2, H3. rewrite exp2 in H2.
    destruct H2 as (m2' & H2 & H4). rewrite H2 in H3.
    destruct (exec_bblock ge fn p2 rs m); simpl in H3.
    * destruct H3 as (s' & H3 & H5 & H6). inv H3. inv MS'.
      cutrewrite (rs0=rs1).
      - cutrewrite (m0=m1); auto. congruence.
      - apply functional_extensionality. intros r.
        generalize (H0 r). intros Hr. congruence.
    * discriminate.
  + intros MO MO2. remember (trans_state (State rs m)) as s1. inversion MO2. clear MO2. unfold exec in *.
    rewrite H0 in H2. clear H0. destruct (exec_bblock ge fn p2 rs m); auto. rewrite H2 in MO. unfold match_outcome in MO.
    destruct MO as (? & ? & ?). discriminate.
Qed.

Definition string_of_name (x: P.R.t): ?? pstring := RET (Str ("resname")).
(*   match x with
  | xH => RET (Str ("the_mem"))
  | _ as x => 
     DO s <~ string_of_Z (Zpos (Pos.pred x)) ;;
     RET ("R" +; s)
  end. *)

Definition string_of_op (op: P.op): ?? pstring := RET (Str ("OP")).
(*   match op with
  | P.Imm i => 
     DO s <~ string_of_Z i ;;
     RET s
  | P.ARITH ADD => RET (Str "ADD")
  | P.ARITH SUB => RET (Str "SUB")
  | P.ARITH MUL => RET (Str "MUL")
  | P.LOAD => RET (Str "LOAD")
  | P.STORE => RET (Str "STORE")
  end. *)

Definition bblock_eq_test (verb: bool) (p1 p2: Asmblock.bblock) : ?? bool :=
  if verb then
    IDT.verb_bblock_eq_test string_of_name string_of_op (trans_block p1) (trans_block p2)
  else
    IDT.bblock_eq_test (trans_block p1) (trans_block p2).

Local Hint Resolve IDT.bblock_eq_test_correct bblock_equiv_reduce IDT.verb_bblock_eq_test_correct: wlp.

Theorem bblock_eq_test_correct verb p1 p2 :
  WHEN bblock_eq_test verb p1 p2 ~> b THEN b=true -> forall ge fn, Ge = Genv ge fn -> Asmblockgenproof0.bblock_equiv ge fn p1 p2.
Proof.
  wlp_simplify.
Qed.
Hint Resolve bblock_eq_test_correct: wlp.

(* Coerce bblock_eq_test into a pure function (this is a little unsafe like all oracles in CompCert). *)

Import UnsafeImpure.

Definition pure_bblock_eq_test (verb: bool) (p1 p2: Asmblock.bblock): bool := unsafe_coerce (bblock_eq_test verb p1 p2).

Theorem pure_bblock_eq_test_correct verb p1 p2:
  forall ge fn, Ge = Genv ge fn ->
   pure_bblock_eq_test verb p1 p2 = true -> Asmblockgenproof0.bblock_equiv ge fn p1 p2.
Proof.
   intros; unfold pure_bblock_eq_test. intros; eapply bblock_eq_test_correct; eauto.
   apply unsafe_coerce_not_really_correct; eauto.
Qed.

Definition bblock_equivb: Asmblock.bblock -> Asmblock.bblock -> bool := pure_bblock_eq_test true.

Definition bblock_equiv_eq := pure_bblock_eq_test_correct true.

End SECT.
