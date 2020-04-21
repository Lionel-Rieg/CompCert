(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Compopts.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op ExtValues ExtFloats RTL ValueDomain.

Definition intoffloat_total (x: aval) :=
  match x with
  | F f =>
      match Float.to_int f with
      | Some i => I i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition intuoffloat_total (x: aval) :=
  match x with
  | F f =>
      match Float.to_intu f with
      | Some i => I i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition intofsingle_total (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_int f with
      | Some i => I i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition intuofsingle_total (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_intu f with
      | Some i => I i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition longoffloat_total (x: aval) :=
  match x with
  | F f =>
      match Float.to_long f with
      | Some i => L i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition longuoffloat_total (x: aval) :=
  match x with
  | F f =>
      match Float.to_longu f with
      | Some i => L i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition longofsingle_total (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_long f with
      | Some i => L i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition longuofsingle_total (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_longu f with
      | Some i => L i
      | None => ntop
      end
  | _ => ntop1 x
  end.

Definition minf := binop_float ExtFloat.min.
Definition maxf := binop_float ExtFloat.max.
Definition minfs := binop_single ExtFloat32.min.
Definition maxfs := binop_single ExtFloat32.max.

Definition ntop3 (x y z: aval) : aval := Ifptr (plub (provenance x) (plub (provenance y) (provenance z))).
               
Definition triple_op_float (sem: float -> float -> float -> float) (x y z: aval) :=
  match x, y, z with
  | F a, F b, F c => F (sem a b c)
  | _, _, _ => ntop3 x y z
  end.
               
Definition triple_op_single (sem: float32 -> float32 -> float32 -> float32) (x y z: aval) :=
  match x, y, z with
  | FS a, FS b, FS c => FS (sem a b c)
  | _, _, _ => ntop3 x y z
  end.

Definition fmaddf := triple_op_float (fun x y z => Float.fma y z x).
Definition fmsubf := triple_op_float (fun x y z => Float.fma (Float.neg y) z x).
Definition fmaddfs := triple_op_single (fun x y z => Float32.fma y z x).
Definition fmsubfs := triple_op_single (fun x y z => Float32.fma (Float32.neg y) z x).

Definition invfs (y : aval) :=
  match y with
  | FS f => FS (ExtFloat32.inv f)
  | _ => ntop1 y
  end.

(** Value analysis for RISC V operators *)

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool c v1 (I n)
  | Ccompl c, v1 :: v2 :: nil => cmpl_bool c v1 v2
  | Ccomplu c, v1 :: v2 :: nil => cmplu_bool c v1 v2
  | Ccomplimm c n, v1 :: nil => cmpl_bool c v1 (L n)
  | Ccompluimm c n, v1 :: nil => cmplu_bool c v1 (L n)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Ccompfs c, v1 :: v2 :: nil => cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => cnot (cmpfs_bool c v1 v2)
  | _, _ => Bnone
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => offset_ptr v1 n
  | Aindexed2, v1::v2::nil => addl v1 v2
  | Aindexed2XS scale, v1::v2::nil => addl v1 (shll v2 (I (Int.repr scale)))
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Ainstack ofs, nil => Ptr (Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_static_condition0 (cond : condition0) (v : aval) : abool :=
  match cond with
  | Ccomp0 c => cmp_bool c v (I Int.zero)
  | Ccompu0 c => cmpu_bool c v (I Int.zero)
  | Ccompl0  c => cmpl_bool c v (L Int64.zero)
  | Ccomplu0 c => cmplu_bool c v (L Int64.zero)
  end.
  

Definition eval_static_extfs (stop : Z) (start : Z) (v : aval) :=
  if is_bitfield stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | I w =>
      I (Int.shr (Int.shl w (Int.repr (Z.sub Int.zwordsize stop'))) (Int.repr (Z.sub Int.zwordsize (Z.sub stop' start))))
    | _ => Vtop
    end
  else Vtop.

Definition eval_static_extfz (stop : Z) (start : Z) (v : aval) :=
  if is_bitfield stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | I w =>
      I (Int.shru (Int.shl w (Int.repr (Z.sub Int.zwordsize stop'))) (Int.repr (Z.sub Int.zwordsize (Z.sub stop' start))))
    | _ => Vtop
    end
  else Vtop.

Definition eval_static_extfsl (stop : Z) (start : Z) (v : aval) :=
  if is_bitfieldl stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | L w =>
      L (Int64.shr' (Int64.shl' w (Int.repr (Z.sub Int64.zwordsize stop'))) (Int.repr (Z.sub Int64.zwordsize (Z.sub stop' start))))
    | _ => Vtop
    end
  else Vtop.

Definition eval_static_extfzl (stop : Z) (start : Z) (v : aval) :=
  if is_bitfieldl stop start
  then
    let stop' := Z.add stop Z.one in
    match v with
    | L w =>
      L (Int64.shru' (Int64.shl' w (Int.repr (Z.sub Int64.zwordsize stop'))) (Int.repr (Z.sub Int64.zwordsize (Z.sub stop' start))))
    | _ => Vtop
    end
  else Vtop.

Definition eval_static_insf stop start prev fld :=
  let mask := Int.repr (zbitfield_mask stop start) in
  if is_bitfield stop start
  then
    match prev, fld with
    | (I prevI), (I fldI) =>
      if Int.ltu (Int.repr start) Int.iwordsize
      then I (Int.or (Int.and prevI (Int.not mask))
                     (Int.and (Int.shl fldI (Int.repr start)) mask))
      else Vtop
    | _, _ => Vtop
    end
  else Vtop.

Definition eval_static_insfl stop start prev fld :=
  let mask := Int64.repr (zbitfield_mask stop start) in
  if is_bitfieldl stop start
  then
    match prev, fld with
    | (L prevL), (L fldL) =>
      if Int.ltu (Int.repr start) Int64.iwordsize'
      then L (Int64.or (Int64.and prevL (Int64.not mask))
                       (Int64.and (Int64.shl' fldL (Int.repr start)) mask))
      else Vtop
    | _,_ => Vtop
    end
  else Vtop.

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Olongconst n, nil => L n
  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oaddrsymbol id ofs, nil => Ptr (Gl id ofs)
  | Oaddrstack ofs, nil => Ptr (Stk ofs)
  | Ocast8signed, v1 :: nil => sign_ext 8 v1
  | Ocast16signed, v1 :: nil => sign_ext 16 v1
  | Oadd, v1::v2::nil => add v1 v2
  | Oaddimm n, v1::nil => add v1 (I n)
  | Oaddx shift, v1::v2::nil => add v2 (shl v1 (I (int_of_shift1_4 shift)))
  | Oaddximm shift n, v1::nil => add (I n) (shl v1 (I (int_of_shift1_4 shift)))
  | Oneg, v1::nil => neg v1
  | Osub, v1::v2::nil => sub v1 v2
  | Orevsubx shift, v1::v2::nil => sub v2 (shl v1 (I (int_of_shift1_4 shift)))
  | Orevsubimm n, v1::nil => sub (I n) v1
  | Orevsubximm shift n, v1::nil => sub (I n) (shl v1 (I (int_of_shift1_4 shift)))
  | Omul, v1::v2::nil => mul v1 v2
  | Omulimm n, v1::nil => mul v1 (I n)
  | Omulhs, v1::v2::nil => mulhs v1 v2
  | Omulhu, v1::v2::nil => mulhu v1 v2
  | Odiv, v1::v2::nil => divs v1 v2
  | Odivu, v1::v2::nil => divu v1 v2
  | Omod, v1::v2::nil => mods v1 v2
  | Omodu, v1::v2::nil => modu v1 v2
  | Oand, v1::v2::nil => and v1 v2
  | Oandimm n, v1::nil => and v1 (I n)
  | Onand, v1::v2::nil => notint (and v1 v2)
  | Onandimm n, v1::nil => notint (and v1 (I n))
  | Oor, v1::v2::nil => or v1 v2
  | Oorimm n, v1::nil => or v1 (I n)
  | Onor, v1::v2::nil => notint (or v1 v2)
  | Onorimm n, v1::nil => notint (or v1 (I n))
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Onxor, v1::v2::nil => notint (xor v1 v2)
  | Onxorimm n, v1::nil => notint (xor v1 (I n))
  | Onot, v1::nil => notint v1
  | Oandn, v1::v2::nil => and (notint v1) v2
  | Oandnimm n, v1::nil => and (notint v1) (I n)
  | Oorn, v1::v2::nil => or (notint v1) v2
  | Oornimm n, v1::nil => or (notint v1) (I n)
  | Oshl, v1::v2::nil => shl v1 v2
  | Oshlimm n, v1::nil => shl v1 (I n)
  | Oshr, v1::v2::nil => shr v1 v2
  | Oshrimm n, v1::nil => shr v1 (I n)
  | Ororimm n, v1::nil => ror v1 (I n)
  | Oshru, v1::v2::nil => shru v1 v2
  | Oshruimm n, v1::nil => shru v1 (I n)
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Omadd, v1::v2::v3::nil => add v1 (mul v2 v3)
  | Omaddimm n, v1::v2::nil => add v1 (mul v2 (I n))
  | Omsub, v1::v2::v3::nil => sub v1 (mul v2 v3)
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => loword v1
  | Ohighlong, v1::nil => hiword v1
  | Ocast32signed, v1::nil => longofint v1
  | Ocast32unsigned, v1::nil => longofintu v1
  | Oaddl, v1::v2::nil => addl v1 v2
  | Oaddlimm n, v1::nil => addl v1 (L n)
  | Oaddxl shift, v1::v2::nil => addl v2 (shll v1 (I (int_of_shift1_4 shift)))
  | Oaddxlimm shift n, v1::nil => addl (L n) (shll v1 (I (int_of_shift1_4 shift))) 
  | Onegl, v1::nil => negl v1
  | Osubl, v1::v2::nil => subl v1 v2
  | Orevsubxl shift, v1::v2::nil => subl v2 (shll v1 (I (int_of_shift1_4 shift)))
  | Orevsublimm n, v1::nil => subl (L n) v1
  | Orevsubxlimm shift n, v1::nil => subl (L n) (shll v1 (I (int_of_shift1_4 shift)))
  | Omull, v1::v2::nil => mull v1 v2
  | Omullimm n, v1::nil => mull v1 (L n)
  | Omullhs, v1::v2::nil => mullhs v1 v2
  | Omullhu, v1::v2::nil => mullhu v1 v2
  | Odivl, v1::v2::nil => divls v1 v2
  | Odivlu, v1::v2::nil => divlu v1 v2
  | Omodl, v1::v2::nil => modls v1 v2
  | Omodlu, v1::v2::nil => modlu v1 v2
  | Oandl, v1::v2::nil => andl v1 v2
  | Oandlimm n, v1::nil => andl v1 (L n)
  | Onandl, v1::v2::nil => notl (andl v1 v2)
  | Onandlimm n, v1::nil => notl (andl v1 (L n))
  | Oorl, v1::v2::nil => orl v1 v2
  | Oorlimm n, v1::nil => orl v1 (L n)
  | Onorl, v1::v2::nil => notl (orl v1 v2)
  | Onorlimm n, v1::nil => notl (orl v1 (L n))
  | Oxorl, v1::v2::nil => xorl v1 v2
  | Oxorlimm n, v1::nil => xorl v1 (L n)
  | Onxorl, v1::v2::nil => notl (xorl v1 v2)
  | Onxorlimm n, v1::nil => notl (xorl v1 (L n))
  | Onotl, v1::nil => notl v1
  | Oandnl, v1::v2::nil => andl (notl v1) v2
  | Oandnlimm n, v1::nil => andl (notl v1) (L n)
  | Oornl, v1::v2::nil => orl (notl v1) v2
  | Oornlimm n, v1::nil => orl (notl v1) (L n)
  | Oshll, v1::v2::nil => shll v1 v2
  | Oshllimm n, v1::nil => shll v1 (I n)
  | Oshrl, v1::v2::nil => shrl v1 v2
  | Oshrlimm n, v1::nil => shrl v1 (I n)
  | Oshrlu, v1::v2::nil => shrlu v1 v2
  | Oshrluimm n, v1::nil => shrlu v1 (I n)
  | Oshrxlimm n, v1::nil => shrxl v1 (I n)
  | Omaddl, v1::v2::v3::nil => addl v1 (mull v2 v3)
  | Omaddlimm n, v1::v2::nil => addl v1 (mull v2 (L n))
  | Omsubl, v1::v2::v3::nil => subl v1 (mull v2 v3)
  | Onegf, v1::nil => negf v1
  | Oabsf, v1::nil => absf v1
  | Oaddf, v1::v2::nil => addf v1 v2
  | Osubf, v1::v2::nil => subf v1 v2
  | Omulf, v1::v2::nil => mulf v1 v2
  | Odivf, v1::v2::nil => divf v1 v2
  | Ominf, v1::v2::nil => minf v1 v2
  | Omaxf, v1::v2::nil => maxf v1 v2
  | Ofmaddf, v1::v2::v3::nil => fmaddf v1 v2 v3
  | Ofmsubf, v1::v2::v3::nil => fmsubf v1 v2 v3
  | Onegfs, v1::nil => negfs v1
  | Oabsfs, v1::nil => absfs v1
  | Oaddfs, v1::v2::nil => addfs v1 v2
  | Osubfs, v1::v2::nil => subfs v1 v2
  | Omulfs, v1::v2::nil => mulfs v1 v2
  | Odivfs, v1::v2::nil => divfs v1 v2
  | Ominfs, v1::v2::nil => minfs v1 v2
  | Omaxfs, v1::v2::nil => maxfs v1 v2
  | Oinvfs, v1::nil => invfs v1
  | Ofmaddfs, v1::v2::v3::nil => fmaddfs v1 v2 v3
  | Ofmsubfs, v1::v2::v3::nil => fmsubfs v1 v2 v3
  | Osingleoffloat, v1::nil => singleoffloat v1
  | Ofloatofsingle, v1::nil => floatofsingle v1
  | Ointoffloat, v1::nil => intoffloat_total v1
  | Ointuoffloat, v1::nil => intuoffloat_total v1
  | Ointofsingle, v1::nil => intofsingle_total v1
  | Ointuofsingle, v1::nil => intuofsingle_total v1
  | Osingleofint, v1::nil => singleofint v1
  | Osingleofintu, v1::nil => singleofintu v1
  | Olongoffloat, v1::nil => longoffloat_total v1
  | Olonguoffloat, v1::nil => longuoffloat_total v1
  | Ofloatoflong, v1::nil => floatoflong v1
  | Ofloatoflongu, v1::nil => floatoflongu v1
  | Olongofsingle, v1::nil => longofsingle_total v1
  | Olonguofsingle, v1::nil => longuofsingle_total v1
  | Osingleoflong, v1::nil => singleoflong v1
  | Osingleoflongu, v1::nil => singleoflongu v1
  | Ocmp c, _ => of_optbool (eval_static_condition c vl)
  | (Oextfz stop start), v0::nil => eval_static_extfz stop start v0
  | (Oextfs stop start), v0::nil => eval_static_extfs stop start v0
  | (Oextfzl stop start), v0::nil => eval_static_extfzl stop start v0
  | (Oextfsl stop start), v0::nil => eval_static_extfsl stop start v0
  | (Oinsf stop start), v0::v1::nil => eval_static_insf stop start v0 v1
  | (Oinsfl stop start), v0::v1::nil => eval_static_insfl stop start v0 v1
  | Osel c ty, v1::v2::vc::nil => select (eval_static_condition0 c vc) v1 v2
  | Oselimm c imm, v1::vc::nil => select (eval_static_condition0 c vc) v1 (I imm)
  | Osellimm c imm, v1::vc::nil => select (eval_static_condition0 c vc) v1 (L imm)
  | _, _ => Vbot
  end.

Section SOUNDNESS.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.

Lemma intoffloat_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.intoffloat v)) (intoffloat_total x).
Proof.
  unfold Val.intoffloat, intoffloat_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float.to_int f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve intoffloat_total_sound : va.

Lemma intuoffloat_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.intuoffloat v)) (intuoffloat_total x).
Proof.
  unfold Val.intoffloat, intoffloat_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float.to_intu f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve intuoffloat_total_sound : va.

Lemma intofsingle_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.intofsingle v)) (intofsingle_total x).
Proof.
  unfold Val.intofsingle, intofsingle_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float32.to_int f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve intofsingle_total_sound : va.

Lemma intuofsingle_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.intuofsingle v)) (intuofsingle_total x).
Proof.
  unfold Val.intofsingle, intofsingle_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float32.to_intu f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve intuofsingle_total_sound : va.

Lemma singleofint_total_sound:
  forall v x, vmatch bc v x ->
              vmatch bc (Val.maketotal (Val.singleofint v)) (singleofint x).
Proof.
  unfold Val.singleofint, singleofint; intros.
  inv H; simpl.
  all: auto with va.
  all: unfold ntop1, provenance.
  all: try constructor.
Qed.

Hint Resolve singleofint_total_sound : va.

Lemma singleofintu_total_sound:
  forall v x, vmatch bc v x ->
              vmatch bc (Val.maketotal (Val.singleofintu v)) (singleofintu x).
Proof.
  unfold Val.singleofintu, singleofintu; intros.
  inv H; simpl.
  all: auto with va.
  all: unfold ntop1, provenance.
  all: try constructor.
Qed.

Hint Resolve singleofintu_total_sound : va.

Lemma longoffloat_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.longoffloat v)) (longoffloat_total x).
Proof.
  unfold Val.longoffloat, longoffloat_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float.to_long f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve longoffloat_total_sound : va.

Lemma longuoffloat_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.longuoffloat v)) (longuoffloat_total x).
Proof.
  unfold Val.longoffloat, longoffloat_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float.to_longu f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve longuoffloat_total_sound : va.

Lemma longofsingle_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.longofsingle v)) (longofsingle_total x).
Proof.
  unfold Val.longofsingle, longofsingle_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float32.to_long f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve longofsingle_total_sound : va.

Lemma longuofsingle_total_sound:
  forall v x
         (MATCH : vmatch bc v x),
    vmatch bc (Val.maketotal (Val.longuofsingle v)) (longuofsingle_total x).
Proof.
  unfold Val.longofsingle, longofsingle_total. intros.
  inv MATCH; simpl in *; try constructor.
  all: destruct (Float32.to_longu f) as [i|] eqn:E; simpl; [auto with va | constructor].
  unfold ntop1, provenance.
  destruct (va_strict tt); constructor.
Qed.

Hint Resolve longuofsingle_total_sound : va.

Lemma singleoflong_total_sound:
  forall v x, vmatch bc v x ->
              vmatch bc (Val.maketotal (Val.singleoflong v)) (singleoflong x).
Proof.
  unfold Val.singleoflong, singleoflong; intros.
  inv H; simpl.
  all: auto with va.
  all: unfold ntop1, provenance.
  all: try constructor.
Qed.

Hint Resolve singleoflong_total_sound : va.

Lemma singleoflongu_total_sound:
  forall v x, vmatch bc v x ->
              vmatch bc (Val.maketotal (Val.singleoflongu v)) (singleoflongu x).
Proof.
  unfold Val.singleoflongu, singleoflongu; intros.
  inv H; simpl.
  all: auto with va.
  all: unfold ntop1, provenance.
  all: try constructor.
Qed.

Hint Resolve singleoflongu_total_sound : va.

Lemma floatoflong_total_sound:
  forall v x, vmatch bc v x ->
              vmatch bc (Val.maketotal (Val.floatoflong v)) (floatoflong x).
Proof.
  unfold Val.floatoflong, floatoflong; intros.
  inv H; simpl.
  all: auto with va.
  all: unfold ntop1, provenance.
  all: try constructor.
Qed.

Hint Resolve floatoflong_total_sound : va.

Lemma floatoflongu_total_sound:
  forall v x, vmatch bc v x ->
              vmatch bc (Val.maketotal (Val.floatoflongu v)) (floatoflongu x).
Proof.
  unfold Val.floatoflongu, floatoflongu; intros.
  inv H; simpl.
  all: auto with va.
  all: unfold ntop1, provenance.
  all: try constructor.
Qed.

Hint Resolve floatoflongu_total_sound : va.

Lemma minf_sound:
  forall v x w y, vmatch bc v x -> vmatch bc w y -> vmatch bc (ExtValues.minf v w) (minf x y).
Proof.
  apply (binop_float_sound bc ExtFloat.min); assumption.
Qed.

Lemma maxf_sound:
  forall v x w y, vmatch bc v x -> vmatch bc w y -> vmatch bc (ExtValues.maxf v w) (maxf x y).
Proof.
  apply (binop_float_sound bc ExtFloat.max); assumption.
Qed.

Lemma minfs_sound:
  forall v x w y, vmatch bc v x -> vmatch bc w y -> vmatch bc (ExtValues.minfs v w) (minfs x y).
Proof.
  apply (binop_single_sound bc ExtFloat32.min); assumption.
Qed.

Lemma maxfs_sound:
  forall v x w y, vmatch bc v x -> vmatch bc w y -> vmatch bc (ExtValues.maxfs v w) (maxfs x y).
Proof.
  apply (binop_single_sound bc ExtFloat32.max); assumption.
Qed.

Lemma invfs_sound:
  forall v x, vmatch bc v x -> vmatch bc (ExtValues.invfs v) (invfs x).
Proof.
  intros v x;
  intro MATCH;
  inversion MATCH;
  simpl;
  constructor.
Qed.

Lemma triple_op_float_sound:
  forall f a x b y c z,
    vmatch bc a x -> vmatch bc b y -> vmatch bc c z ->
    vmatch bc (ExtValues.triple_op_float f a b c)
           (triple_op_float f x y z).
Proof.
  intros until z.
  intros Hax Hby Hcz.
  inv Hax; simpl; try constructor;
  inv Hby; simpl; try constructor;
  inv Hcz; simpl; try constructor.
Qed.

Lemma triple_op_single_sound:
  forall f a x b y c z,
    vmatch bc a x -> vmatch bc b y -> vmatch bc c z ->
    vmatch bc (ExtValues.triple_op_single f a b c)
           (triple_op_single f x y z).
Proof.
  intros until z.
  intros Hax Hby Hcz.
  inv Hax; simpl; try constructor;
  inv Hby; simpl; try constructor;
  inv Hcz; simpl; try constructor.
Qed.

Lemma fmaddf_sound :
  forall a x b y c z, vmatch bc a x -> vmatch bc b y -> vmatch bc c z ->
                      vmatch bc (ExtValues.fmaddf a b c) (fmaddf x y z).
Proof.
  intros. unfold ExtValues.fmaddf, fmaddf.
  apply triple_op_float_sound; assumption.
Qed.

Lemma fmaddfs_sound :
  forall a x b y c z, vmatch bc a x -> vmatch bc b y -> vmatch bc c z ->
                      vmatch bc (ExtValues.fmaddfs a b c) (fmaddfs x y z).
Proof.
  intros. unfold ExtValues.fmaddfs, fmaddfs.
  apply triple_op_single_sound; assumption.
Qed.

Lemma fmsubf_sound :
  forall a x b y c z, vmatch bc a x -> vmatch bc b y -> vmatch bc c z ->
                      vmatch bc (ExtValues.fmsubf a b c) (fmsubf x y z).
Proof.
  intros. unfold ExtValues.fmsubf, fmsubf.
  apply triple_op_float_sound; assumption.
Qed.

Lemma fmsubfs_sound :
  forall a x b y c z, vmatch bc a x -> vmatch bc b y -> vmatch bc c z ->
                      vmatch bc (ExtValues.fmsubfs a b c) (fmsubfs x y z).
Proof.
  intros. unfold ExtValues.fmsubfs, fmsubfs.
  apply triple_op_single_sound; assumption.
Qed.
Hint Resolve minf_sound maxf_sound minfs_sound maxfs_sound invfs_sound fmaddf_sound fmaddfs_sound fmsubf_sound fmsubfs_sound : va.

Theorem eval_static_condition_sound:
  forall cond vargs m aargs,
  list_forall2 (vmatch bc) vargs aargs ->
  cmatch (eval_condition cond vargs m) (eval_static_condition cond aargs).
Proof.
  intros until aargs; intros VM. inv VM.
  destruct cond; auto with va.
  inv H0.
  destruct cond; simpl; eauto with va.
  inv H2.
  destruct cond; simpl; eauto with va.
  destruct cond; auto with va.
Qed.

Theorem eval_static_condition0_sound:
  forall cond varg m aarg,
  vmatch bc varg aarg ->
  cmatch (eval_condition0 cond varg m) (eval_static_condition0 cond aarg).
Proof.
  intros until aarg; intro VM.
  destruct cond; simpl; eauto with va.
Qed.

Lemma symbol_address_sound:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs)).
Proof.
  intros; apply symbol_address_sound; apply GENV.
Qed.

Lemma symbol_address_sound_2:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ifptr (Gl id ofs)).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:F.
  constructor. constructor. apply GENV; auto.
  constructor.
Qed.

Hint Resolve symbol_address_sound symbol_address_sound_2: va.

Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | [H: (if Archi.ptr64 then _ else _) = Some _ |- _] => destruct Archi.ptr64 eqn:?; InvHyps
  | _ => idtac
  end.

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; eauto with va.
Qed.

Theorem eval_static_addressing_sound_none:
  forall addr vargs aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = None ->
  list_forall2 (vmatch bc) vargs aargs ->
  (eval_static_addressing addr aargs) = Vbot.
Proof.
  unfold eval_addressing, eval_static_addressing.
  intros until aargs. intros Heval_none Hlist.
  inv Hlist.
  destruct addr; trivial; discriminate.
  inv H0.
  destruct addr; trivial; discriminate.
  inv H2.
  destruct addr; trivial; discriminate.
  inv H3;
  destruct addr; trivial; discriminate.
Qed.

Lemma vmatch_vint_ntop1:
  forall x y, vmatch bc (Vint x) (ntop1 y).
Proof.
  intro. unfold ntop1, provenance.
  destruct y;
    destruct (va_strict tt);
    constructor.
Qed.

Lemma vmatch_vlong_ntop1:
  forall x y, vmatch bc (Vlong x) (ntop1 y).
Proof.
  intro. unfold ntop1, provenance.
  destruct y;
    destruct (va_strict tt);
    constructor.
Qed.

Hint Resolve vmatch_vint_ntop1 vmatch_vlong_ntop1: va.
       
Theorem eval_static_operation_sound:
  forall op vargs m vres aargs,
  eval_operation ge (Vptr sp Ptrofs.zero) op vargs m = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_operation op aargs).
Proof.
  unfold eval_operation, eval_static_operation, addx, revsubx, addxl, revsubxl; intros.
  destruct op; InvHyps; eauto with va.
  - destruct (propagate_float_constants tt); constructor.
  - destruct (propagate_float_constants tt); constructor.
  - rewrite Ptrofs.add_zero_l; eauto with va.
  - replace(match Val.shl a1 (Vint (int_of_shift1_4 shift)) with
    | Vint n2 => Vint (Int.add n n2)
    | Vptr b2 ofs2 =>
        if Archi.ptr64
        then Vundef
        else Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int n))
    | _ => Vundef
    end)  with (Val.add (Vint n) (Val.shl a1 (Vint (int_of_shift1_4 shift)))).
    + eauto with va.
    + destruct a1; destruct shift; reflexivity.
  - (*revsubimm*) inv H1; constructor.
  - replace (match Val.shl a1 (Vint (int_of_shift1_4 shift)) with
   | Vint n2 => Vint (Int.sub n n2)
   | _ => Vundef
             end) with (Val.sub (Vint n) (Val.shl a1 (Vint (int_of_shift1_4 shift)))).
    + eauto with va.
    + destruct n; destruct shift; reflexivity.
  - (* shrx *)
    inv H1; simpl; try constructor.
    all: destruct Int.ltu; [simpl | constructor; fail].
    all: auto with va.
  - replace (match Val.shll a1 (Vint (int_of_shift1_4 shift)) with
    | Vlong n2 => Vlong (Int64.add n n2)
    | Vptr b2 ofs2 =>
        if Archi.ptr64
        then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 n))
        else Vundef
    | _ => Vundef
             end) with (Val.addl (Vlong n) (Val.shll a1 (Vint (int_of_shift1_4 shift)))).
    + eauto with va.
    + destruct a1; destruct shift; reflexivity.
  - inv H1; constructor.
  - replace (match Val.shll a1 (Vint (int_of_shift1_4 shift)) with
    | Vlong n2 => Vlong (Int64.sub n n2)
    | _ => Vundef
             end) with (Val.subl (Vlong n) (Val.shll a1 (Vint (int_of_shift1_4 shift)))).
    + eauto with va.
    + destruct a1; destruct shift; reflexivity.
  - (* shrxl *)
    inv H1; simpl; try constructor.
    all: destruct Int.ltu; [simpl | constructor; fail].
    all: auto with va.
  - apply of_optbool_sound. eapply eval_static_condition_sound; eauto.

  (* extfz *)
  - unfold extfz, eval_static_extfz.
    destruct (is_bitfield _ _).
    + inv H1; constructor.
    + constructor.

  (* extfs *)
  - unfold extfs, eval_static_extfs.
    destruct (is_bitfield _ _).
    + inv H1; constructor.
    + constructor.

  (* extfzl *)
  - unfold extfzl, eval_static_extfzl.
    destruct (is_bitfieldl _ _).
    + inv H1; constructor.
    + constructor.

  (* extfsl *)
  - unfold extfsl, eval_static_extfsl.
    destruct (is_bitfieldl _ _).
    + inv H1; constructor.
    + constructor.
      
  (* insf *)
  - unfold insf, eval_static_insf.
    destruct (is_bitfield _ _).
    + inv H1; inv H0; simpl; try constructor; destruct (Int.ltu _ _); simpl; constructor.
    + constructor.
  (* insfl *)
  - unfold insfl, eval_static_insfl.
    destruct (is_bitfieldl _ _).
    + inv H1; inv H0; simpl; try constructor; destruct (Int.ltu _ _); simpl; constructor.
    + constructor.
    (* select *)
  - apply select_sound; auto. eapply eval_static_condition0_sound; eauto.
    (* select imm *)
  - apply select_sound; auto with va. eapply eval_static_condition0_sound; eauto.
    (* select long imm *)
  - apply select_sound; auto with va. eapply eval_static_condition0_sound; eauto.
Qed.

End SOUNDNESS.

