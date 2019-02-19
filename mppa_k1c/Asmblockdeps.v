Require Import Asmblock.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import ImpDep.


Module R<: ResourceNames.

Inductive t_wrap := Reg (r: preg) | Mem.

Definition t := t_wrap.

Lemma eq_dec : forall (x y: t), { x = y } + { x<>y }.
Proof.
  decide equality. decide equality; apply ireg_eq.
Qed.

End R.


Module P<: ImpParam.

Module R := R.

Inductive value_wrap :=
  | Val (v: val)
  | Memstate (m: mem)
.

Definition value := value_wrap.

Inductive op_wrap :=
  | Arith (ai: ar_instruction)
  | Load (li: ld_instruction)
  | Store (si: st_instruction)
.

Definition op := op_wrap.

Definition genv := Genv.t fundef unit.

Definition arith_eval (ge: genv) (ai: ar_instruction) (l: list value) :=
  match ai, l with
  | PArithR n _, [] =>
      match n with
      | Ploadsymbol s ofs => Some (Genv.symbol_address ge s ofs)
      end

  | PArithRR n _ _, [Val v] =>
      match n with
      | Pmv => Some v
      | Pnegw => Some (Val.neg v)
      | Pnegl => Some (Val.negl v)
      | Pcvtl2w => Some (Val.loword v)
      | Psxwd => Some (Val.longofint v)
      | Pzxwd => Some (Val.longofintu v)
      | Pfnegd => Some (Val.negf v)
      | Pfnegw => Some (Val.negfs v)
      | Pfabsd => Some (Val.absf v)
      | Pfabsw => Some (Val.absfs v)
      | Pfnarrowdw => Some (Val.singleoffloat v)
      | Pfwidenlwd => Some (Val.floatofsingle v)
      | Pfloatwrnsz => Some (match Val.singleofint v with Some f => f | _ => Vundef end)
      | Pfloatudrnsz => Some (match Val.floatoflongu v with Some f => f | _ => Vundef end)
      | Pfloatdrnsz => Some (match Val.floatoflong v with Some f => f | _ => Vundef end)
      | Pfixedwrzz => Some (match Val.intofsingle v with Some i => i | _ => Vundef end)
      | Pfixeddrzz => Some (match Val.longoffloat v with Some i => i | _ => Vundef end)
      end

  | PArithRI32 n _ i, [] =>
      match n with
      | Pmake => Some (Vint i)
      end

  | PArithRI64 n _ i, [] =>
      match n with
      | Pmakel => Some (Vlong i)
      end

  | PArithRF32 n _ i, [] =>
      match n with
      | Pmakefs => Some (Vsingle i)
      end

  | PArithRF64 n _ i, [] =>
      match n with
      | Pmakef => Some (Vfloat i)
      end

  | PArithRRR n _ _ _, [Val v1; Val v2; Memstate m] =>
      match n with
      | Pcompw c => Some (compare_int c v1 v2 m)
      | Pcompl c => Some (compare_long c v1 v2 m)
      | _ => None
      end

  | PArithRRR n _ _ _, [Val v1; Val v2] =>
      match n with
      | Paddw  => Some (Val.add  v1 v2)
      | Psubw  => Some (Val.sub  v1 v2)
      | Pmulw  => Some (Val.mul  v1 v2)
      | Pandw  => Some (Val.and  v1 v2)
      | Porw   => Some (Val.or   v1 v2)
      | Pxorw  => Some (Val.xor  v1 v2)
      | Psrlw  => Some (Val.shru v1 v2)
      | Psraw  => Some (Val.shr  v1 v2)
      | Psllw  => Some (Val.shl  v1 v2)

      | Paddl => Some (Val.addl v1 v2)
      | Psubl => Some (Val.subl v1 v2)
      | Pandl => Some (Val.andl v1 v2)
      | Porl  => Some (Val.orl  v1 v2)
      | Pxorl  => Some (Val.xorl  v1 v2)
      | Pmull => Some (Val.mull v1 v2)
      | Pslll => Some (Val.shll v1 v2)
      | Psrll => Some (Val.shrlu v1 v2)
      | Psral => Some (Val.shrl v1 v2)

      | Pfaddd => Some (Val.addf v1 v2)
      | Pfaddw => Some (Val.addfs v1 v2)
      | Pfsbfd => Some (Val.subf v1 v2)
      | Pfsbfw => Some (Val.subfs v1 v2)
      | Pfmuld => Some (Val.mulf v1 v2)
      | Pfmulw => Some (Val.mulfs v1 v2)

      | _ => None
      end

  | PArithRRI32 n _ _ i, [Val v; Memstate m] =>
      match n with
      | Pcompiw c => Some (compare_int c v (Vint i) m)
      | _ => None
      end

  | PArithRRI32 n _ _ i, [Val v] =>
      match n with
      | Paddiw  => Some (Val.add   v (Vint i))
      | Pandiw  => Some (Val.and   v (Vint i))
      | Poriw   => Some (Val.or    v (Vint i))
      | Pxoriw  => Some (Val.xor   v (Vint i))
      | Psraiw  => Some (Val.shr   v (Vint i))
      | Psrliw  => Some (Val.shru  v (Vint i))
      | Pslliw  => Some (Val.shl   v (Vint i))
      | Psllil  => Some (Val.shll  v (Vint i))
      | Psrlil  => Some (Val.shrlu v (Vint i))
      | Psrail  => Some (Val.shrl  v (Vint i))
      | _ => None
      end

  | PArithRRI64 n d s i =>
      match n with
      | Pcompil c => rs#d <- (compare_long c rs#s (Vlong i) m)
      | Paddil  => rs#d <- (Val.addl rs#s (Vlong i))
      | Pandil  => rs#d <- (Val.andl rs#s (Vlong i))
      | Poril   => rs#d <- (Val.orl  rs#s (Vlong i))
      | Pxoril  => rs#d <- (Val.xorl  rs#s (Vlong i))
      end
  end

Definition op_eval (ge: genv) (o: op) (l: list value) :=
  match o with
  | Arith i => arith_eval ge i l
  | Load i => load_eval ge i l
  | Store i => store_eval ge i l
  end.

End P.
