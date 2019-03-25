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

(** Translation from Machblock to K1c assembly language (Asmblock) *)

Require Archi.
Require Import Coqlib Errors.
Require Import AST Integers Floats Memdata.
Require Import Op Locations Machblock Asmblock.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(** The code generation functions take advantage of several
  characteristics of the [Mach] code generated by earlier passes of the
  compiler, mostly that argument and result registers are of the correct
  types.  These properties are true by construction, but it's easier to
  recheck them during code generation and fail if they do not hold. *)

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgenblock.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgenblock.freg_of") end.

(*
(** Decomposition of 32-bit integer constants.  They are split into either
  small signed immediates that fit in 12-bits, or, if they do not fit,
  into a (20-bit hi, 12-bit lo) pair where lo is sign-extended. *)

*)
Inductive immed32 : Type :=
  | Imm32_single (imm: int).

Definition make_immed32 (val: int) := Imm32_single val.

(** Likewise, for 64-bit integer constants. *)
Inductive immed64 : Type :=
  | Imm64_single (imm: int64)
.

(* For now, let's suppose all instructions of K1c can handle 64-bits immediate *)
Definition make_immed64 (val: int64) := Imm64_single val.

Notation "a ::g b" := (cons (A:=instruction) a b) (at level 49, right associativity).
Notation "a ::i b" := (cons (A:=basic) a b) (at level 49, right associativity).
Notation "a ::b lb" := ((bblock_single_inst a) :: lb) (at level 49, right associativity).
Notation "a ++g b" := (app (A:=instruction) a b) (at level 49, right associativity).
Notation "a @@ b" := (app a b) (at level 49, right associativity).

(** Smart constructors for arithmetic operations involving
  a 32-bit or 64-bit integer constant.  Depending on whether the
  constant fits in 12 bits or not, one or several instructions
  are generated as required to perform the operation
  and prepended to the given instruction sequence [k]. *)

Definition loadimm32 (r: ireg) (n: int) :=
  match make_immed32 n with
  | Imm32_single imm => Pmake r imm
  end.

Definition opimm32 (op: arith_name_rrr)
                   (opimm: arith_name_rri32)
                   (rd rs: ireg) (n: int) :=
  match make_immed32 n with
  | Imm32_single imm => opimm rd rs imm
  end.

Definition addimm32 := opimm32 Paddw Paddiw.
Definition mulimm32 := opimm32 Pmulw Pmuliw.
Definition andimm32 := opimm32 Pandw Pandiw.
Definition nandimm32 := opimm32 Pnandw Pnandiw.
Definition orimm32  := opimm32 Porw Poriw.
Definition norimm32 := opimm32 Pnorw Pnoriw.
Definition xorimm32 := opimm32 Pxorw Pxoriw.
Definition nxorimm32 := opimm32 Pnxorw Pnxoriw.
(*
Definition sltimm32 := opimm32 Psltw Psltiw.
Definition sltuimm32 := opimm32 Psltuw Psltiuw.
*)

Definition loadimm64 (r: ireg) (n: int64) :=
  match make_immed64 n with
  | Imm64_single imm => Pmakel r imm
  end.

Definition opimm64 (op: arith_name_rrr)
                   (opimm: arith_name_rri64)
                   (rd rs: ireg) (n: int64) :=
  match make_immed64 n with
  | Imm64_single imm => opimm rd rs imm
end.

Definition addimm64 := opimm64 Paddl Paddil.
Definition mulimm64 := opimm64 Pmull Pmulil.
Definition orimm64  := opimm64 Porl  Poril.
Definition andimm64 := opimm64 Pandl Pandil.
Definition xorimm64 := opimm64 Pxorl  Pxoril.
Definition norimm64  := opimm64 Pnorl  Pnoril.
Definition nandimm64 := opimm64 Pnandl Pnandil.
Definition nxorimm64 := opimm64 Pnxorl  Pnxoril.

(*
Definition sltimm64 := opimm64 Psltl Psltil.
Definition sltuimm64 := opimm64 Psltul Psltiul.
*)

Definition addptrofs (rd rs: ireg) (n: ptrofs) :=
  if Ptrofs.eq_dec n Ptrofs.zero then
    Pmv rd rs
  else
    addimm64 rd rs (Ptrofs.to_int64 n).

(** Translation of conditional branches. *)

Definition transl_comp
    (c: comparison) (s: signedness) (r1 r2: ireg) (lbl: label) (k: code) : list instruction :=
  Pcompw (itest_for_cmp c s) RTMP r1 r2 ::g Pcb BTwnez RTMP lbl ::g k.

Definition transl_compl
    (c: comparison) (s: signedness) (r1 r2: ireg) (lbl: label) (k: code) : list instruction :=
  Pcompl (itest_for_cmp c s) RTMP r1 r2 ::g Pcb BTwnez RTMP lbl ::g k.

Definition select_comp (n: int) (c: comparison) : option comparison :=
  if Int.eq n Int.zero then
    match c with
    | Ceq => Some Ceq
    | Cne => Some Cne
    | _   => None
    end
  else
    None
  .

Definition transl_opt_compuimm
    (n: int) (c: comparison) (r1: ireg) (lbl: label) (k: code) : list instruction :=
  if Int.eq n Int.zero then
    match c with
    | Ceq => Pcbu BTweqz r1 lbl ::g k
    | Cne => Pcbu BTwnez r1 lbl ::g k
    | _ => loadimm32 RTMP n ::g (transl_comp c Unsigned r1 RTMP lbl k)
    end
  else
    loadimm32 RTMP n ::g (transl_comp c Unsigned r1 RTMP lbl k)
  .

(* Definition transl_opt_compuimm
    (n: int) (c: comparison) (r1: ireg) (lbl: label) (k: code) : list instruction :=
  loadimm32 RTMP n ::g (transl_comp c Unsigned r1 RTMP lbl k). *)

(*   match select_comp n c with
  | Some Ceq => Pcbu BTweqz r1 lbl ::g k
  | Some Cne => Pcbu BTwnez r1 lbl ::g k
  | Some _   => nil (* Never happens *)
  | None     => loadimm32 RTMP n ::g (transl_comp c Unsigned r1 RTMP lbl k)
  end
  .
 *)

Definition select_compl (n: int64) (c: comparison) : option comparison :=
  if Int64.eq n Int64.zero then
    match c with
    | Ceq => Some Ceq
    | Cne => Some Cne
    | _   => None
    end
  else
    None
  .

Definition transl_opt_compluimm
    (n: int64) (c: comparison) (r1: ireg) (lbl: label) (k: code) : list instruction :=
  if Int64.eq n Int64.zero then
    match c with
    | Ceq => Pcbu BTdeqz r1 lbl ::g k
    | Cne => Pcbu BTdnez r1 lbl ::g k
    | _ => loadimm64 RTMP n ::g (transl_compl c Unsigned r1 RTMP lbl k)
    end
  else
    loadimm64 RTMP n ::g (transl_compl c Unsigned r1 RTMP lbl k)
  .

Definition transl_comp_float32 (cmp: comparison) (r1 r2: ireg) (lbl: label) (k: code) :=
  match ftest_for_cmp cmp with
  | Normal ft => Pfcompw ft GPR32 r1 r2 ::g Pcb BTwnez GPR32 lbl ::g k
  | Reversed ft => Pfcompw ft GPR32 r2 r1 ::g Pcb BTwnez GPR32 lbl ::g k
  end.

Definition transl_comp_notfloat32 (cmp: comparison) (r1 r2: ireg) (lbl: label) (k: code) :=
  match notftest_for_cmp cmp with
  | Normal ft => Pfcompw ft GPR32 r1 r2 ::g Pcb BTwnez GPR32 lbl ::g k
  | Reversed ft => Pfcompw ft GPR32 r2 r1 ::g Pcb BTwnez GPR32 lbl ::g k
  end.

Definition transl_comp_float64 (cmp: comparison) (r1 r2: ireg) (lbl: label) (k: code) :=
  match ftest_for_cmp cmp with
  | Normal ft => Pfcompl ft GPR32 r1 r2 ::g Pcb BTwnez GPR32 lbl ::g k
  | Reversed ft => Pfcompl ft GPR32 r2 r1 ::g Pcb BTwnez GPR32 lbl ::g k
  end.

Definition transl_comp_notfloat64 (cmp: comparison) (r1 r2: ireg) (lbl: label) (k: code) :=
  match notftest_for_cmp cmp with
  | Normal ft => Pfcompl ft GPR32 r1 r2 ::g Pcb BTwnez GPR32 lbl ::g k
  | Reversed ft => Pfcompl ft GPR32 r2 r1 ::g Pcb BTwnez GPR32 lbl ::g k
  end.

Definition transl_cbranch
    (cond: condition) (args: list mreg) (lbl: label) (k: code) : res (list instruction ) :=
  match cond, args with
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_opt_compuimm n c r1 lbl k)
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_comp c Signed r1 r2 lbl k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_comp c Unsigned r1 r2 lbl k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq n Int.zero then
            Pcb (btest_for_cmpswz c) r1 lbl ::g k
          else
            loadimm32 RTMP n ::g (transl_comp c Signed r1 RTMP lbl k)
         )
  | Ccompluimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_opt_compluimm n c r1 lbl k)
  | Ccompl c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_compl c Signed r1 r2 lbl k)
  | Ccomplu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_compl c Unsigned r1 r2 lbl k)
  | Ccomplimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int64.eq n Int64.zero then
            Pcb (btest_for_cmpsdz c) r1 lbl ::g k
          else
            loadimm64 RTMP n ::g (transl_compl c Signed r1 RTMP lbl k)
         )
  | Ccompf c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_comp_float64 c r1 r2 lbl k)
  | Cnotcompf c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_comp_notfloat64 c r1 r2 lbl k)
  | Ccompfs c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_comp_float32 c r1 r2 lbl k)
  | Cnotcompfs c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_comp_notfloat32 c r1 r2 lbl k)
  | _, _ =>
      Error(msg "Asmgenblock.transl_cbranch")
  end.

(** Translation of a condition operator.  The generated code sets the
  [rd] target register to 0 or 1 depending on the truth value of the
  condition. *)

Definition transl_cond_int32s (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  Pcompw (itest_for_cmp cmp Signed) rd r1 r2 ::i k.

Definition transl_cond_int32u (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  Pcompw (itest_for_cmp cmp Unsigned) rd r1 r2 ::i k.

Definition transl_cond_int64s (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  Pcompl (itest_for_cmp cmp Signed) rd r1 r2 ::i k.

Definition transl_cond_int64u (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  Pcompl (itest_for_cmp cmp Unsigned) rd r1 r2 ::i k.

Definition transl_condimm_int32s (cmp: comparison) (rd r1: ireg) (n: int) (k: bcode) :=
  Pcompiw (itest_for_cmp cmp Signed) rd r1 n ::i k.

Definition transl_condimm_int32u (cmp: comparison) (rd r1: ireg) (n: int) (k: bcode) :=
  Pcompiw (itest_for_cmp cmp Unsigned) rd r1 n ::i k.

Definition transl_condimm_int64s (cmp: comparison) (rd r1: ireg) (n: int64) (k: bcode) :=
  Pcompil (itest_for_cmp cmp Signed) rd r1 n ::i k.

Definition transl_condimm_int64u (cmp: comparison) (rd r1: ireg) (n: int64) (k: bcode) :=
  Pcompil (itest_for_cmp cmp Unsigned) rd r1 n ::i k.


Definition transl_cond_float32 (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  match ftest_for_cmp cmp with
  | Normal ft => Pfcompw ft rd r1 r2 ::i k
  | Reversed ft => Pfcompw ft rd r2 r1 ::i k
  end.

Definition transl_cond_notfloat32 (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  match notftest_for_cmp cmp with
  | Normal ft => Pfcompw ft rd r1 r2 ::i k
  | Reversed ft => Pfcompw ft rd r2 r1 ::i k
  end.

Definition transl_cond_float64 (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  match ftest_for_cmp cmp with
  | Normal ft => Pfcompl ft rd r1 r2 ::i k
  | Reversed ft => Pfcompl ft rd r2 r1 ::i k
  end.

Definition transl_cond_notfloat64 (cmp: comparison) (rd r1 r2: ireg) (k: bcode) :=
  match notftest_for_cmp cmp with
  | Normal ft => Pfcompl ft rd r1 r2 ::i k
  | Reversed ft => Pfcompl ft rd r2 r1 ::i k
  end.

Definition transl_cond_op
           (cond: condition) (rd: ireg) (args: list mreg) (k: bcode) :=
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int32s c rd r1 r2 k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int32u c rd r1 r2 k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int32s c rd r1 n k)
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int32u c rd r1 n k)
  | Ccompl c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int64s c rd r1 r2 k)
  | Ccomplu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_int64u c rd r1 r2 k)
  | Ccomplimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int64s c rd r1 n k)
  | Ccompluimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (transl_condimm_int64u c rd r1 n k)
  | Ccompfs c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_float32 c rd r1 r2 k)
  | Cnotcompfs c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_notfloat32 c rd r1 r2 k)
  | Ccompf c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_float64 c rd r1 r2 k)
  | Cnotcompf c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (transl_cond_notfloat64 c rd r1 r2 k)
  | _, _ =>
      Error(msg "Asmblockgen.transl_cond_op")
end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Definition transl_op
              (op: operation) (args: list mreg) (res: mreg) (k: bcode) :=
  match op, args with
  | Omove, a1 :: nil =>
      match preg_of res, preg_of a1 with
      | IR r, IR a => OK (Pmv r a ::i k)
      |  _  ,  _   => Error(msg "Asmgenblock.transl_op: Omove")
      end
  | Ointconst n, nil =>
      do rd <- ireg_of res;
      OK (loadimm32 rd n ::i k)
  | Olongconst n, nil =>
      do rd <- ireg_of res;
      OK (loadimm64 rd n ::i k)
  | Ofloatconst f, nil =>
      do rd <- freg_of res;
      OK (Pmakef rd f ::i k)
  | Osingleconst f, nil =>
      do rd <- freg_of res;
      OK (Pmakefs rd f ::i k)
  | Oaddrsymbol s ofs, nil =>
      do rd <- ireg_of res;
      OK (if Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)
          then Ploadsymbol s Ptrofs.zero rd ::i addptrofs rd rd ofs ::i k
          else Ploadsymbol s ofs rd ::i k)
  | Oaddrstack n, nil =>
      do rd <- ireg_of res;
      OK (addptrofs rd SP n ::i k)

  | Ocast8signed, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Pslliw rd rs (Int.repr 24) ::i Psraiw rd rd (Int.repr 24) ::i k)
  | Ocast16signed, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Pslliw rd rs (Int.repr 16) ::i Psraiw rd rd (Int.repr 16) ::i k)
  | Oadd, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Paddw rd rs1 rs2 ::i k)
  | Oaddimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (addimm32 rd rs n ::i k)
  | Oneg, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Pnegw rd rs ::i k)
  | Osub, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psubw rd rs1 rs2 ::i k)
  | Omul, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pmulw rd rs1 rs2 ::i k)
  | Omulimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1;
      OK (mulimm32 rd rs1 n ::i k)
  | Omulhs, _ => Error(msg "Asmblockgen.transl_op: Omulhs") (* Normalement pas émis *)
  | Omulhu, _ => Error(msg "Asmblockgen.transl_op: Omulhu") (* Normalement pas émis *)
  | Oand, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pandw rd rs1 rs2 ::i k)
  | Oandimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (andimm32 rd rs n ::i k)
  | Onand, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pnandw rd rs1 rs2 ::i k)
  | Onandimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (nandimm32 rd rs n ::i k)
  | Oor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Porw rd rs1 rs2 ::i k)
  | Onor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pnorw rd rs1 rs2 ::i k)
  | Oorimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (orimm32 rd rs n ::i k)
  | Onorimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (norimm32 rd rs n ::i k)
  | Oxor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pxorw rd rs1 rs2 ::i k)
  | Oxorimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (xorimm32 rd rs n ::i k)
  | Onxor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pnxorw rd rs1 rs2 ::i k)
  | Onxorimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
        OK (nxorimm32 rd rs n ::i k)
  | Onot, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
        OK (xorimm32 rd rs Int.mone ::i k)
  | Oandn, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pandnw rd rs1 rs2 ::i k)
  | Oandnimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Pandniw rd rs n ::i k)
  | Oorn, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pornw rd rs1 rs2 ::i k)
  | Oornimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Porniw rd rs n ::i k)
  | Oshl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psllw rd rs1 rs2 ::i k)
  | Oshlimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Pslliw rd rs n ::i k)
  | Oshr, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psraw rd rs1 rs2 ::i k)
  | Oshrimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Psraiw rd rs n ::i k)
  | Oshru, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psrlw rd rs1 rs2 ::i k)
  | Oshruimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Psrliw rd rs n ::i k)
  | Oshrximm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (if Int.eq n Int.zero then Pmv rd rs ::i k else
          Psraiw RTMP rs (Int.repr 31) ::i
          Psrliw RTMP RTMP (Int.sub Int.iwordsize n) ::i
          Paddw RTMP rs RTMP ::i
          Psraiw rd RTMP n ::i k)
  | Ororimm n, a1 :: nil =>
    do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Proriw rd rs n ::i k)
  | Omadd, a1 :: a2 :: a3 :: nil =>
    assertion (mreg_eq a1 res);
      do r1 <- ireg_of a1;
      do r2 <- ireg_of a2;
      do r3 <- ireg_of a3;
        OK (Pmaddw r1 r2 r3 ::i k)
  | Omaddimm n, a1 :: a2 :: nil =>
    assertion (mreg_eq a1 res);
      do r1 <- ireg_of a1;
      do r2 <- ireg_of a2;
        OK (Pmaddiw r1 r2 n ::i k)
  (* [Omakelong], [Ohighlong]  should not occur *)
  | Olowlong, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Pcvtl2w rd rs ::i k)  
  | Ocast32signed, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Psxwd rd rs ::i k)
  | Ocast32unsigned, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Pzxwd rd rs ::i k)
(*       assertion (ireg_eq rd rs);
      OK (Pcvtw2l rd ::i Psllil rd rd (Int.repr 32) ::i Psrlil rd rd (Int.repr 32) ::i k) *)
  | Oaddl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Paddl rd rs1 rs2 ::i k)
  | Oaddlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (addimm64 rd rs n ::i k)
  | Onegl, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Pnegl rd rs ::i k)
  | Osubl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psubl rd rs1 rs2 ::i k)
  | Omull, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pmull rd rs1 rs2 ::i k)
  | Omullimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1;
      OK (mulimm64 rd rs1 n ::i k)
  | Omullhs, _ => Error (msg "Asmblockgen.transl_op: Omullhs") (* Normalement pas émis *)
  | Omullhu, _ => Error (msg "Asmblockgen.transl_op: Omullhu") (* Normalement pas émis *)
  | Odivl, _ => Error (msg "Asmblockgen.transl_op: Odivl") (* Géré par fonction externe *)
  | Odivlu, _ => Error (msg "Asmblockgen.transl_op: Odivlu") (* Géré par fonction externe *)
  | Omodl, _ => Error (msg "Asmblockgen.transl_op: Omodl") (* Géré par fonction externe *)
  | Omodlu, _ => Error (msg "Asmblockgen.transl_op: Omodlu") (* Géré par fonction externe *)
  | Onotl, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
        OK (xorimm64 rd rs Int64.mone ::i k)
  | Oandl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pandl rd rs1 rs2 ::i k)
  | Oandlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (andimm64 rd rs n ::i k)
  | Onandl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pnandl rd rs1 rs2 ::i k)
  | Onandlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (nandimm64 rd rs n ::i k)
  | Oorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Porl rd rs1 rs2 ::i k)
  | Oorlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (orimm64 rd rs n ::i k)
  | Onorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pnorl rd rs1 rs2 ::i k)
  | Onorlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (norimm64 rd rs n ::i k)
  | Oxorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pxorl rd rs1 rs2 ::i k)
  | Oxorlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (xorimm64 rd rs n ::i k)
  | Onxorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pnxorl rd rs1 rs2 ::i k)
  | Onxorlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (nxorimm64 rd rs n ::i k)
  | Oandnl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pandnl rd rs1 rs2 ::i k)
  | Oandnlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Pandnil rd rs n ::i k)
  | Oornl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pornl rd rs1 rs2 ::i k)
  | Oornlimm n, a1 :: nil =>
      do rd  <- ireg_of res; do rs <- ireg_of a1;
      OK (Pornil rd rs n ::i k)
  | Oshll, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Pslll rd rs1 rs2 ::i k)
  | Oshllimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Psllil rd rs n ::i k)
  | Oshrl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psral rd rs1 rs2 ::i k)
  | Oshrlimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Psrail rd rs n ::i k)
  | Oshrlu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do rs1 <- ireg_of a1; do rs2 <- ireg_of a2;
      OK (Psrll rd rs1 rs2 ::i k)
  | Oshrluimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (Psrlil rd rs n ::i k)
  | Oshrxlimm n, a1 :: nil =>
      do rd <- ireg_of res; do rs <- ireg_of a1;
      OK (if Int.eq n Int.zero then Pmv rd rs ::i k else
          Psrail RTMP rs (Int.repr 63) ::i
          Psrlil RTMP RTMP (Int.sub Int64.iwordsize' n) ::i
          Paddl RTMP rs RTMP ::i
          Psrail rd RTMP n ::i k)
  | Omaddl, a1 :: a2 :: a3 :: nil =>
    assertion (mreg_eq a1 res);
      do r1 <- ireg_of a1;
      do r2 <- ireg_of a2;
      do r3 <- ireg_of a3;
        OK (Pmaddl r1 r2 r3 ::i k)
  | Omaddlimm n, a1 :: a2 :: nil =>
    assertion (mreg_eq a1 res);
      do r1 <- ireg_of a1;
      do r2 <- ireg_of a2;
        OK (Pmaddil r1 r2 n ::i k)
  | Oabsf, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfabsd rd rs ::i k)
  | Oabsfs, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfabsw rd rs ::i k)
  | Oaddf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfaddd rd rs1 rs2 ::i k)
  | Oaddfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfaddw rd rs1 rs2 ::i k)
  | Osubf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfsbfd rd rs1 rs2 ::i k)
  | Osubfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfsbfw rd rs1 rs2 ::i k)
  | Omulf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfmuld rd rs1 rs2 ::i k)
  | Omulfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfmulw rd rs1 rs2 ::i k)
  | Onegf, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfnegd rd rs ::i k)
  | Onegfs, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfnegw rd rs ::i k)

  | Osingleofint, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pfloatwrnsz rd rs ::i k)
  | Osingleofintu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pfloatuwrnsz rd rs ::i k)
  | Ofloatoflong, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pfloatdrnsz rd rs ::i k)
  | Ofloatoflongu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pfloatudrnsz rd rs ::i k)
  | Ofloatofint, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pfloatdrnsz_i32 rd rs ::i k)
  | Ofloatofintu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pfloatudrnsz_i32 rd rs ::i k)
  | Ointofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfixedwrzz rd rs ::i k)
  | Ointuofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfixeduwrzz rd rs ::i k)
  | Olongoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfixeddrzz rd rs ::i k)
  | Ointoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfixeddrzz_i32 rd rs ::i k)
  | Ointuoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfixedudrzz_i32 rd rs ::i k)
  | Olonguoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfixedudrzz rd rs ::i k)

  | Ofloatofsingle, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfwidenlwd rd rs ::i k)
  | Osingleoffloat, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfnarrowdw rd rs ::i k)


  | Odivf , _ => Error (msg "Asmblockgen.transl_op: Odivf")
  | Odivfs, _ => Error (msg "Asmblockgen.transl_op: Odivfs")

  (* We use the Splitlong instead for these four conversions *)
  | Osingleoflong , _ => Error (msg "Asmblockgen.transl_op: Osingleoflong") 
  | Osingleoflongu , _ => Error (msg "Asmblockgen.transl_op: Osingleoflongu")
  | Olongofsingle , _ => Error (msg "Asmblockgen.transl_op: Olongofsingle")
  | Olonguofsingle , _ => Error (msg "Asmblockgen.transl_op: Olonguofsingle")



  | Ocmp cmp, _ =>
      do rd <- ireg_of res;
      transl_cond_op cmp rd args k

  | Oselect, a0 :: a1 :: aS :: nil =>
    assertion (mreg_eq a0 res);
      do r0 <- ireg_of a0;
      do r1 <- ireg_of a1;
      do rS <- ireg_of aS;
        OK (Pcmove BTwnez r0 rS r1 ::i k)

  | _, _ =>
      Error(msg "Asmgenblock.transl_op")
  end.

(** Accessing data in the stack frame. *)

Definition indexed_memory_access
        (mk_instr: ireg -> offset -> basic)
        (base: ireg) (ofs: ptrofs) :=
  match make_immed64 (Ptrofs.to_int64 ofs) with
  | Imm64_single imm =>
      mk_instr base (Ofsimm (Ptrofs.of_int64 imm))
(*| Imm64_pair hi lo =>
      Pluil GPR31 hi :: Paddl GPR31 base GPR31 :: mk_instr GPR31 (Ofsimm (Ptrofs.of_int64 lo)) :: k
  | Imm64_large imm =>
      Pmake GPR31 imm :: Paddl GPR31 base GPR31 :: mk_instr GPR31 (Ofsimm Ptrofs.zero) :: k
*)end.

Definition loadind (base: ireg) (ofs: ptrofs) (ty: typ) (dst: mreg) (k: bcode) :=
  match ty, preg_of dst with
  | Tint,    IR rd => OK (indexed_memory_access (Plw rd) base ofs ::i k)
  | Tlong,   IR rd => OK (indexed_memory_access (Pld rd) base ofs ::i k)
  | Tsingle, IR rd => OK (indexed_memory_access (Pfls rd) base ofs ::i k)
  | Tfloat,  IR rd => OK (indexed_memory_access (Pfld rd) base ofs ::i k)
  | Tany32,  IR rd => OK (indexed_memory_access (Plw_a rd) base ofs ::i k)
  | Tany64,  IR rd => OK (indexed_memory_access (Pld_a rd) base ofs ::i k)
  | _, _           => Error (msg "Asmblockgen.loadind")
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: ptrofs) (ty: typ) (k: bcode) :=
  match ty, preg_of src with
  | Tint,    IR rd => OK (indexed_memory_access (Psw rd) base ofs ::i k)
  | Tlong,   IR rd => OK (indexed_memory_access (Psd rd) base ofs ::i k)
  | Tsingle, IR rd => OK (indexed_memory_access (Pfss rd) base ofs ::i k)
  | Tfloat,  IR rd => OK (indexed_memory_access (Pfsd rd) base ofs ::i k)
  | Tany32,  IR rd => OK (indexed_memory_access (Psw_a rd) base ofs ::i k)
  | Tany64,  IR rd => OK (indexed_memory_access (Psd_a rd) base ofs ::i k)
  | _, _           => Error (msg "Asmblockgen.storeind")
  end.

Definition loadind_ptr (base: ireg) (ofs: ptrofs) (dst: ireg) :=
  indexed_memory_access (Pld dst) base ofs.

Definition storeind_ptr (src: ireg) (base: ireg) (ofs: ptrofs) :=
  indexed_memory_access (Psd src) base ofs.

(** Translation of memory accesses: loads, and stores. *)

Definition transl_memory_access
     (mk_instr: ireg -> offset -> basic)
     (addr: addressing) (args: list mreg) (k: bcode) : res bcode :=
  match addr, args with
  | Aindexed ofs, a1 :: nil =>
      do rs <- ireg_of a1;
      OK (indexed_memory_access mk_instr rs ofs ::i k)
  | Aglobal id ofs, nil =>
      OK (Ploadsymbol id ofs RTMP ::i (mk_instr RTMP (Ofsimm Ptrofs.zero) ::i k))
  | Ainstack ofs, nil =>
      OK (indexed_memory_access mk_instr SP ofs ::i k)
  | _, _ =>
      Error(msg "Asmblockgen.transl_memory_access")
  end.

Definition transl_load (chunk: memory_chunk) (addr: addressing)
           (args: list mreg) (dst: mreg) (k: bcode) : res bcode :=
  match chunk with
  | Mint8signed =>
      do r <- ireg_of dst;
      transl_memory_access (Plb r)  addr args k
  | Mint8unsigned =>
      do r <- ireg_of dst;
      transl_memory_access (Plbu r) addr args k
  | Mint16signed =>
      do r <- ireg_of dst;
      transl_memory_access (Plh r)  addr args k
  | Mint16unsigned =>
      do r <- ireg_of dst;
      transl_memory_access (Plhu r) addr args k
  | Mint32 =>
      do r <- ireg_of dst;
      transl_memory_access (Plw r)  addr args k
  | Mint64 =>
      do r <- ireg_of dst;
      transl_memory_access (Pld r)  addr args k
  | Mfloat32 =>
      do r <- freg_of dst;
      transl_memory_access (Pfls r) addr args k
  | Mfloat64 =>
      do r <- freg_of dst;
      transl_memory_access (Pfld r) addr args k
  | _ =>
      Error (msg "Asmblockgen.transl_load")
  end.

Definition transl_store (chunk: memory_chunk) (addr: addressing)
           (args: list mreg) (src: mreg) (k: bcode) : res bcode :=
  match chunk with
  | Mint8signed | Mint8unsigned =>
      do r <- ireg_of src;
      transl_memory_access (Psb r)  addr args k
  | Mint16signed | Mint16unsigned =>
      do r <- ireg_of src;
      transl_memory_access (Psh r)  addr args k
  | Mint32 =>
      do r <- ireg_of src;
      transl_memory_access (Psw r)  addr args k
  | Mint64 =>
      do r <- ireg_of src;
      transl_memory_access (Psd r)  addr args k
  | Mfloat32 =>
      do r <- freg_of src;
      transl_memory_access (Pfss r) addr args k
  | Mfloat64 =>
      do r <- freg_of src;
      transl_memory_access (Pfsd r) addr args k
  | _ =>
      Error (msg "Asmblockgen.transl_store")
  end.

(** Function epilogue *)

Definition make_epilogue (f: Machblock.function) (k: code) :=
  (loadind_ptr SP f.(fn_retaddr_ofs) GPRA) 
  ::g Pset RA GPRA ::g Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) ::g k.

(** Translation of a Mach instruction. *)

Definition transl_instr_basic (f: Machblock.function) (i: Machblock.basic_inst)
                              (ep: bool) (k: bcode) :=
  match i with
  | MBgetstack ofs ty dst =>
      loadind SP ofs ty dst k
  | MBsetstack src ofs ty =>
      storeind src SP ofs ty k
  | MBgetparam ofs ty dst =>
      (* load via the frame pointer if it is valid *)
      do c <- loadind FP ofs ty dst k;
      OK (if ep then c
                else (loadind_ptr SP f.(fn_link_ofs) FP) ::i c)
  | MBop op args res =>
      transl_op op args res k
  | MBload chunk addr args dst =>
      transl_load chunk addr args dst k
  | MBstore chunk addr args src =>
      transl_store chunk addr args src k
  end.

Definition transl_instr_control (f: Machblock.function) (oi: option Machblock.control_flow_inst)
                                : res code :=
  match oi with
  | None => OK nil
  | Some i =>
    match i with
    | MBcall sig (inl r) =>
        do r1 <- ireg_of r; OK ((Picall r1) ::g nil)
    | MBcall sig (inr symb) =>
        OK ((Pcall symb) ::g nil)
    | MBtailcall sig (inr symb) =>
        OK (make_epilogue f ((Pgoto symb) ::g nil))
    | MBtailcall sig (inl r) =>
        do r1 <- ireg_of r; OK (make_epilogue f ((Pigoto r1) ::g nil))
    | MBbuiltin ef args res =>
        OK (Pbuiltin ef (List.map (map_builtin_arg preg_of) args) (map_builtin_res preg_of res) ::g nil)
    | MBgoto lbl =>
        OK (Pj_l lbl ::g nil)
    | MBcond cond args lbl =>
        transl_cbranch cond args lbl nil
    | MBreturn =>
        OK (make_epilogue f (Pret ::g nil))
      (*OK (make_epilogue f (Pj_r RA f.(Mach.fn_sig) :: k))*) 
    | MBjumptable _ _ =>
        Error (msg "Asmblockgen.transl_instr_control MBjumptable")
    end
  end.

(* TODO - dans l'idée, transl_instr_control renvoie une liste d'instructions sous la forme :
  * transl_instr_control _ _ _ = lb ++ (ctl :: nil), où lb est une liste de basics, ctl est un control_inst

  Il faut arriver à exprimer cet aspect là ; extraire le lb, le rajouter dans le body ; et extraire le ctl
  qu'on met dans le exit
*)

(** Translation of a code sequence *)

Definition fp_is_parent (before: bool) (i: Machblock.basic_inst) : bool :=
  match i with
  | MBsetstack src ofs ty => before
  | MBgetparam ofs ty dst => negb (mreg_eq dst MFP)
  | MBop op args res => before && negb (mreg_eq res MFP)
  | _ => false
  end.

(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)

Fixpoint transl_basic_code (f: Machblock.function) (il: list Machblock.basic_inst) (it1p: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_basic_code f il' (fp_is_parent it1p i1);
      transl_instr_basic f i1 it1p k
  end.

(* (** This is an equivalent definition in continuation-passing style
  that runs in constant stack space. *)

Fixpoint transl_basic_rec (f: Machblock.function) (il: list Machblock.basic_inst)
                          (it1p: bool) (k: bcode -> res bcode) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_basic_rec f il' (fp_is_parent it1p i1)
        (fun c1 => do c2 <- transl_instr_basic f i1 it1p c1; k c2)
  end.

Definition transl_basic_code' (f: Machblock.function) (il: list Machblock.basic_inst) (it1p: bool) :=
  transl_basic_rec f il it1p (fun c => OK c). *)

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

(* Local Obligation Tactic := bblock_auto_correct. *)

(* Program Definition gen_bblock_noctl (hd: list label) (c: list basic) :=
  match c with
  | nil => {| header := hd; body := Pnop::nil; exit := None |}
  | i::c => {| header := hd; body := i::c; exit := None |}
  end.
 *)

(** Can generate two bblocks if the ctl is a PExpand (since the PExpand must be alone in its block) *)
Program Definition gen_bblocks (hd: list label) (c: list basic) (ctl: list instruction) :=
  match (extract_ctl ctl) with
  | None => 
      match c with
      | nil => {| header := hd; body := Pnop::nil; exit := None |} :: nil
      | i::c => {| header := hd; body := ((i::c) ++ extract_basic ctl); exit := None |} :: nil
      end
(* gen_bblock_noctl hd (c ++ (extract_basic ctl)) :: nil *)
  | Some (PExpand (Pbuiltin ef args res)) =>
      match c with
      | nil => {| header := hd; body := nil; exit := Some (PExpand (Pbuiltin ef args res)) |} :: nil
      | _ => {| header := hd; body := c; exit := None |} 
              :: {| header := nil; body := nil; exit := Some (PExpand (Pbuiltin ef args res)) |} :: nil
      end
  | Some ex => {| header := hd; body := (c ++ extract_basic ctl); exit := Some ex |} :: nil
  end
.
Next Obligation.
  apply wf_bblock_refl. constructor.
    left. auto.
    discriminate.
Qed. Next Obligation.
  apply wf_bblock_refl. constructor.
    right. discriminate.
    unfold builtin_alone. intros. pose (H ef args res). rewrite H0 in n. contradiction.
Qed.

Definition transl_block (f: Machblock.function) (fb: Machblock.bblock) (ep: bool) : res (list bblock) :=
  do c <- transl_basic_code f fb.(Machblock.body) ep;
  do ctl <- transl_instr_control f fb.(Machblock.exit);
  OK (gen_bblocks fb.(Machblock.header) c ctl)
.

Fixpoint transl_blocks (f: Machblock.function) (lmb: list Machblock.bblock) (ep: bool) :=
  match lmb with
  | nil => OK nil
  | mb :: lmb => 
      do lb <- transl_block f mb (if Machblock.header mb then ep else false);
      do lb' <- transl_blocks f lmb false;
      OK (lb @@ lb')
  end
.

Definition transl_function (f: Machblock.function) :=
  do lb <- transl_blocks f f.(Machblock.fn_code) true;
  OK (mkfunction f.(Machblock.fn_sig)
        (Pallocframe f.(fn_stacksize) f.(fn_link_ofs) ::b
         Pget GPRA RA ::b
         storeind_ptr GPRA SP f.(fn_retaddr_ofs) ::b lb)).

Definition transf_function (f: Machblock.function) : res Asmblock.function :=
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (size_blocks tf.(fn_blocks))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: Machblock.fundef) : res Asmblock.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Machblock.program) : res Asmblock.program :=
  transform_partial_program transf_fundef p.
