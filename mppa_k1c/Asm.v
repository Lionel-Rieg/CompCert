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

(** * Abstract syntax *)

(** General Purpose registers. *)

Inductive gpreg: Type :=
  | GPR0:  gpreg | GPR1:  gpreg | GPR2:  gpreg | GPR3:  gpreg | GPR4:  gpreg
  | GPR5:  gpreg | GPR6:  gpreg | GPR7:  gpreg | GPR8:  gpreg | GPR9:  gpreg
  | GPR10: gpreg | GPR11: gpreg | GPR12: gpreg | GPR13: gpreg | GPR14: gpreg
  | GPR15: gpreg | GPR16: gpreg | GPR17: gpreg | GPR18: gpreg | GPR19: gpreg
  | GPR20: gpreg | GPR21: gpreg | GPR22: gpreg | GPR23: gpreg | GPR24: gpreg
  | GPR25: gpreg | GPR26: gpreg | GPR27: gpreg | GPR28: gpreg | GPR29: gpreg
  | GPR30: gpreg | GPR31: gpreg | GPR32: gpreg | GPR33: gpreg | GPR34: gpreg
  | GPR35: gpreg | GPR36: gpreg | GPR37: gpreg | GPR38: gpreg | GPR39: gpreg
  | GPR40: gpreg | GPR41: gpreg | GPR42: gpreg | GPR43: gpreg | GPR44: gpreg
  | GPR45: gpreg | GPR46: gpreg | GPR47: gpreg | GPR48: gpreg | GPR49: gpreg
  | GPR50: gpreg | GPR51: gpreg | GPR52: gpreg | GPR53: gpreg | GPR54: gpreg
  | GPR55: gpreg | GPR56: gpreg | GPR57: gpreg | GPR58: gpreg | GPR59: gpreg
  | GPR60: gpreg | GPR61: gpreg | GPR62: gpreg | GPR63: gpreg.

Definition ireg := gpreg.
Definition freg := gpreg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** We model the following registers of the RISC-V architecture. *)

Inductive preg: Type :=
  | IR: gpreg -> preg                   (**r integer registers *)
  | FR: gpreg -> preg                   (**r float registers   *)
  | RA: preg                            (**r return address    *)
  | PC: preg.                           (**r program counter   *)

Coercion IR: gpreg >-> preg.
Coercion FR: gpreg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

Notation "'SP'" := GPR12 (only parsing) : asm.
Notation "'FP'" := GPR10 (only parsing) : asm.
Notation "'RTMP'" := GPR31 (only parsing) : asm.

Inductive btest: Type :=
  | BTdnez                              (**r Double Not Equal to Zero *)
  | BTdeqz                              (**r Double Equal to Zero *)
  | BTdltz                              (**r Double Less Than Zero *)
  | BTdgez                              (**r Double Greater Than or Equal to Zero *)
  | BTdlez                              (**r Double Less Than or Equal to Zero *)
  | BTdgtz                              (**r Double Greater Than Zero *)
(*| BTodd                               (**r Odd (LSB Set) *)
  | BTeven                              (**r Even (LSB Clear) *)
*)| BTwnez                              (**r Word Not Equal to Zero *)
  | BTweqz                              (**r Word Equal to Zero *)
  | BTwltz                              (**r Word Less Than Zero *)
  | BTwgez                              (**r Word Greater Than or Equal to Zero *)
  | BTwlez                              (**r Word Less Than or Equal to Zero *)
  | BTwgtz                              (**r Word Greater Than Zero *)
  .

Inductive itest: Type :=
  | ITne                                (**r Not Equal *)
  | ITeq                                (**r Equal *)
  | ITlt                                (**r Less Than *)
  | ITge                                (**r Greater Than or Equal *)
  | ITle                                (**r Less Than or Equal *)
  | ITgt                                (**r Greater Than *)
  | ITneu                               (**r Unsigned Not Equal *)
  | ITequ                               (**r Unsigned Equal *)
  | ITltu                               (**r Less Than Unsigned *)
  | ITgeu                               (**r Greater Than or Equal Unsigned *)
  | ITleu                               (**r Less Than or Equal Unsigned *)
  | ITgtu                               (**r Greater Than Unsigned *)
  (* Not used yet *)
  | ITall                               (**r All Bits Set in Mask *)
  | ITnall                              (**r Not All Bits Set in Mask *)
  | ITany                               (**r Any Bits Set in Mask *)
  | ITnone                              (**r Not Any Bits Set in Mask *)
  .

(** Offsets for load and store instructions.  An offset is either an
  immediate integer or the low part of a symbol. *)

Inductive offset : Type :=
  | Ofsimm (ofs: ptrofs)
  | Ofslow (id: ident) (ofs: ptrofs).

(** We model a subset of the K1c instruction set. In particular, we do not
  support floats yet.

  Although it is possible to use the 32-bits mode, for now we don't support it.

  We follow a design close to the one used for the Risc-V port: one set of
  pseudo-instructions for 32-bit integer arithmetic, with suffix W, another
  set for 64-bit integer arithmetic, with suffix L.

  When mapping to actual instructions, the OCaml code in TargetPrinter.ml
  throws an error if we are not in 64-bits mode.
*)

Definition label := positive.

(** A note on immediates: there are various constraints on immediate
  operands to K1c instructions.  We do not attempt to capture these
  restrictions in the abstract syntax nor in the semantics.  The
  assembler will emit an error if immediate operands exceed the
  representable range.  Of course, our K1c generator (file
  [Asmgen]) is careful to respect this range. *)

(** Instructions to be expanded *)
Inductive ex_instruction : Type :=
  (* Pseudo-instructions *)
  | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)               (**r deallocate stack frame and restore previous frame *)
  | Plabel  (lbl: label)                            (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the address of a symbol *)
(*| Ploadsymbol_high (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the high part of the address of a symbol *)
  | Ploadli (rd: ireg) (i: int64)                   (**r load an immediate int64 *)
  | Ploadfi (rd: freg) (f: float)                   (**r load an immediate float *)
  | Ploadsi (rd: freg) (f: float32)                 (**r load an immediate single *)
  | Pbtbl   (r: ireg)  (tbl: list label)            (**r N-way branch through a jump table *) *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> ex_instruction   (**r built-in function (pseudo) *)
  (* Instructions not generated by Asmgen (most likely result of AsmExpand) *)
    (* BCU *)
  | Pawait
  | Pbarrier
  | Pdoze
  | Pwfxl (rs1 rs2: ireg)
  | Pwfxm (rs1 rs2: ireg)
  | Pinvaldtlb
  | Pinvalitlb
  | Pprobetlb
  | Preadtlb
  | Psleep
  | Pstop
  | Psyncgroup (rs: ireg)
  | Ptlbwrite

    (* LSU *)
  | Pafda (rd rs1 rs2: ireg)
  | Paldc (rd rs: ireg)
  | Pdinval
  | Pdinvall (rs: ireg)
  | Pdtouchl (rs: ireg)
  | Pdzerol (rs: ireg)
  | Pfence
  | Piinval
  | Piinvals (rs: ireg)
  | Pitouchl (rs: ireg)
  | Plbsu (rd rs: ireg)
  | Plbzu (rd rs: ireg)
  | Pldu (rd rs: ireg)
  | Plhsu (rd rs: ireg)
  | Plhzu (rd rs: ireg)
  | Plwzu (rd rs: ireg)

    (* ALU *)
  | Paddhp (rd rs1 rs2: ireg)
  | Padds (rd rs1 rs2: ireg)
  | Pbwlu (rd rs1 rs2 rs3 rs4 rs5: ireg)
  | Pbwluhp (rd rs1 rs2 rs3: ireg)
  | Pbwluwp (rd rs1 rs2 rs3: ireg)
  | Pcbs (rd rs: ireg)
  | Pcbsdl (rd rs: ireg)
  | Pclz (rd rs: ireg)
  | Pclzw (rd rs: ireg)
  | Pclzd (rd rs: ireg)
  | Pclzdl (rd rs: ireg)
  | Pcmove (rd rs1 rs2 rs3: ireg)
  | Pctz (rd rs: ireg)
  | Pctzw (rd rs: ireg)
  | Pctzd (rd rs: ireg)
  | Pctzdl (rd rs: ireg)
  | Pextfz (rd rs1 rs2 rs3: ireg)
  | Plandhp (rd rs1 rs2 rs3: ireg)
  | Psat (rd rs1 rs2: ireg)
  | Psatd (rd rs1 rs2: ireg)
  | Psbfhp (rd rs1 rs2: ireg)
  | Psbmm8 (rd rs1 rs2: ireg)
  | Psbmmt8 (rd rs1 rs2: ireg)
  | Psllhps (rd rs1 rs2: ireg)
  | Psrahps (rd rs1 rs2: ireg)
  | Pstsu (rd rs1 rs2: ireg)
  | Pstsud (rd rs1 rs2: ireg)
.

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to the [la] assembler pseudo-instruction, which does the right
  thing even if we are in PIC mode.

- [Ploadli rd ival]: load an immediate 64-bit integer into an integer
  register rd.  Expands to a load from an address in the constant data section,
  using the integer register x31 as temporary:
<<
        lui x31, %hi(lbl)
        ld rd, %lo(lbl)(x31)
lbl:
        .quad ival
>>

- [Ploadfi rd fval]: similar to [Ploadli] but loads a double FP constant fval
  into a float register rd.

- [Ploadsi rd fval]: similar to [Ploadli] but loads a singe FP constant fval
  into a float register rd.

- [Pallocframe sz pos]: in the formal semantics, this
  pseudo-instruction allocates a memory block with bounds [0] and
  [sz], stores the value of the stack pointer at offset [pos] in this
  block, and sets the stack pointer to the address of the bottom of
  this block.
  In the printed ASM assembly code, this allocation is:
<<
        mv      x30, sp
        sub     sp,  sp, #sz
        sw      x30, #pos(sp)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.

- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing is just an increment of [sp]:
<<
        add     sp,  sp, #sz
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.

- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        la      x31, table
        add     x31, x31, reg
        jr      x31
table:  .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.

- [Pseq rd rs1 rs2]: since unsigned comparisons have particular
  semantics for pointers, we cannot encode equality directly using
  xor/sub etc, which have only integer semantics.
<<
        xor     rd, rs1, rs2
        sltiu   rd, rd, 1
>>
  The [xor] is omitted if one of [rs1] and [rs2] is [x0].

- [Psne rd rs1 rs2]: similarly for unsigned inequality.
<<
        xor     rd, rs1, rs2
        sltu    rd, x0, rd
>>
*)

(** Control Flow instructions *)
Inductive cf_instruction : Type :=
  | Pget    (rd: ireg) (rs: preg)                   (**r get system register *)
  | Pset    (rd: preg) (rs: ireg)                   (**r set system register *)
  | Pret                                            (**r return *)
  | Pcall   (l: label)                              (**r function call *)
  (* Pgoto is for tailcalls, Pj_l is for jumping to a particular label *)
  | Pgoto   (l: label)                              (**r goto *)
  | Pj_l    (l: label)                              (**r jump to label *)
  (* Conditional branches *)
  | Pcb     (bt: btest) (r: ireg) (l: label)        (**r branch based on btest *)
  | Pcbu    (bt: btest) (r: ireg) (l: label)        (**r branch based on btest with unsigned semantics *)
.

(** Loads **)
Inductive ld_instruction : Type :=
  | Plb     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load byte *)
  | Plbu    (rd: ireg) (ra: ireg) (ofs: offset)     (**r load byte unsigned *)
  | Plh     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load half word *)
  | Plhu    (rd: ireg) (ra: ireg) (ofs: offset)     (**r load half word unsigned *)
  | Plw     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load int32 *)
  | Plw_a   (rd: ireg) (ra: ireg) (ofs: offset)     (**r load any32 *)
  | Pld     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load int64 *)
  | Pld_a   (rd: ireg) (ra: ireg) (ofs: offset)     (**r load any64 *)
  | Pfls    (rd: freg) (ra: ireg) (ofs: offset)     (**r load float *)
  | Pfld     (rd: freg) (ra: ireg) (ofs: offset)    (**r load 64-bit float *)
.

(** Stores **)
Inductive st_instruction : Type :=
  | Psb     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store byte *)
  | Psh     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store half byte *)
  | Psw     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any32 *)
  | Psd     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int64 *)
  | Psd_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any64 *)
  | Pfss    (rs: freg) (ra: ireg) (ofs: offset)     (**r store float *)
  | Pfsd     (rd: freg) (ra: ireg) (ofs: offset)    (**r store 64-bit float *)
.

(** Arithmetic instructions **)
Inductive arith_name_r : Type :=
  | Pcvtw2l                                         (**r Convert Word to Long *)
.

Inductive arith_name_rr : Type :=
  | Pmv                                             (**r register move *)
  | Pnegw                                           (**r negate word *)
  | Pnegl                                           (**r negate long *)
  | Pfnegd                                          (**r float negate double *)
  | Pcvtl2w                                         (**r Convert Long to Word *)
  | Pmvw2l                                          (**r Move Convert Word to Long *)
.

Inductive arith_name_ri32 : Type :=
  | Pmake                                           (**r load immediate *)
.

Inductive arith_name_ri64 : Type :=
  | Pmakel                                          (**r load immediate long *)
.

Inductive arith_name_rrr : Type :=
  | Pcompw  (it: itest)                             (**r comparison word *)
  | Pcompl  (it: itest)                             (**r comparison long *)

  | Paddw                                           (**r add word *)
  | Psubw                                           (**r sub word *)
  | Pmulw                                           (**r mul word *)
  | Pandw                                           (**r and word *)
  | Porw                                            (**r or word *)
  | Pxorw                                           (**r xor word *)
  | Psraw                                           (**r shift right arithmetic word *)
  | Psrlw                                           (**r shift right logical word *)
  | Psllw                                           (**r shift left logical word *)

  | Paddl                                           (**r add long *)
  | Psubl                                           (**r sub long *)
  | Pandl                                           (**r and long *)
  | Porl                                            (**r or long *)
  | Pxorl                                           (**r xor long *)
  | Pmull                                           (**r mul long (low part) *)
  | Pslll                                           (**r shift left logical long *)
  | Psrll                                           (**r shift right logical long *)
  | Psral                                           (**r shift right arithmetic long *)
.

Inductive arith_name_rri32 : Type :=
  | Pcompiw (it: itest)                             (**r comparison imm word *)

  | Paddiw                                          (**r add imm word *)
  | Pandiw                                          (**r and imm word *)
  | Poriw                                           (**r or imm word *)
  | Pxoriw                                          (**r xor imm word *)
  | Psraiw                                          (**r shift right arithmetic imm word *)
  | Psrliw                                          (**r shift right logical imm word *)
  | Pslliw                                          (**r shift left logical imm word *)

  | Psllil                                          (**r shift left logical immediate long *)
  | Psrlil                                          (**r shift right logical immediate long *)
  | Psrail                                          (**r shift right arithmetic immediate long *)
.

Inductive arith_name_rri64 : Type :=
  | Pcompil (it: itest)                             (**r comparison imm long *)
  | Paddil                                          (**r add immediate long *) 
  | Pandil                                          (**r and immediate long *) 
  | Poril                                           (**r or immediate long *) 
  | Pxoril                                          (**r xor immediate long *) 
.

Inductive ar_instruction : Type :=
  | PArithR     (i: arith_name_r)     (rd: ireg)
  | PArithRR    (i: arith_name_rr)    (rd rs: ireg)
  | PArithRI32  (i: arith_name_ri32)  (rd: ireg) (imm: int)
  | PArithRI64  (i: arith_name_ri64)  (rd: ireg) (imm: int64)
  | PArithRRR   (i: arith_name_rrr)   (rd rs1 rs2: ireg)
  | PArithRRI32 (i: arith_name_rri32) (rd rs: ireg) (imm: int)
  | PArithRRI64 (i: arith_name_rri64) (rd rs: ireg) (imm: int64)
.

Coercion PArithR:       arith_name_r        >-> Funclass.
Coercion PArithRR:      arith_name_rr       >-> Funclass.
Coercion PArithRI32:    arith_name_ri32     >-> Funclass.
Coercion PArithRI64:    arith_name_ri64     >-> Funclass.
Coercion PArithRRR:     arith_name_rrr      >-> Funclass.
Coercion PArithRRI32:   arith_name_rri32    >-> Funclass.
Coercion PArithRRI64:   arith_name_rri64    >-> Funclass.

(*| Pfence                                          (**r fence *)

  (* floating point register move *)
  | Pfmv     (rd: freg) (rs: freg)                  (**r move *)
  | Pfmvxs   (rd: ireg) (rs: freg)                  (**r move FP single to integer register *)
  | Pfmvxd   (rd: ireg) (rs: freg)                  (**r move FP double to integer register *)

*)(* 32-bit (single-precision) floating point *)

(*| Pfnegs   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabss   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfadds   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubs   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuls   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivs   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmins   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxs   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqs    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pflts    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfles    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrts  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmadds  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubs  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmadds (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubs (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtws  (rd: ireg) (rs: freg)                  (**r float32 -> int32 conversion *)
  | Pfcvtwus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int32 conversion *)
  | Pfcvtsw  (rd: freg) (rs: ireg)                 (**r int32 -> float32 conversion *)
  | Pfcvtswu (rd: freg) (rs: ireg)                 (**r unsigned int32 -> float32 conversion *)

  | Pfcvtls  (rd: ireg) (rs: freg)                  (**r float32 -> int64 conversion *)
  | Pfcvtlus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int64 conversion *)
  | Pfcvtsl  (rd: freg) (rs: ireg)                 (**r int64 -> float32 conversion *)
  | Pfcvtslu (rd: freg) (rs: ireg)                 (**r unsigned int 64-> float32 conversion *)

*)(* 64-bit (double-precision) floating point *)
(*| Pfld_a   (rd: freg) (ra: ireg) (ofs: offset)    (**r load any64 *)
  | Pfsd_a   (rd: freg) (ra: ireg) (ofs: offset)    (**r store any64 *)

  | Pfabsd   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfaddd   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubd   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuld   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivd   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmind   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxd   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqd    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pfltd    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfled    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrtd  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmaddd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmaddd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtwd  (rd: ireg) (rs: freg)                  (**r float -> int32 conversion *)
  | Pfcvtwud (rd: ireg) (rs: freg)                  (**r float -> unsigned int32 conversion *)
  | Pfcvtdw  (rd: freg) (rs: ireg)                 (**r int32 -> float conversion *)
  | Pfcvtdwu (rd: freg) (rs: ireg)                 (**r unsigned int32 -> float conversion *)

  | Pfcvtld  (rd: ireg) (rs: freg)                  (**r float -> int64 conversion *)
  | Pfcvtlud (rd: ireg) (rs: freg)                  (**r float -> unsigned int64 conversion *)
  | Pfcvtdl  (rd: freg) (rs: ireg)                 (**r int64 -> float conversion *)
  | Pfcvtdlu (rd: freg) (rs: ireg)                 (**r unsigned int64 -> float conversion *)

  | Pfcvtds  (rd: freg) (rs: freg)                  (**r float32 -> float   *)
  | Pfcvtsd  (rd: freg) (rs: freg)                  (**r float   -> float32 *)
*)

Inductive instruction : Type :=
  | PExpand         (i: ex_instruction)
  | PControlFlow    (i: cf_instruction)
  | PLoad           (i: ld_instruction)
  | PStore          (i: st_instruction)
  | PArith          (i: ar_instruction)
.

Coercion PExpand:       ex_instruction >-> instruction.
Coercion PControlFlow:  cf_instruction >-> instruction.
Coercion PLoad:         ld_instruction >-> instruction.
Coercion PStore:        st_instruction >-> instruction.
Coercion PArith:        ar_instruction >-> instruction.

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain
  the convention that integer registers are mapped to values of
  type [Tint] or [Tlong] (in 64 bit mode),
  and float registers to values of type [Tsingle] or [Tfloat]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Definition getw (rs: regset) (r: ireg) : val :=
  match r with
  | _ => rs r
  end.

Definition getl (rs: regset) (r: ireg) : val :=
  match r with
  | _ => rs r
  end.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a ## b" := (getw a b) (at level 1) : asm.
Notation "a ### b" := (getl a b) (at level 1) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  destruct i; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset)] and splits their
  actual values into a 20-bit high part [%hi(symbol + offset)] and 
  a 12-bit low part [%lo(symbol + offset)]. *)

Parameter low_half: genv -> ident -> ptrofs -> ptrofs.
Parameter high_half: genv -> ident -> ptrofs -> val.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)

Definition eval_offset (ofs: offset) : ptrofs :=
  match ofs with
  | Ofsimm n => n
  | Ofslow id delta => low_half ge id delta
  end.

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: preg) (a: ireg) (ofs: offset) :=
  match Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#d <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: preg) (a: ireg) (ofs: offset) :=
  match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) (rs s) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

Inductive signedness: Type := Signed | Unsigned.

Inductive intsize: Type := Int | Long.

Definition itest_for_cmp (c: comparison) (s: signedness) :=
  match c, s with
  | Cne, Signed => ITne
  | Ceq, Signed => ITeq
  | Clt, Signed => ITlt
  | Cge, Signed => ITge
  | Cle, Signed => ITle
  | Cgt, Signed => ITgt
  | Cne, Unsigned => ITneu
  | Ceq, Unsigned => ITequ
  | Clt, Unsigned => ITltu
  | Cge, Unsigned => ITgeu
  | Cle, Unsigned => ITleu
  | Cgt, Unsigned => ITgtu
  end.

(* CoMPare Signed Words to Zero *)
Definition btest_for_cmpswz (c: comparison) :=
  match c with
  | Cne => BTwnez
  | Ceq => BTweqz
  | Clt => BTwltz
  | Cge => BTwgez
  | Cle => BTwlez
  | Cgt => BTwgtz
  end.

(* CoMPare Signed Doubles to Zero *)
Definition btest_for_cmpsdz (c: comparison) :=
  match c with
  | Cne => BTdnez
  | Ceq => BTdeqz
  | Clt => BTdltz
  | Cge => BTdgez
  | Cle => BTdlez
  | Cgt => BTdgtz
  end.

Definition cmp_for_btest (bt: btest) :=
  match bt with
  | BTwnez => (Some Cne, Int)
  | BTweqz => (Some Ceq, Int)
  | BTwltz => (Some Clt, Int)
  | BTwgez => (Some Cge, Int)
  | BTwlez => (Some Cle, Int)
  | BTwgtz => (Some Cgt, Int)

  | BTdnez => (Some Cne, Long)
  | BTdeqz => (Some Ceq, Long)
  | BTdltz => (Some Clt, Long)
  | BTdgez => (Some Cge, Long)
  | BTdlez => (Some Cle, Long)
  | BTdgtz => (Some Cgt, Long)
  end.

Definition cmpu_for_btest (bt: btest) :=
  match bt with
  | BTwnez => (Some Cne, Int)
  | BTweqz => (Some Ceq, Int)
  | BTdnez => (Some Cne, Long)
  | BTdeqz => (Some Ceq, Long)
  | _ => (None, Int)
  end.

(** Comparing integers *)
Definition compare_int (t: itest) (v1 v2: val) (m: mem): val :=
  match t with
  | ITne  => Val.cmp Cne v1 v2
  | ITeq  => Val.cmp Ceq v1 v2
  | ITlt  => Val.cmp Clt v1 v2
  | ITge  => Val.cmp Cge v1 v2
  | ITle  => Val.cmp Cle v1 v2
  | ITgt  => Val.cmp Cgt v1 v2
  | ITneu => Val.cmpu (Mem.valid_pointer m) Cne v1 v2
  | ITequ => Val.cmpu (Mem.valid_pointer m) Ceq v1 v2
  | ITltu => Val.cmpu (Mem.valid_pointer m) Clt v1 v2
  | ITgeu => Val.cmpu (Mem.valid_pointer m) Cge v1 v2
  | ITleu => Val.cmpu (Mem.valid_pointer m) Cle v1 v2
  | ITgtu => Val.cmpu (Mem.valid_pointer m) Cgt v1 v2
  | ITall
  | ITnall
  | ITany
  | ITnone => Vundef
  end.

Definition compare_long (t: itest) (v1 v2: val) (m: mem): val :=
  let res := match t with
  | ITne  => Val.cmpl Cne v1 v2
  | ITeq  => Val.cmpl Ceq v1 v2
  | ITlt  => Val.cmpl Clt v1 v2
  | ITge  => Val.cmpl Cge v1 v2
  | ITle  => Val.cmpl Cle v1 v2
  | ITgt  => Val.cmpl Cgt v1 v2
  | ITneu => Val.cmplu (Mem.valid_pointer m) Cne v1 v2
  | ITequ => Val.cmplu (Mem.valid_pointer m) Ceq v1 v2
  | ITltu => Val.cmplu (Mem.valid_pointer m) Clt v1 v2
  | ITgeu => Val.cmplu (Mem.valid_pointer m) Cge v1 v2
  | ITleu => Val.cmplu (Mem.valid_pointer m) Cle v1 v2
  | ITgtu => Val.cmplu (Mem.valid_pointer m) Cgt v1 v2
  | ITall
  | ITnall
  | ITany
  | ITnone => Some Vundef
  end in 
  match res with
  | Some v => v
  | None => Vundef
  end
  .

(** Execution of a single instruction [i] in initial state [rs] and
    [m].  Return updated state.  For instructions that correspond to
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
(** Get/Set system registers *)
  match i with
  | Pget rd ra =>
    match ra with
    | RA => Next (nextinstr (rs#rd <- (rs#ra))) m
    | _  => Stuck
    end
  | Pset ra rd =>
    match ra with
    | RA => Next (nextinstr (rs#ra <- (rs#rd))) m
    | _  => Stuck
    end

(** Branch Control Unit instructions *)
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  | Pcall s =>
      Next (rs#RA <- (Val.offset_ptr (rs#PC) Ptrofs.one)#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pgoto s =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pj_l l =>
      goto_label f l rs m
  | Pcb bt r l =>
      match cmp_for_btest bt with
      | (Some c, Int)  => eval_branch f l rs m (Val.cmp_bool c rs##r (Vint (Int.repr 0)))
      | (Some c, Long) => eval_branch f l rs m (Val.cmpl_bool c rs###r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end
  | Pcbu bt r l => 
      match cmpu_for_btest bt with
      | (Some c, Int) => eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) c rs##r (Vint (Int.repr 0)))
      | (Some c, Long) => eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) c rs###r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end

(** Arithmetic Instructions *)
  | PArithR n d =>
      match n with
      | Pcvtw2l => Next (nextinstr (rs#d <- (Val.longofint rs#d))) m
      end
  
  | PArithRR n d s =>
      match n with
      | Pmv => Next (nextinstr (rs#d <- (rs#s))) m
      | Pnegw => Next (nextinstr (rs#d <- (Val.neg rs###s))) m
      | Pnegl => Next (nextinstr (rs#d <- (Val.negl rs###s))) m
      | Pfnegd => Next (nextinstr (rs#d <- (Val.negf rs#s))) m
      | Pcvtl2w => Next (nextinstr (rs#d <- (Val.loword rs###s))) m
      | Pmvw2l => Next (nextinstr (rs#d <- (Val.longofint rs#s))) m
      end

  | PArithRI32 n d i =>
      match n with
      | Pmake => Next (nextinstr (rs#d <- (Vint i))) m
      end

  | PArithRI64 n d i =>
      match n with
      | Pmakel => Next (nextinstr (rs#d <- (Vlong i))) m
      end

  | PArithRRR n d s1 s2 =>
      match n with
      | Pcompw c => Next (nextinstr (rs#d <- (compare_int c rs##s1 rs##s2 m))) m
      | Pcompl c => Next (nextinstr (rs#d <- (compare_long c rs###s1 rs###s2 m))) m
      | Paddw  => Next (nextinstr (rs#d <- (Val.add  rs##s1 rs##s2))) m
      | Psubw  => Next (nextinstr (rs#d <- (Val.sub  rs##s1 rs##s2))) m
      | Pmulw  => Next (nextinstr (rs#d <- (Val.mul  rs##s1 rs##s2))) m
      | Pandw  => Next (nextinstr (rs#d <- (Val.and  rs##s1 rs##s2))) m
      | Porw   => Next (nextinstr (rs#d <- (Val.or   rs##s1 rs##s2))) m
      | Pxorw  => Next (nextinstr (rs#d <- (Val.xor  rs##s1 rs##s2))) m
      | Psrlw  => Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m
      | Psraw  => Next (nextinstr (rs#d <- (Val.shr  rs##s1 rs##s2))) m
      | Psllw  => Next (nextinstr (rs#d <- (Val.shl  rs##s1 rs##s2))) m

      | Paddl => Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m
      | Psubl => Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m
      | Pandl => Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m
      | Porl  => Next (nextinstr (rs#d <- (Val.orl  rs###s1 rs###s2))) m
      | Pxorl  => Next (nextinstr (rs#d <- (Val.xorl  rs###s1 rs###s2))) m
      | Pmull => Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m
      | Pslll => Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m
      | Psrll => Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m
      | Psral => Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m
      end

  | PArithRRI32 n d s i =>
      match n with
      | Pcompiw c => Next (nextinstr (rs#d <- (compare_int c rs##s (Vint i) m))) m
      | Paddiw  => Next (nextinstr (rs#d <- (Val.add   rs##s (Vint i)))) m
      | Pandiw  => Next (nextinstr (rs#d <- (Val.and   rs##s (Vint i)))) m
      | Poriw   => Next (nextinstr (rs#d <- (Val.or    rs##s (Vint i)))) m
      | Pxoriw  => Next (nextinstr (rs#d <- (Val.xor   rs##s (Vint i)))) m
      | Psraiw  => Next (nextinstr (rs#d <- (Val.shr   rs##s (Vint i)))) m
      | Psrliw  => Next (nextinstr (rs#d <- (Val.shru  rs##s (Vint i)))) m
      | Pslliw  => Next (nextinstr (rs#d <- (Val.shl   rs##s (Vint i)))) m

      | Psllil  => Next (nextinstr (rs#d <- (Val.shll  rs###s (Vint i)))) m
      | Psrlil  => Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m
      | Psrail  => Next (nextinstr (rs#d <- (Val.shrl  rs###s (Vint i)))) m
      end

  | PArithRRI64 n d s i =>
      match n with
      | Pcompil c => Next (nextinstr (rs#d <- (compare_long c rs###s (Vlong i) m))) m
      | Paddil  => Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m
      | Pandil  => Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m
      | Poril   => Next (nextinstr (rs#d <- (Val.orl  rs###s (Vlong i)))) m
      | Pxoril  => Next (nextinstr (rs#d <- (Val.xorl  rs###s (Vlong i)))) m
      end

(** Loads and stores *)
  | Plb d a ofs =>
      exec_load Mint8signed rs m d a ofs
  | Plbu d a ofs =>
      exec_load Mint8unsigned rs m d a ofs
  | Plh d a ofs =>
      exec_load Mint16signed rs m d a ofs
  | Plhu d a ofs =>
      exec_load Mint16unsigned rs m d a ofs
  | Plw d a ofs =>
      exec_load Mint32 rs m d a ofs
  | Plw_a d a ofs =>
      exec_load Many32 rs m d a ofs
  | Pld d a ofs =>
      exec_load Mint64 rs m d a ofs
  | Pld_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Psb s a ofs =>
      exec_store Mint8unsigned rs m s a ofs
  | Psh s a ofs =>
      exec_store Mint16unsigned rs m s a ofs
  | Psw s a ofs =>
      exec_store Mint32 rs m s a ofs
  | Psw_a s a ofs =>
      exec_store Many32 rs m s a ofs
  | Psd s a ofs =>
      exec_store Mint64 rs m s a ofs
  | Psd_a s a ofs =>
      exec_store Many64 rs m s a ofs

(** Floating point register move *)
(*| Pfmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit (single-precision) floating point *)
*)| Pfls d a ofs =>
      exec_load Mfloat32 rs m d a ofs
  | Pfss s a ofs =>
      exec_store Mfloat32 rs m s a ofs

(*| Pfnegs d s =>
      Next (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfabss d s =>
      Next (nextinstr (rs#d <- (Val.absfs rs#s))) m

  | Pfadds d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfeqs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m

  | Pfcvtws d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtwus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m
  | Pfcvtsw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m
  | Pfcvtswu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m

  | Pfcvtls d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m
  | Pfcvtlus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m
  | Pfcvtsl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m
  | Pfcvtslu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m

(** 64-bit (double-precision) floating point *)
*)| Pfld d a ofs =>
      exec_load Mfloat64 rs m d a ofs
(*| Pfld_a d a ofs =>
      exec_load Many64 rs m d a ofs
*)| Pfsd s a ofs =>
      exec_store Mfloat64 rs m s a ofs
(*| Pfsd_a s a ofs =>
      exec_store Many64 rs m s a ofs

  | Pfabsd d s =>
      Next (nextinstr (rs#d <- (Val.absf rs#s))) m

  | Pfaddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

  | Pfcvtwd d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtwud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m
  | Pfcvtdw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m
  | Pfcvtdwu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m

  | Pfcvtld d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m
  | Pfcvtlud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuoffloat rs#s)))) m
  | Pfcvtdl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m
  | Pfcvtdlu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m

  | Pfcvtds d s =>
      Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtsd d s =>
      Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m

(** Pseudo-instructions *)
*)| Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #FP <- (rs SP) #SP <- sp #GPR31 <- Vundef)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v #GPR31 <- Vundef)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd s ofs =>
      Next (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m
(*| Ploadsymbol_high rd s ofs =>
      Next (nextinstr (rs#rd <- (high_half ge s ofs))) m
  | Ploadli rd i =>
      Next (nextinstr (rs#GPR31 <- Vundef #rd <- (Vlong i))) m
  | Ploadfi rd f =>
      Next (nextinstr (rs#GPR31 <- Vundef #rd <- (Vfloat f))) m
  | Ploadsi rd f =>
      Next (nextinstr (rs#GPR31 <- Vundef #rd <- (Vsingle f))) m
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#GPR5 <- Vundef #GPR31 <- Vundef) m
          end
      | _ => Stuck
      end
*)| Pbuiltin ef args res =>
      Stuck (**r treated specially below *)

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
    (* BCU *)
  | Pawait
  | Pbarrier
  | Pdoze
  | Pwfxl _ _
  | Pwfxm _ _
  | Pinvaldtlb
  | Pinvalitlb
  | Pprobetlb
  | Preadtlb
  | Psleep
  | Pstop
  | Psyncgroup _
  | Ptlbwrite

    (* LSU *)
  | Pafda _ _ _
  | Paldc _ _
  | Pdinval
  | Pdinvall _
  | Pdtouchl _
  | Pdzerol _
  | Pfence
  | Piinval
  | Piinvals _
  | Pitouchl _
  | Plbsu _ _
  | Plbzu _ _
  | Pldu _ _
  | Plhsu _ _
  | Plhzu _ _
  | Plwzu _ _

    (* ALU *)
  | Paddhp _ _ _
  | Padds _ _ _
  | Pbwlu _ _ _ _ _ _
  | Pbwluhp _ _ _ _
  | Pbwluwp _ _ _ _
  | Pcbs _ _
  | Pcbsdl _ _
  | Pclz _ _
  | Pclzw _ _
  | Pclzd _ _
  | Pclzdl _ _
  | Pcmove _ _ _ _
  | Pctz _ _
  | Pctzw _ _
  | Pctzd _ _
  | Pctzdl _ _
  | Pextfz _ _ _ _
  | Plandhp _ _ _ _
  | Psat _ _ _
  | Psatd _ _ _
  | Psbfhp _ _ _
  | Psbmm8 _ _ _
  | Psbmmt8 _ _ _
  | Psllhps _ _ _
  | Psrahps _ _ _
  | Pstsu _ _ _
  | Pstsud _ _ _

    => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [X31].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)

  (* FIXME - R31 is not there *)
Definition preg_of (r: mreg) : preg :=
  match r with
  | R0  => GPR0  | R1  => GPR1  | R2  => GPR2  | R3  => GPR3  | R4  => GPR4
  | R5  => GPR5  | R6  => GPR6  | R7  => GPR7                 | R9  => GPR9
  | R10 => GPR10 (*| R11 => GPR11 | R12 => GPR12 | R13 => GPR13 | R14  => GPR14 *)
  | R15 => GPR15 | R16 => GPR16 | R17 => GPR17 | R18 => GPR18 | R19  => GPR19
  | R20 => GPR20 | R21 => GPR21 | R22 => GPR22 | R23 => GPR23 | R24  => GPR24
  | R25 => GPR25 | R26 => GPR26 | R27 => GPR27 | R28 => GPR28 | R29  => GPR29
  | R30 => GPR30 |                R32 => GPR32 | R33 => GPR33 | R34  => GPR34
  | R35 => GPR35 | R36 => GPR36 | R37 => GPR37 | R38 => GPR38 | R39  => GPR39
  | R40 => GPR40 | R41 => GPR41 | R42 => GPR42 | R43 => GPR43 | R44  => GPR44
  | R45 => GPR45 | R46 => GPR46 | R47 => GPR47 | R48 => GPR48 | R49  => GPR49
  | R50 => GPR50 | R51 => GPR51 | R52 => GPR52 | R53 => GPR53 | R54  => GPR54
  | R55 => GPR55 | R56 => GPR56 | R57 => GPR57 | R58 => GPR58 | R59  => GPR59
  | R60 => GPR60 | R61 => GPR61 | R62 => GPR62 | R63 => GPR63
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use RISC-V registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (A:=instruction) (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs#GPR31 <- Vundef))) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res rs)#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs GPR0 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

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
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
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

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | RA  => false
  | IR GPR31 => false
  | IR GPR8 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.
