(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           Xavier Leroy       INRIA Paris-Rocquencourt       *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

(** Abstract syntax and semantics for VLIW semantics of KVX assembly language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import ExtValues.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.
Require Import Errors.
Require Import Sorting.Permutation.
Require Import Chunks.

(** * Abstract syntax *)

(** A KVX program is syntactically given as a list of functions. 
    Each function is associated to a list of bundles of type [bblock] below.
    Hence, syntactically, we view each bundle as a basic block:
    this view induces our sequential semantics of bundles defined in [Asmblock].
*)

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

Lemma gpreg_eq: forall (x y: gpreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive gpreg_q : Type :=
| R0R1 | R2R3 | R4R5 | R6R7 | R8R9
| R10R11 | R12R13 | R14R15 | R16R17 | R18R19
| R20R21 | R22R23 | R24R25 | R26R27 | R28R29
| R30R31 | R32R33 | R34R35 | R36R37 | R38R39
| R40R41 | R42R43 | R44R45 | R46R47 | R48R49
| R50R51 | R52R53 | R54R55 | R56R57 | R58R59
| R60R61 | R62R63.
                             
Lemma gpreg_q_eq : forall (x y : gpreg_q), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition gpreg_q_expand (x : gpreg_q) : gpreg * gpreg :=
  match x with
  | R0R1 => (GPR0, GPR1)
  | R2R3 => (GPR2, GPR3)
  | R4R5 => (GPR4, GPR5)
  | R6R7 => (GPR6, GPR7)
  | R8R9 => (GPR8, GPR9)
  | R10R11 => (GPR10, GPR11)
  | R12R13 => (GPR12, GPR13)
  | R14R15 => (GPR14, GPR15)
  | R16R17 => (GPR16, GPR17)
  | R18R19 => (GPR18, GPR19)
  | R20R21 => (GPR20, GPR21)
  | R22R23 => (GPR22, GPR23)
  | R24R25 => (GPR24, GPR25)
  | R26R27 => (GPR26, GPR27)
  | R28R29 => (GPR28, GPR29)
  | R30R31 => (GPR30, GPR31)
  | R32R33 => (GPR32, GPR33)
  | R34R35 => (GPR34, GPR35)
  | R36R37 => (GPR36, GPR37)
  | R38R39 => (GPR38, GPR39)
  | R40R41 => (GPR40, GPR41)
  | R42R43 => (GPR42, GPR43)
  | R44R45 => (GPR44, GPR45)
  | R46R47 => (GPR46, GPR47)
  | R48R49 => (GPR48, GPR49)
  | R50R51 => (GPR50, GPR51)
  | R52R53 => (GPR52, GPR53)
  | R54R55 => (GPR54, GPR55)
  | R56R57 => (GPR56, GPR57)
  | R58R59 => (GPR58, GPR59)
  | R60R61 => (GPR60, GPR61)
  | R62R63 => (GPR62, GPR63)
  end.

Inductive gpreg_o : Type :=
| R0R1R2R3 | R4R5R6R7 | R8R9R10R11 | R12R13R14R15
| R16R17R18R19 | R20R21R22R23 | R24R25R26R27 | R28R29R30R31
| R32R33R34R35 | R36R37R38R39 | R40R41R42R43 | R44R45R46R47
| R48R49R50R51 | R52R53R54R55 | R56R57R58R59 | R60R61R62R63.

Definition gpreg_o_expand (x : gpreg_o) : gpreg * gpreg * gpreg * gpreg :=
  match x with
  | R0R1R2R3 => (GPR0, GPR1, GPR2, GPR3)
  | R4R5R6R7 => (GPR4, GPR5, GPR6, GPR7)
  | R8R9R10R11 => (GPR8, GPR9, GPR10, GPR11)
  | R12R13R14R15 => (GPR12, GPR13, GPR14, GPR15)
  | R16R17R18R19 => (GPR16, GPR17, GPR18, GPR19)
  | R20R21R22R23 => (GPR20, GPR21, GPR22, GPR23)
  | R24R25R26R27 => (GPR24, GPR25, GPR26, GPR27)
  | R28R29R30R31 => (GPR28, GPR29, GPR30, GPR31)
  | R32R33R34R35 => (GPR32, GPR33, GPR34, GPR35)
  | R36R37R38R39 => (GPR36, GPR37, GPR38, GPR39)
  | R40R41R42R43 => (GPR40, GPR41, GPR42, GPR43)
  | R44R45R46R47 => (GPR44, GPR45, GPR46, GPR47)
  | R48R49R50R51 => (GPR48, GPR49, GPR50, GPR51)
  | R52R53R54R55 => (GPR52, GPR53, GPR54, GPR55)
  | R56R57R58R59 => (GPR56, GPR57, GPR58, GPR59)
  | R60R61R62R63 => (GPR60, GPR61, GPR62, GPR63)
  end.

Lemma gpreg_o_eq : forall (x y : gpreg_o), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive preg: Type :=
  | IR: gpreg -> preg                   (**r integer general purpose registers *)
  | RA: preg
  | PC: preg
  .

Coercion IR: gpreg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]), return address ([RA]), frame pointer ([FP]) and other temporaries used *)

Notation "'SP'" := GPR12 (only parsing) : asm.
Notation "'FP'" := GPR17 (only parsing) : asm.
Notation "'MFP'" := R17 (only parsing) : asm.
Notation "'GPRA'" := GPR16 (only parsing) : asm.
Notation "'RTMP'" := GPR32 (only parsing) : asm.

Inductive btest: Type :=
  | BTdnez                              (**r Double Not Equal to Zero *)
  | BTdeqz                              (**r Double Equal to Zero *)
  | BTdltz                              (**r Double Less Than Zero *)
  | BTdgez                              (**r Double Greater Than or Equal to Zero *)
  | BTdlez                              (**r Double Less Than or Equal to Zero *)
  | BTdgtz                              (**r Double Greater Than Zero *)
  | BTwnez                              (**r Word Not Equal to Zero *)
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
  .

Inductive ftest: Type :=
  | FTone                               (**r Ordered and Not Equal *)
  | FTueq                               (**r Unordered or Equal *)
  | FToeq                               (**r Ordered and Equal *)
  | FTune                               (**r Unordered or Not Equal *)
  | FTolt                               (**r Ordered and Less Than *)
  | FTuge                               (**r Unordered or Greater Than or Equal *)
  | FToge                               (**r Ordered and Greater Than or Equal *)
  | FTult                               (**r Unordered or Less Than *)
  .

(** Offsets for load and store instructions.  An offset is either an
  immediate integer or the low part of a symbol. *)

Definition offset : Type := ptrofs.

(** We model a subset of the KVX instruction set. In particular, we do not
  support floats yet.

  Although it is possible to use the 32-bits mode, for now we don't support it.

  We follow a design close to the one used for the Risc-V port: one set of
  pseudo-instructions for 32-bit integer arithmetic, with suffix W, another
  set for 64-bit integer arithmetic, with suffix L.

  When mapping to actual instructions, the OCaml code in TargetPrinter.ml
  throws an error if we are not in 64-bits mode.
*)

(** * Instructions *)

Definition label := positive.

(** Instructions to be expanded in control-flow *)
Inductive ex_instruction : Type :=
  (* Pseudo-instructions *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> ex_instruction   (**r built-in function (pseudo) *)
.

(** FIXME: comment not up to date !


 The pseudo-instructions are the following:

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to the [la] assembler pseudo-instruction, which does the right
  thing even if we are in PIC mode.

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
*)

(** Control Flow instructions *)
Inductive cf_instruction : Type :=
  | Pret                                            (**r return *)
  | Pcall   (l: label)                              (**r function call *)
  | Picall  (r: ireg)                               (**r function call on register value *)
  | Pjumptable (r: ireg) (labels: list label) (**r N-way branch through a jump table (pseudo) *)

  (* Pgoto is for tailcalls, Pj_l is for jumping to a particular label *)
  | Pgoto   (l: label)                              (**r goto *)
  | Pigoto  (r: ireg)                               (**r goto from register *)
  | Pj_l    (l: label)                              (**r jump to label *)

  (* Conditional branches *)
  | Pcb     (bt: btest) (r: ireg) (l: label)        (**r branch based on btest *)
  | Pcbu    (bt: btest) (r: ireg) (l: label)        (**r branch based on btest with unsigned semantics *)
.

(** Loads **)
Definition concrete_default_notrap_load_value (chunk : memory_chunk) :=
  match chunk with
  | Mint8signed | Mint8unsigned | Mint16signed | Mint16unsigned
  | Mint32 => Vint Int.zero
  | Mint64 => Vlong Int64.zero
  | Many32 | Many64 => Vundef
  | Mfloat32 => Vsingle Float32.zero
  | Mfloat64 => Vfloat Float.zero
  end.

Inductive load_name : Type :=
  | Plb                                             (**r load byte *)
  | Plbu                                            (**r load byte unsigned *)
  | Plh                                             (**r load half word *)
  | Plhu                                            (**r load half word unsigned *)
  | Plw                                             (**r load int32 *)
  | Plw_a                                           (**r load any32 *)
  | Pld                                             (**r load int64 *)
  | Pld_a                                           (**r load any64 *)
  | Pfls                                            (**r load float *)
  | Pfld                                            (**r load 64-bit float *)
.

Inductive ld_instruction : Type :=
  | PLoadRRO   (trap: trapping_mode) (i: load_name) (rd: ireg) (ra: ireg) (ofs: offset)
  | PLoadRRR   (trap: trapping_mode) (i: load_name) (rd: ireg) (ra: ireg) (rofs: ireg)
  | PLoadRRRXS (trap: trapping_mode) (i: load_name) (rd: ireg) (ra: ireg) (rofs: ireg)
  | PLoadQRRO  (rd: gpreg_q) (ra: ireg) (ofs: offset)
  | PLoadORRO  (rd: gpreg_o) (ra: ireg) (ofs: offset)
.

(** Stores **)
Inductive store_name : Type :=
  | Psb                                             (**r store byte *)
  | Psh                                             (**r store half byte *)
  | Psw                                             (**r store int32 *)
  | Psw_a                                           (**r store any32 *)
  | Psd                                             (**r store int64 *)
  | Psd_a                                           (**r store any64 *)
  | Pfss                                            (**r store float *)
  | Pfsd                                            (**r store 64-bit float *)
.

Inductive st_instruction : Type :=
  | PStoreRRO  (i: store_name) (rs: ireg) (ra: ireg) (ofs: offset)
  | PStoreRRR  (i: store_name) (rs: ireg) (ra: ireg) (rofs: ireg)
  | PStoreRRRXS(i: store_name) (rs: ireg) (ra: ireg) (rofs: ireg)
  | PStoreQRRO (rs: gpreg_q) (ra: ireg) (ofs: offset)
  | PStoreORRO (rs: gpreg_o) (ra: ireg) (ofs: offset)
.

(** Arithmetic instructions **)
Inductive arith_name_r : Type :=
  | Ploadsymbol (id: ident) (ofs: ptrofs)           (**r load the address of a symbol *)
.

Inductive arith_name_rr : Type :=
  | Pmv                                             (**r register move *)
  | Pnegw                                           (**r negate word *)
  | Pnegl                                           (**r negate long *)
  | Pcvtl2w                                         (**r Convert Long to Word *)
  | Psxwd                                           (**r Sign Extend Word to Double Word *)
  | Pzxwd                                           (**r Zero Extend Word to Double Word *)
  | Pextfz (stop : Z) (start : Z)               (**r extract bit field, unsigned *)
  | Pextfs (stop : Z) (start : Z)               (**r extract bit field, signed *)
  | Pextfzl (stop : Z) (start : Z)              (**r extract bit field, unsigned *)
  | Pextfsl (stop : Z) (start : Z)              (**r extract bit field, signed *)
          
  | Pfabsd                                          (**r float absolute double *)
  | Pfabsw                                          (**r float absolute word *)
  | Pfnegd                                          (**r float negate double *)
  | Pfnegw                                          (**r float negate word *)
  | Pfinvw                                          (**r float invert word *)
  | Pfnarrowdw                                      (**r float narrow 64 -> 32 bits *)
  | Pfwidenlwd                                      (**r Floating Point widen from 32 bits to 64 bits *)
  | Pfloatwrnsz                                     (**r Floating Point conversion from integer (int -> SINGLE) *)
  | Pfloatuwrnsz                                    (**r Floating Point conversion from integer (unsigned int -> SINGLE) *)
  | Pfloatudrnsz                                    (**r Floating Point Conversion from integer (unsigned long -> float) *)
  | Pfloatdrnsz                                     (**r Floating Point Conversion from integer (long -> float) *)
  | Pfixedwrzz                                      (**r Integer conversion from floating point (single -> int) *)
  | Pfixeduwrzz                                     (**r Integer conversion from floating point (single -> unsigned int) *)
  | Pfixeddrzz                                      (**r Integer conversion from floating point (float -> long) *)
  | Pfixedudrzz                                      (**r Integer conversion from floating point (float -> unsigned long) *)
  | Pfixeddrzz_i32                                  (**r Integer conversion from floating point (float -> int) *)
  | Pfixedudrzz_i32                                  (**r Integer conversion from floating point (float -> unsigned int) *)
.

Inductive arith_name_ri32 : Type :=
  | Pmake                                           (**r load immediate *)
.

Inductive arith_name_ri64 : Type :=
  | Pmakel                                          (**r load immediate long *)
.

Inductive arith_name_rf32 : Type :=
  | Pmakefs                                         (**r load immediate single *)
.

Inductive arith_name_rf64 : Type :=
  | Pmakef                                          (**r load immediate float *)
.

Inductive arith_name_rrr : Type :=
  | Pcompw  (it: itest)                             (**r comparison word *)
  | Pcompl  (it: itest)                             (**r comparison long *)
  | Pfcompw (ft: ftest)                             (**r comparison float32 *)
  | Pfcompl (ft: ftest)                             (**r comparison float64 *)

  | Paddw                                           (**r add word *)
  | Paddxw (shift : shift1_4)                              (**r add shift *)
  | Psubw                                           (**r sub word word *)
  | Prevsubxw (shift : shift1_4)                              (**r sub shift word *)
  | Pmulw                                           (**r mul word *)
  | Pandw                                           (**r and word *)
  | Pnandw                                          (**r nand word *)
  | Porw                                            (**r or word *)
  | Pnorw                                           (**r nor word *)
  | Pxorw                                           (**r xor word *)
  | Pnxorw                                          (**r nxor word *)
  | Pandnw                                          (**r andn word *)
  | Pornw                                           (**r orn word *)
  | Psraw                                           (**r shift right arithmetic word *)
  | Psrxw                                           (**r shift right arithmetic word round to 0*)
  | Psrlw                                           (**r shift right logical word *)
  | Psllw                                           (**r shift left logical word *)

  | Paddl                                           (**r add long *)
  | Paddxl (shift : shift1_4)                              (**r add shift long *)
  | Psubl                                           (**r sub long *)
  | Prevsubxl (shift : shift1_4)                              (**r sub shift long *)
  | Pandl                                           (**r and long *)
  | Pnandl                                          (**r nand long *)
  | Porl                                            (**r or long *)
  | Pnorl                                           (**r nor long *)
  | Pxorl                                           (**r xor long *)
  | Pnxorl                                          (**r nxor long *)
  | Pandnl                                          (**r andn long *)
  | Pornl                                           (**r orn long *)
  | Pmull                                           (**r mul long (low part) *)
  | Pslll                                           (**r shift left logical long *)
  | Psrll                                           (**r shift right logical long *)
  | Psrxl                                           (**r shift right logical long round to 0*)
  | Psral                                           (**r shift right arithmetic long *)

  | Pfaddd                                          (**r float add double *)
  | Pfaddw                                          (**r float add word *)
  | Pfsbfd                                          (**r float sub double *)
  | Pfsbfw                                          (**r float sub word *)
  | Pfmuld                                          (**r float multiply double *)
  | Pfmulw                                          (**r float multiply word *)
  | Pfmind                                          (**r float min double *)
  | Pfminw                                          (**r float min word *)
  | Pfmaxd                                          (**r float max double *)
  | Pfmaxw                                          (**r float max word *)
.

Inductive arith_name_rri32 : Type :=
  | Pcompiw (it: itest)                             (**r comparison imm word *)

  | Paddiw                                          (**r add imm word *)
  | Paddxiw (shift : shift1_4)
  | Prevsubiw                                          (**r add imm word *)
  | Prevsubxiw (shift : shift1_4)
  | Pmuliw                                          (**r add imm word *)
  | Pandiw                                          (**r and imm word *)
  | Pnandiw                                         (**r nand imm word *)
  | Poriw                                           (**r or imm word *)
  | Pnoriw                                          (**r nor imm word *)
  | Pxoriw                                          (**r xor imm word *)
  | Pnxoriw                                         (**r nxor imm word *)
  | Pandniw                                         (**r andn word *)
  | Porniw                                          (**r orn word *)
  | Psraiw                                          (**r shift right arithmetic imm word *)
  | Psrxiw                                          (**r shift right arithmetic imm word round to 0*)
  | Psrliw                                          (**r shift right logical imm word *)
  | Pslliw                                          (**r shift left logical imm word *)
  | Proriw                                          (**r rotate right imm word *)
  | Psllil                                          (**r shift left logical immediate long *)
  | Psrlil                                          (**r shift right logical immediate long *)
  | Psrail                                          (**r shift right arithmetic immediate long *)
  | Psrxil                                          (**r shift right arithmetic immediate long round to 0*)
.

Inductive arith_name_rri64 : Type :=
  | Pcompil (it: itest)                             (**r comparison imm long *)
  | Paddil                                          (**r add immediate long *) 
  | Paddxil (shift : shift1_4)
  | Prevsubil
  | Prevsubxil (shift : shift1_4)
  | Pmulil                                          (**r mul immediate long *) 
  | Pandil                                          (**r and immediate long *) 
  | Pnandil                                         (**r nand immediate long *) 
  | Poril                                           (**r or immediate long *) 
  | Pnoril                                          (**r nor immediate long *) 
  | Pxoril                                          (**r xor immediate long *) 
  | Pnxoril                                         (**r nxor immediate long *) 
  | Pandnil                                         (**r andn immediate long *)
  | Pornil                                          (**r orn immediate long *)
.

Inductive arith_name_arrr : Type :=
  | Pmaddw                                           (**r multiply add word *)
  | Pmaddl                                           (**r multiply add long *)
  | Pmsubw                                           (**r multiply subtract word *)
  | Pmsubl                                           (**r multiply subtract long *)
  | Pcmove (bt: btest)                               (**r conditional move *)
  | Pcmoveu (bt: btest)                              (**r conditional move, test on unsigned semantics *)
  | Pfmaddfw                                         (**r float fused multiply add word *)
  | Pfmaddfl                                         (**r float fused multiply add long *)
  | Pfmsubfw                                         (**r float fused multiply subtract word *)
  | Pfmsubfl                                         (**r float fused multiply subtract long *)
.

Inductive arith_name_arri32 : Type :=
  | Pmaddiw                                           (**r multiply add word *)
  | Pcmoveiw (bt: btest)
  | Pcmoveuiw (bt: btest)
.

Inductive arith_name_arri64 : Type :=
  | Pmaddil                                           (**r multiply add long *)
  | Pcmoveil (bt: btest)
  | Pcmoveuil (bt: btest)
.

Inductive arith_name_arr : Type :=
  | Pinsf (stop : Z) (start : Z)                (**r insert bit field *)
  | Pinsfl (stop : Z) (start : Z)               (**r insert bit field *)
.

Inductive ar_instruction : Type :=
  | PArithR     (i: arith_name_r)     (rd: ireg)
  | PArithRR    (i: arith_name_rr)    (rd rs: ireg)
  | PArithRI32  (i: arith_name_ri32)  (rd: ireg) (imm: int)
  | PArithRI64  (i: arith_name_ri64)  (rd: ireg) (imm: int64)
  | PArithRF32  (i: arith_name_rf32)  (rd: ireg) (imm: float32)
  | PArithRF64  (i: arith_name_rf64)  (rd: ireg) (imm: float)
  | PArithRRR   (i: arith_name_rrr)   (rd rs1 rs2: ireg)
  | PArithRRI32 (i: arith_name_rri32) (rd rs: ireg) (imm: int)
  | PArithRRI64 (i: arith_name_rri64) (rd rs: ireg) (imm: int64)
  | PArithARRR   (i: arith_name_arrr)   (rd rs1 rs2: ireg)
  | PArithARR   (i: arith_name_arr) (rd rs: ireg)
  | PArithARRI32 (i: arith_name_arri32) (rd rs: ireg) (imm: int)
  | PArithARRI64 (i: arith_name_arri64) (rd rs: ireg) (imm: int64)
.

Module PArithCoercions.

Coercion PArithR:       arith_name_r        >-> Funclass.
Coercion PArithRR:      arith_name_rr       >-> Funclass.
Coercion PArithRI32:    arith_name_ri32     >-> Funclass.
Coercion PArithRI64:    arith_name_ri64     >-> Funclass.
Coercion PArithRF32:    arith_name_rf32     >-> Funclass.
Coercion PArithRF64:    arith_name_rf64     >-> Funclass.
Coercion PArithRRR:     arith_name_rrr      >-> Funclass.
Coercion PArithRRI32:   arith_name_rri32    >-> Funclass.
Coercion PArithRRI64:   arith_name_rri64    >-> Funclass.
Coercion PArithARRR:    arith_name_arrr     >-> Funclass.
Coercion PArithARR:     arith_name_arr      >-> Funclass.
Coercion PArithARRI32:   arith_name_arri32    >-> Funclass.
Coercion PArithARRI64:   arith_name_arri64    >-> Funclass.

End PArithCoercions.

Inductive basic : Type :=
  | PArith          (i: ar_instruction)
  | PLoad           (i: ld_instruction)
  | PStore          (i: st_instruction)
  | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)               (**r deallocate stack frame and restore previous frame *)
  | Pget    (rd: ireg) (rs: preg)                   (**r get system register *)
  | Pset    (rd: preg) (rs: ireg)                   (**r set system register *)
  | Pnop                                            (**r virtual instruction that does nothing *)
.

Coercion PLoad:         ld_instruction >-> basic.
Coercion PStore:        st_instruction >-> basic.
Coercion PArith:        ar_instruction >-> basic.


Inductive control : Type :=
  | PExpand         (i: ex_instruction)
  | PCtlFlow        (i: cf_instruction)
.

Coercion PExpand:   ex_instruction >-> control.
Coercion PCtlFlow:  cf_instruction >-> control.


(** * Definition of a bblock (ie a bundle)

A bundle/bblock must contain at least one instruction.

This choice simplifies the definition of [find_bblock] below:
indeed, each address of a code block identifies at most one bundle
(which depends on the number of instructions in the bundles of lower addresses).

*)

Definition non_empty_body (body: list basic): bool :=
  match body with
  | nil => false
  | _ => true
  end.

Definition non_empty_exit (exit: option control): bool :=
  match exit with
  | None => false
  | _ => true
  end.

Definition non_empty_bblockb (body: list basic) (exit: option control): bool := non_empty_body body || non_empty_exit exit.


(** TODO
 * For now, we consider a builtin is alone in a bundle (and a basic block).
 * Is there a way to avoid that ?
 *)
Definition builtin_aloneb (body: list basic) (exit: option control) :=
  match exit with
  | Some (PExpand (Pbuiltin _ _ _)) =>
    match body with
    | nil => true
    | _ => false
    end
  | _ => true
  end.

Definition wf_bblockb (body: list basic) (exit: option control) :=
  (non_empty_bblockb body exit) && (builtin_aloneb body exit).

(** A bblock is well-formed if he contains at least one instruction,
    and if there is a builtin then it must be alone in this bblock. *)

Record bblock := mk_bblock {
  header: list label;
  body: list basic;
  exit: option control;
  correct: Is_true (wf_bblockb body exit)
}.

(* FIXME? redundant with definition in Machblock *)
Definition length_opt {A} (o: option A) : nat :=
  match o with
  | Some o => 1
  | None => 0
  end.

(* WARNING: the notion of size is not the same than in Machblock !
   We ignore labels here...

   This notion of size induces the notion of "valid" code address given by [find_bblock]

   The result is in Z to be compatible with operations on PC.
*)
Definition size (b:bblock): Z := Z.of_nat (length (body b) + length_opt (exit b)).

Definition bblocks := list bblock.

Fixpoint size_blocks (l: bblocks): Z :=
  match l with
  | nil => 0
  | b :: l =>
     (size b) + (size_blocks l)
  end
  .

Record function : Type := mkfunction { fn_sig: signature; fn_blocks: bblocks }.
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

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
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


(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Local Open Scope asm.

(** * Parallel Semantics of bundles *)

Section RELSEM.

(** Execution of arith instructions *)

Variable ge: genv.

(** The parallel semantics on bundles is purely small-step and defined as a relation
  from the current state (a register set + a memory state) to either [Next rs' m']
  where [rs'] and [m'] are the updated register set and memory state after execution
  of the instruction at [rs#PC], or [Stuck] if the processor is stuck.
 
  The parallel semantics of each instructions handles two states in input:
   - the actual input state of the bundle which is only read
   - and the other on which every "write" is performed:
     it represents a temporary "writes" buffer, from which the final state
     of the bundle is computed.

  NB: the sequential semantics defined in [Asmblock] is derived
  from the parallel semantics of each instruction by identifying
  the read state and the write state.

*)

Inductive outcome: Type :=
  | Next (rs:regset) (m:mem)
  | Stuck
.

(** ** Arithmetic Expressions (including comparisons) *)

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

Inductive oporder_ftest :=
  | Normal (ft: ftest)
  | Reversed (ft: ftest)
.

Definition ftest_for_cmp (c: comparison) :=
  match c with
  | Ceq => Normal FToeq
  | Cne => Normal FTune
  | Clt => Normal FTolt
  | Cle => Reversed FToge
  | Cgt => Reversed FTolt
  | Cge => Normal FToge
  end.

Definition notftest_for_cmp (c: comparison) :=
  match c with
  | Ceq => Normal FTune
  | Cne => Normal FToeq
  | Clt => Normal FTuge
  | Cle => Reversed FTult
  | Cgt => Reversed FTuge
  | Cge => Normal FTult
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


(* a few lemma on comparisons of unsigned (e.g. pointers) *)

Definition Val_cmpu_bool cmp v1 v2: option bool :=
  Val.cmpu_bool (fun _ _ => true) cmp v1 v2.

Lemma Val_cmpu_bool_correct (m:mem) (cmp: comparison) (v1 v2: val) b:
   (Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) = Some b
   -> (Val_cmpu_bool cmp v1 v2) = Some b.
Proof.
  intros; eapply Val.cmpu_bool_lessdef; (econstructor 1 || eauto).
Qed.

Definition Val_cmpu cmp v1 v2 := Val.of_optbool (Val_cmpu_bool cmp v1 v2).

Lemma Val_cmpu_correct (m:mem) (cmp: comparison) (v1 v2: val):
   Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp v1 v2)
               (Val_cmpu cmp v1 v2).
Proof.
  unfold Val.cmpu, Val_cmpu.
  remember (Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as ob.
  destruct ob; simpl.
  - erewrite Val_cmpu_bool_correct; eauto.
    econstructor.
  - econstructor.
Qed.

Definition Val_cmplu_bool (cmp: comparison) (v1 v2: val)
 := (Val.cmplu_bool (fun _ _ => true) cmp v1 v2).

Lemma Val_cmplu_bool_correct (m:mem) (cmp: comparison) (v1 v2: val) b:
   (Val.cmplu_bool (Mem.valid_pointer m) cmp v1 v2) = Some b
   -> (Val_cmplu_bool cmp v1 v2) = Some b.
Proof.
  intros; eapply Val.cmplu_bool_lessdef; (econstructor 1 || eauto).
Qed.

Definition Val_cmplu cmp v1 v2 := Val.of_optbool (Val_cmplu_bool cmp v1 v2).

Lemma Val_cmplu_correct (m:mem) (cmp: comparison) (v1 v2: val):
   Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp v1 v2))
               (Val_cmplu cmp v1 v2).
Proof.
  unfold Val.cmplu, Val_cmplu.
  remember (Val.cmplu_bool (Mem.valid_pointer m) cmp v1 v2) as ob.
  destruct ob as [b|]; simpl.
  - erewrite Val_cmplu_bool_correct; eauto.
    simpl. econstructor.
  - econstructor.
Qed.



(** Comparing integers *)
Definition compare_int (t: itest) (v1 v2: val): val :=
  match t with
  | ITne  => Val.cmp Cne v1 v2
  | ITeq  => Val.cmp Ceq v1 v2
  | ITlt  => Val.cmp Clt v1 v2
  | ITge  => Val.cmp Cge v1 v2
  | ITle  => Val.cmp Cle v1 v2
  | ITgt  => Val.cmp Cgt v1 v2
  | ITneu => Val_cmpu Cne v1 v2
  | ITequ => Val_cmpu Ceq v1 v2
  | ITltu => Val_cmpu Clt v1 v2
  | ITgeu => Val_cmpu Cge v1 v2
  | ITleu => Val_cmpu Cle v1 v2
  | ITgtu => Val_cmpu Cgt v1 v2
  end.

Definition compare_long (t: itest) (v1 v2: val): val :=
  let res := match t with
  | ITne  => Val.cmpl Cne v1 v2
  | ITeq  => Val.cmpl Ceq v1 v2
  | ITlt  => Val.cmpl Clt v1 v2
  | ITge  => Val.cmpl Cge v1 v2
  | ITle  => Val.cmpl Cle v1 v2
  | ITgt  => Val.cmpl Cgt v1 v2
  | ITneu => Some (Val_cmplu Cne v1 v2)
  | ITequ => Some (Val_cmplu Ceq v1 v2)
  | ITltu => Some (Val_cmplu Clt v1 v2)
  | ITgeu => Some (Val_cmplu Cge v1 v2)
  | ITleu => Some (Val_cmplu Cle v1 v2)
  | ITgtu => Some (Val_cmplu Cgt v1 v2)
  end in 
  match res with
  | Some v => v
  | None => Vundef
  end
  .

Definition compare_single (t: ftest) (v1 v2: val): val :=
  match t with
  | FTone | FTueq => Vundef (* unused *)
  | FToeq => Val.cmpfs Ceq v1 v2
  | FTune => Val.cmpfs Cne v1 v2
  | FTolt => Val.cmpfs Clt v1 v2
  | FTuge => Val.notbool (Val.cmpfs Clt v1 v2)
  | FToge => Val.cmpfs Cge v1 v2
  | FTult => Val.notbool (Val.cmpfs Cge v1 v2)
  end.

Definition compare_float (t: ftest) (v1 v2: val): val :=
  match t with
  | FTone | FTueq => Vundef (* unused *)
  | FToeq => Val.cmpf Ceq v1 v2
  | FTune => Val.cmpf Cne v1 v2
  | FTolt => Val.cmpf Clt v1 v2
  | FTuge => Val.notbool (Val.cmpf Clt v1 v2)
  | FToge => Val.cmpf Cge v1 v2
  | FTult => Val.notbool (Val.cmpf Cge v1 v2)
  end.

Definition arith_eval_r n :=
  match n with
  | Ploadsymbol s ofs => Genv.symbol_address ge s ofs
  end
.

Definition arith_eval_rr n v :=
  match n with
  | Pmv => v
  | Pnegw => Val.neg v
  | Pnegl => Val.negl v
  | Pcvtl2w => Val.loword v
  | Psxwd => Val.longofint v
  | Pzxwd => Val.longofintu v
  | Pextfz stop start => extfz stop start v
  | Pextfs stop start => extfs stop start v
  | Pextfzl stop start => extfzl stop start v
  | Pextfsl stop start => extfsl stop start v
  | Pfnegd => Val.negf v
  | Pfnegw => Val.negfs v
  | Pfabsd => Val.absf v
  | Pfabsw => Val.absfs v
  | Pfinvw => ExtValues.invfs v
  | Pfnarrowdw => Val.singleoffloat v
  | Pfwidenlwd => Val.floatofsingle v
  | Pfloatwrnsz => Val.maketotal (Val.singleofint v)
  | Pfloatuwrnsz => Val.maketotal (Val.singleofintu v)
  | Pfloatudrnsz => Val.maketotal (Val.floatoflongu v)
  | Pfloatdrnsz => Val.maketotal (Val.floatoflong v)
  | Pfixedwrzz => Val.maketotal (Val.intofsingle v)
  | Pfixeduwrzz => Val.maketotal (Val.intuofsingle v)
  | Pfixeddrzz => Val.maketotal (Val.longoffloat v)
  | Pfixedudrzz => Val.maketotal (Val.longuoffloat v)
  | Pfixeddrzz_i32 => Val.maketotal (Val.intoffloat v)
  | Pfixedudrzz_i32 => Val.maketotal (Val.intuoffloat v)
  end.

Definition arith_eval_ri32 n i :=
  match n with
  | Pmake => Vint i
  end.

Definition arith_eval_ri64 n i :=
  match n with
  | Pmakel => Vlong i
  end.

Definition arith_eval_rf32 n i :=
  match n with
  | Pmakefs => Vsingle i
  end.

Definition arith_eval_rf64 n i :=
  match n with
  | Pmakef => Vfloat i
  end.

Definition arith_eval_rrr n v1 v2 :=
  match n with
  | Pcompw c => compare_int c v1 v2
  | Pcompl c => compare_long c v1 v2
  | Pfcompw c => compare_single c v1 v2
  | Pfcompl c => compare_float c v1 v2

  | Paddw  => Val.add  v1 v2
  | Psubw  => Val.sub  v1 v2
  | Pmulw  => Val.mul  v1 v2
  | Pandw  => Val.and  v1 v2
  | Pnandw => Val.notint (Val.and v1 v2)
  | Porw   => Val.or   v1 v2
  | Pnorw  => Val.notint (Val.or v1 v2)
  | Pxorw  => Val.xor  v1 v2
  | Pnxorw => Val.notint (Val.xor v1 v2)
  | Pandnw => Val.and (Val.notint v1) v2
  | Pornw  => Val.or (Val.notint v1) v2
  | Psrlw  => Val.shru v1 v2
  | Psraw  => Val.shr  v1 v2
  | Psllw  => Val.shl  v1 v2
  | Psrxw  => ExtValues.val_shrx  v1 v2

  | Paddl => Val.addl v1 v2
  | Psubl => Val.subl v1 v2
  | Pandl => Val.andl v1 v2
  | Pnandl => Val.notl (Val.andl v1 v2)
  | Porl  => Val.orl  v1 v2
  | Pnorl  => Val.notl (Val.orl  v1 v2)
  | Pxorl  => Val.xorl  v1 v2
  | Pnxorl  => Val.notl (Val.xorl  v1 v2)
  | Pandnl => Val.andl (Val.notl v1) v2
  | Pornl  => Val.orl (Val.notl v1) v2
  | Pmull => Val.mull v1 v2
  | Pslll => Val.shll v1 v2
  | Psrll => Val.shrlu v1 v2
  | Psral => Val.shrl v1 v2
  | Psrxl  => ExtValues.val_shrxl v1 v2

  | Pfaddd => Val.addf v1 v2
  | Pfaddw => Val.addfs v1 v2
  | Pfsbfd => Val.subf v1 v2
  | Pfsbfw => Val.subfs v1 v2
  | Pfmuld => Val.mulf v1 v2
  | Pfmulw => Val.mulfs v1 v2

  | Pfmind => ExtValues.minf v1 v2
  | Pfminw => ExtValues.minfs v1 v2
  | Pfmaxd => ExtValues.maxf v1 v2
  | Pfmaxw => ExtValues.maxfs v1 v2

  | Paddxw shift => ExtValues.addx (int_of_shift1_4 shift) v1 v2
  | Paddxl shift => ExtValues.addxl (int_of_shift1_4 shift) v1 v2

  | Prevsubxw shift => ExtValues.revsubx (int_of_shift1_4 shift) v1 v2
  | Prevsubxl shift => ExtValues.revsubxl (int_of_shift1_4 shift) v1 v2
  end.

Definition arith_eval_rri32 n v i :=
  match n with
  | Pcompiw c => compare_int c v (Vint i)
  | Paddiw  => Val.add   v (Vint i)
  | Prevsubiw  => Val.sub (Vint i) v
  | Pmuliw  => Val.mul   v (Vint i)
  | Pandiw  => Val.and   v (Vint i)
  | Pnandiw => Val.notint (Val.and  v (Vint i))
  | Poriw   => Val.or    v (Vint i)
  | Pnoriw  => Val.notint (Val.or v (Vint i))
  | Pxoriw  => Val.xor   v (Vint i)
  | Pnxoriw => Val.notint (Val.xor v (Vint i))
  | Pandniw => Val.and (Val.notint v) (Vint i)
  | Porniw  => Val.or (Val.notint v) (Vint i)
  | Psraiw  => Val.shr   v (Vint i)
  | Psrxiw  => ExtValues.val_shrx v (Vint i)
  | Psrliw  => Val.shru  v (Vint i)
  | Pslliw  => Val.shl   v (Vint i)
  | Proriw  => Val.ror   v (Vint i)
  | Psllil  => Val.shll  v (Vint i)
  | Psrxil  => ExtValues.val_shrxl v (Vint i)
  | Psrlil  => Val.shrlu v (Vint i)
  | Psrail  => Val.shrl  v (Vint i)
  | Paddxiw shift => ExtValues.addx (int_of_shift1_4 shift) v (Vint i)
  | Prevsubxiw shift => ExtValues.revsubx (int_of_shift1_4 shift) v (Vint i)
  end.

Definition arith_eval_rri64 n v i :=
  match n with
  | Pcompil c => compare_long c v (Vlong i)
  | Paddil  => Val.addl v (Vlong i)
  | Prevsubil  => Val.subl (Vlong i) v
  | Pmulil  => Val.mull v (Vlong i)
  | Pandil  => Val.andl v (Vlong i)
  | Pnandil  => Val.notl (Val.andl v (Vlong i))
  | Poril   => Val.orl  v (Vlong i)
  | Pnoril   => Val.notl (Val.orl  v (Vlong i))
  | Pxoril  => Val.xorl  v (Vlong i)
  | Pnxoril  => Val.notl (Val.xorl  v (Vlong i))
  | Pandnil => Val.andl (Val.notl v) (Vlong i)
  | Pornil  => Val.orl (Val.notl v) (Vlong i)
  | Paddxil shift => ExtValues.addxl (int_of_shift1_4 shift) v (Vlong i)
  | Prevsubxil shift => ExtValues.revsubxl (int_of_shift1_4 shift) v (Vlong i)
  end.

Definition cmove bt v1 v2 v3 :=
  match cmp_for_btest bt with
  | (Some c, Int)  =>
    match Val.cmp_bool c v2 (Vint Int.zero) with
    | None => Vundef
    | Some true => v3
    | Some false => v1
    end
  | (Some c, Long) =>
    match Val.cmpl_bool c v2 (Vlong Int64.zero) with
    | None => Vundef
    | Some true => v3
    | Some false => v1
    end
  | (None, _) => Vundef
  end.

Definition cmoveu bt v1 v2 v3 :=
  match cmpu_for_btest bt with
  | (Some c, Int)  =>
    match Val_cmpu_bool c v2 (Vint Int.zero) with
    | None => Vundef
    | Some true => v3
    | Some false => v1
    end
  | (Some c, Long) =>
    match Val_cmplu_bool c v2 (Vlong Int64.zero) with
    | None => Vundef
    | Some true => v3
    | Some false => v1
    end
  | (None, _) => Vundef
  end.

Definition arith_eval_arrr n v1 v2 v3 :=
  match n with
  | Pmaddw => Val.add v1 (Val.mul v2 v3)
  | Pmaddl => Val.addl v1 (Val.mull v2 v3)
  | Pmsubw => Val.sub v1 (Val.mul v2 v3)
  | Pmsubl => Val.subl v1 (Val.mull v2 v3)
  | Pcmove bt => cmove bt v1 v2 v3
  | Pcmoveu bt => cmoveu bt v1 v2 v3
  | Pfmaddfw => ExtValues.fmaddfs v1 v2 v3
  | Pfmaddfl => ExtValues.fmaddf v1 v2 v3
  | Pfmsubfw => ExtValues.fmsubfs v1 v2 v3
  | Pfmsubfl => ExtValues.fmsubf v1 v2 v3
  end.

Definition arith_eval_arr n v1 v2 :=
  match n with
  | Pinsf stop start => ExtValues.insf stop start v1 v2
  | Pinsfl stop start => ExtValues.insfl stop start v1 v2
  end.

Definition arith_eval_arri32 n v1 v2 v3 :=
  match n with
  | Pmaddiw => Val.add v1 (Val.mul v2 (Vint v3))
  | Pcmoveiw bt => cmove bt v1 v2 (Vint v3)
  | Pcmoveuiw bt => cmoveu bt v1 v2 (Vint v3)
  end.

Definition arith_eval_arri64 n v1 v2 v3 :=
  match n with
  | Pmaddil => Val.addl v1 (Val.mull v2 (Vlong v3))
  | Pcmoveil bt => cmove bt v1 v2 (Vlong v3)
  | Pcmoveuil bt => cmoveu bt v1 v2 (Vlong v3)
  end.

Definition parexec_arith_instr (ai: ar_instruction) (rsr rsw: regset): regset :=
  match ai with
  | PArithR n d => rsw#d <- (arith_eval_r n)

  | PArithRR n d s => rsw#d <- (arith_eval_rr n rsr#s)

  | PArithRI32 n d i => rsw#d <- (arith_eval_ri32 n i)
  | PArithRI64 n d i => rsw#d <- (arith_eval_ri64 n i)
  | PArithRF32 n d i => rsw#d <- (arith_eval_rf32 n i)
  | PArithRF64 n d i => rsw#d <- (arith_eval_rf64 n i)

  | PArithRRR n d s1 s2 => rsw#d <- (arith_eval_rrr n rsr#s1 rsr#s2)
  | PArithRRI32 n d s i => rsw#d <- (arith_eval_rri32 n rsr#s i)
  | PArithRRI64 n d s i => rsw#d <- (arith_eval_rri64 n rsr#s i)

  | PArithARRR n d s1 s2 => rsw#d <- (arith_eval_arrr n rsr#d rsr#s1 rsr#s2)
  | PArithARR n d s => rsw#d <- (arith_eval_arr n rsr#d rsr#s)
  | PArithARRI32 n d s i => rsw#d <- (arith_eval_arri32 n rsr#d rsr#s i)
  | PArithARRI64 n d s i => rsw#d <- (arith_eval_arri64 n rsr#d rsr#s i)
  end.

Definition eval_offset (ofs: offset) : res ptrofs := OK ofs.

(** * load/store *)

Definition parexec_incorrect_load trap chunk d rsw mw :=
  match trap with
  | TRAP => Stuck
  | NOTRAP => Next (rsw#d <- (concrete_default_notrap_load_value chunk)) mw
  end.

Definition parexec_load_offset (trap: trapping_mode) (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (d a: ireg) (ofs: offset) :=
  match (eval_offset ofs) with
  | OK ptr => match Mem.loadv chunk mr (Val.offset_ptr (rsr a) ptr) with
              | None => parexec_incorrect_load trap chunk d rsw mw
              | Some v => Next (rsw#d <- v) mw
              end
  | _ => Stuck
  end.

Definition parexec_load_q_offset (rsr rsw: regset) (mr mw: mem) (d : gpreg_q) (a: ireg) (ofs: offset) :=
  let (rd0, rd1) := gpreg_q_expand d in
(* NB: By construction of [gpreg_q], register rd0 and rd1 are distinct, thus, the register writes cannot overlap.
       But we do not need to express/prove this in the semantics.
*)
    match Mem.loadv Many64 mr (Val.offset_ptr (rsr a) ofs) with
    | None => Stuck
    | Some v0 =>
      match Mem.loadv Many64 mr (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 8))) with
      | None => Stuck
      | Some v1 => Next (rsw#rd0 <- v0 #rd1 <- v1) mw
      end
    end.

Definition parexec_load_o_offset (rsr rsw: regset) (mr mw: mem) (d : gpreg_o) (a: ireg) (ofs: offset) :=
  match gpreg_o_expand d with
  | (rd0, rd1, rd2, rd3) =>
(* NB: By construction of [gpreg_o], the four destination registers are pairwise distinct, thus, the register writes cannot overlap.
       But we do not need to express/prove this in the semantics.
*)
   match Mem.loadv Many64 mr (Val.offset_ptr (rsr a) ofs) with
    | None => Stuck
    | Some v0 =>
      match Mem.loadv Many64 mr (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 8))) with
      | None => Stuck
      | Some v1 =>
        match Mem.loadv Many64 mr (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 16))) with
        | None => Stuck
        | Some v2 =>
          match Mem.loadv Many64 mr (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 24))) with
          | None => Stuck
          | Some v3 =>
            Next (rsw#rd0 <- v0 #rd1 <- v1 #rd2 <- v2 #rd3 <- v3) mw
          end
        end
      end
    end
  end.

Definition parexec_load_reg (trap: trapping_mode) (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (d a ro: ireg) :=
  match Mem.loadv chunk mr (Val.addl (rsr a) (rsr ro)) with
  | None => parexec_incorrect_load trap chunk d rsw mw
  | Some v => Next (rsw#d <- v) mw
  end.

Definition parexec_load_regxs (trap: trapping_mode) (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (d a ro: ireg) :=
  match Mem.loadv chunk mr (Val.addl (rsr a) (Val.shll (rsr ro) (scale_of_chunk chunk))) with
  | None => parexec_incorrect_load trap chunk d rsw mw
  | Some v => Next (rsw#d <- v) mw
  end.

Definition parexec_store_offset (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (s a: ireg) (ofs: offset) :=
  match (eval_offset ofs) with
  | OK ptr => match Mem.storev chunk mr (Val.offset_ptr (rsr a) ptr) (rsr s) with
              | None => Stuck
              | Some m' => Next rsw m'
              end
  | _ => Stuck
  end.

Definition parexec_store_reg
           (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (s a ro: ireg) :=
  match Mem.storev chunk mr (Val.addl (rsr a) (rsr ro)) (rsr s) with
  | None => Stuck
  | Some m' => Next rsw m'
  end.

Definition parexec_store_regxs (chunk: memory_chunk) (rsr rsw: regset) (mr mw: mem) (s a ro: ireg) :=
  match Mem.storev chunk mr (Val.addl (rsr a) (Val.shll (rsr ro) (scale_of_chunk chunk))) (rsr s) with
  | None => Stuck
  | Some m' => Next rsw m'
  end.

Definition parexec_store_q_offset (rsr rsw: regset) (mr mw: mem) (s : gpreg_q) (a: ireg) (ofs: offset) :=
  let (s0, s1) := gpreg_q_expand s in
  match Mem.storev Many64 mr (Val.offset_ptr (rsr a) ofs) (rsr s0) with
  | None => Stuck
  | Some m1 =>
    match Mem.storev Many64 m1 (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 8))) (rsr s1) with
    | None => Stuck
    | Some m2 => Next rsw m2
    end
  end.
  
Definition parexec_store_o_offset (rsr rsw: regset) (mr mw: mem) (s : gpreg_o) (a: ireg) (ofs: offset) :=
  match gpreg_o_expand s with
  | (s0, s1, s2, s3) =>
    match Mem.storev Many64 mr (Val.offset_ptr (rsr a) ofs) (rsr s0) with
    | None => Stuck
    | Some m1 =>
      match Mem.storev Many64 m1 (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 8))) (rsr s1) with
      | None => Stuck
      | Some m2 =>
        match Mem.storev Many64 m2 (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 16))) (rsr s2) with
        | None => Stuck
        | Some m3 =>
          match Mem.storev Many64 m3 (Val.offset_ptr (rsr a) (Ptrofs.add ofs (Ptrofs.repr 24))) (rsr s3) with
          | None => Stuck
          | Some m4 => Next rsw m4
          end
        end
      end
    end
  end.
  

Definition load_chunk n :=
  match n with
  | Plb => Mint8signed
  | Plbu => Mint8unsigned
  | Plh => Mint16signed
  | Plhu => Mint16unsigned
  | Plw => Mint32
  | Plw_a => Many32
  | Pld => Mint64
  | Pld_a => Many64
  | Pfls => Mfloat32
  | Pfld => Mfloat64
  end.
              
Definition store_chunk n :=
  match n with
  | Psb => Mint8unsigned
  | Psh => Mint16unsigned
  | Psw => Mint32
  | Psw_a => Many32
  | Psd => Mint64
  | Psd_a => Many64
  | Pfss => Mfloat32
  | Pfsd => Mfloat64
  end.

(** * basic instructions *)

Definition bstep (bi: basic) (rsr rsw: regset) (mr mw: mem) :=
  match bi with
  | PArith ai => Next (parexec_arith_instr ai rsr rsw) mw

  | PLoad (PLoadRRO trap n d a ofs) => parexec_load_offset trap (load_chunk n) rsr rsw mr mw d a ofs
  | PLoad (PLoadRRR trap n d a ro) => parexec_load_reg trap (load_chunk n) rsr rsw mr mw d a ro
  | PLoad (PLoadRRRXS trap n d a ro) => parexec_load_regxs trap (load_chunk n) rsr rsw mr mw d a ro
  | PLoad (PLoadQRRO d a ofs) => 
    parexec_load_q_offset rsr rsw mr mw d a ofs
  | PLoad (PLoadORRO d a ofs) => 
    parexec_load_o_offset rsr rsw mr mw d a ofs

  | PStoreRRO n s a ofs => parexec_store_offset (store_chunk n) rsr rsw mr mw s a ofs
  | PStoreRRR n s a ro => parexec_store_reg (store_chunk n) rsr rsw mr mw s a ro
  | PStoreRRRXS n s a ro => parexec_store_regxs (store_chunk n) rsr rsw mr mw s a ro
  | PStoreQRRO s a ofs => 
    parexec_store_q_offset rsr rsw mr mw s a ofs
  | PStoreORRO s a ofs => 
    parexec_store_o_offset rsr rsw mr mw s a ofs

  | Pallocframe sz pos =>
      let (mw, stk) := Mem.alloc mr 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr mw (Val.offset_ptr sp pos) rsr#SP with
      | None => Stuck
      | Some mw => Next (rsw #FP <- (rsr SP) #SP <- sp #RTMP <- Vundef) mw
      end

  | Pfreeframe sz pos =>
      match Mem.loadv Mptr mr (Val.offset_ptr rsr#SP pos) with
      | None => Stuck
      | Some v =>
          match rsr SP with
          | Vptr stk ofs =>
              match Mem.free mr stk 0 sz with
              | None => Stuck
              | Some mw => Next (rsw#SP <- v #RTMP <- Vundef) mw
              end
          | _ => Stuck
          end
      end
  | Pget rd ra =>
    match ra with
    | RA => Next (rsw#rd <- (rsr#ra)) mw
    | _  => Stuck
    end
  | Pset ra rd =>
    match ra with
    | RA => Next (rsw#ra <- (rsr#rd)) mw
    | _  => Stuck
    end
  | Pnop => Next rsw mw
end.

(* parexec with writes-in-order *)
Fixpoint parexec_wio_body (body: list basic) (rsr rsw: regset) (mr mw: mem) :=
  match body with
  | nil => Next rsw mw
  | bi::body' => 
     match bstep bi rsr rsw mr mw with
     | Next rsw mw => parexec_wio_body body' rsr rsw mr mw
     | Stuck => Stuck
     end
  end.

(** TODO: redundant w.r.t Machblock ?? *)
Lemma in_dec (lbl: label) (l: list label):  { List.In lbl l } + { ~(List.In lbl l) }.
Proof.
  apply List.in_dec.
  apply Pos.eq_dec.
Qed.



(** Note: copy-paste from Machblock *)
Definition is_label (lbl: label) (bb: bblock) : bool :=
  if in_dec lbl (header bb) then true else false.

Lemma is_label_correct_true lbl bb:
  List.In lbl (header bb) <-> is_label lbl bb = true. 
Proof.
  unfold is_label; destruct (in_dec lbl (header bb)); simpl; intuition.
Qed.

Lemma is_label_correct_false lbl bb:
  ~(List.In lbl (header bb)) <-> is_label lbl bb = false. 
Proof.
  unfold is_label; destruct (in_dec lbl (header bb)); simpl; intuition.
Qed.



(** convert a label into a position in the code *)
Fixpoint label_pos (lbl: label) (pos: Z) (lb: bblocks) {struct lb} : option Z :=
  match lb with
  | nil => None
  | b :: lb' => if is_label lbl b then Some pos else label_pos lbl (pos + (size b)) lb'
  end.

Definition par_goto_label (f: function) (lbl: label) (rsr rsw: regset) (mw: mem) :=
  match label_pos lbl 0 (fn_blocks f) with
  | None => Stuck
  | Some pos =>
      match rsr#PC with
      | Vptr b ofs => Next (rsw#PC <- (Vptr b (Ptrofs.repr pos))) mw
      | _          => Stuck
      end
  end.

(** Evaluating a branch 

Warning: in m PC is assumed to be already pointing on the next instruction !

*)

Definition par_eval_branch (f: function) (l: label) (rsr rsw: regset) (mw: mem) (res: option bool) :=
  match res with
    | Some true  => par_goto_label f l rsr rsw mw
    | Some false => Next (rsw # PC <- (rsr PC)) mw
    | None => Stuck
  end.


(* FIXME: comment not up-to-date for parallel semantics *)

(** Execution of a single control-flow instruction [i] in initial state [rs] and
    [m].  Return updated state.

    As above: PC is assumed to be incremented on the next block before the control-flow instruction

    For instructions that correspond tobuiltin
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition parexec_control (f: function) (oc: option control) (rsr rsw: regset) (mw: mem) :=
  match oc with
  | Some ic =>
(** Get/Set system registers *)
  match ic with


(** Branch Control Unit instructions *)
  | Pret =>
      Next (rsw#PC <- (rsr#RA)) mw
  | Pcall s =>
      Next (rsw#RA <- (rsr#PC) #PC <- (Genv.symbol_address ge s Ptrofs.zero)) mw
  | Picall r =>
      Next (rsw#RA <- (rsr#PC) #PC <- (rsr#r)) mw
  | Pjumptable r tbl =>
      match rsr#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => par_goto_label f lbl rsr (rsw #GPR62 <- Vundef #GPR63 <- Vundef) mw
          end
      | _ => Stuck
      end
  | Pgoto s =>
      Next (rsw#PC <- (Genv.symbol_address ge s Ptrofs.zero)) mw
  | Pigoto r =>
      Next (rsw#PC <- (rsr#r)) mw
  | Pj_l l =>
      par_goto_label f l rsr rsw mw
  | Pcb bt r l =>
      match cmp_for_btest bt with
      | (Some c, Int)  => par_eval_branch f l rsr rsw mw (Val.cmp_bool c rsr#r (Vint (Int.repr 0)))
      | (Some c, Long) => par_eval_branch f l rsr rsw mw (Val.cmpl_bool c rsr#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end
  | Pcbu bt r l => 
      match cmpu_for_btest bt with
      | (Some c, Int) => par_eval_branch f l rsr rsw mw (Val_cmpu_bool c rsr#r (Vint (Int.repr 0)))
      | (Some c, Long) => par_eval_branch f l rsr rsw mw (Val_cmplu_bool c rsr#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end

(** Pseudo-instructions *)
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)
  end
  | None => Next (rsw#PC <- (rsr#PC)) mw
end.


Definition incrPC size_b (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC size_b).

(** parallel execution of the exit instruction of a bundle *)
Definition estep (f: function) ext size_b (rsr rsw: regset) (mw: mem) 
  := parexec_control f ext (incrPC size_b rsr) rsw mw.

Definition parexec_wio f bdy ext size_b (rs: regset) (m: mem): outcome :=
  match parexec_wio_body bdy rs rs m m with
  | Next rsw mw => estep f ext size_b rs rsw mw
  | Stuck => Stuck
  end.

(** non-deterministic (out-of-order writes) parallel execution of bundles *)
Definition parexec_bblock (f: function) (bundle: bblock) (rs: regset) (m: mem) (o: outcome): Prop :=
   exists bdy1 bdy2, Permutation (bdy1++bdy2) (body bundle) /\ 
      o=match parexec_wio f bdy1 (exit bundle) (Ptrofs.repr (size bundle)) rs m with
      | Next rsw mw => parexec_wio_body bdy2 rs rsw m mw
      | Stuck => Stuck
      end.

(** deterministic parallel (out-of-order writes) execution of bundles *)
Definition det_parexec (f: function) (bundle: bblock) (rs: regset) (m: mem) rs' m': Prop :=
   forall o, parexec_bblock f bundle rs m o -> o = Next rs' m'.


(* FIXME: comment not up-to-date *)
(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [X31].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)


(* FIXME - R16 and R32 are excluded *)
Definition preg_of (r: mreg) : preg :=
  match r with
  | R0  => GPR0  | R1  => GPR1  | R2  => GPR2  | R3  => GPR3  | R4  => GPR4
  | R5  => GPR5  | R6  => GPR6  | R7  => GPR7  | R8  => GPR8  | R9  => GPR9
  | R10 => GPR10 | R11 => GPR11 (* | R12 => GPR12 | R13 => GPR13 | R14  => GPR14 *)
  | R15 => GPR15 (* | R16 => GPR16 *) | R17 => GPR17 | R18 => GPR18 | R19  => GPR19
  | R20 => GPR20 | R21 => GPR21 | R22 => GPR22 | R23 => GPR23 | R24  => GPR24
  | R25 => GPR25 | R26 => GPR26 | R27 => GPR27 | R28 => GPR28 | R29  => GPR29
  | R30 => GPR30 | R31 => GPR31 (* | R32 => GPR32 *) | R33 => GPR33 | R34  => GPR34
  | R35 => GPR35 | R36 => GPR36 | R37 => GPR37 | R38 => GPR38 | R39  => GPR39
  | R40 => GPR40 | R41 => GPR41 | R42 => GPR42 | R43 => GPR43 | R44  => GPR44
  | R45 => GPR45 | R46 => GPR46 | R47 => GPR47 | R48 => GPR48 | R49  => GPR49
  | R50 => GPR50 | R51 => GPR51 | R52 => GPR52 | R53 => GPR53 | R54  => GPR54
  | R55 => GPR55 | R56 => GPR56 | R57 => GPR57 | R58 => GPR58 | R59  => GPR59
  | R60 => GPR60 | R61 => GPR61 | R62 => GPR62 | R63 => GPR63
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(* FIXME: comment not up-to-date *)
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


(** Looking up bblocks in a code sequence by position. *)
Fixpoint find_bblock (pos: Z) (lb: bblocks) {struct lb} : option bblock :=
  match lb with
  | nil => None
  | b :: il => 
    if zlt pos 0 then None  (* NOTE: It is impossible to branch inside a block *)
    else if zeq pos 0 then Some b
    else find_bblock (pos - (size b)) il
  end.


Inductive state: Type :=
  | State: regset -> mem -> state.

Definition nextblock (b:bblock) (rs: regset) :=
  incrPC (Ptrofs.repr (size b)) rs.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f bundle rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_bblock (Ptrofs.unsigned ofs) (fn_blocks f) = Some bundle ->
      det_parexec f bundle rs m rs' m' ->
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


(** parallel in-order writes execution of bundles *)
Definition parexec_wio_bblock (f: function) (b: bblock) (rs: regset) (m: mem): outcome :=
  parexec_wio f (body b) (exit b) (Ptrofs.repr (size b)) rs m.


Lemma parexec_bblock_write_in_order f b rs m:
   parexec_bblock f b rs m (parexec_wio_bblock f b rs m).
Proof.
   exists (body b). exists nil.
   constructor 1.
   - rewrite app_nil_r; auto.
   - unfold parexec_wio_bblock.
     destruct (parexec_wio f _ _ _); simpl; auto.
Qed.


Local Hint Resolve parexec_bblock_write_in_order: core.

Lemma det_parexec_write_in_order f b rs m rs' m':
   det_parexec f b rs m rs' m' -> parexec_wio_bblock f b rs m = Next rs' m'.
Proof.
   unfold det_parexec; auto.
Qed.

End RELSEM.

(** Execution of whole programs. *)

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

Lemma semantics_determinate p: determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
Ltac Det_WIO X :=
  match goal with
  | [ H: det_parexec _ _ _ _ _ _ _ |- _ ] =>
      exploit det_parexec_write_in_order; [ eapply H | idtac]; clear H; intro X
  | _ => idtac
  end.
  intros; constructor; simpl.
- (* determ *) intros s t1 s1 t2 s2 H H0. inv H; Det_WIO X1;
  inv H0; Det_WIO X2; Equalities.
  + split. constructor. auto. 
  + unfold parexec_wio_bblock, parexec_wio in X1. destruct (parexec_wio_body _ _ _ _ _ _); try discriminate.
    rewrite H8 in X1. discriminate.
  + unfold parexec_wio_bblock, parexec_wio in X2. destruct (parexec_wio_body _ _ _ _ _ _); try discriminate.
    rewrite H4 in X2. discriminate.
  + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
    exploit external_call_determ. eexact H6. eexact H13. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
    exploit external_call_determ. eexact H3. eexact H8. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  intros s1 s2 H H0; inv H; inv H0; f_equal; congruence.
- (* final no step *)
  intros s r H; assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  intros s r1 r2 H H0; inv H; inv H0. congruence.
Qed.
