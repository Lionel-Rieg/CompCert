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
Require Import Errors.

(** * Abstract syntax *)

(** General Purpose registers.
*)

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

(** basic register *)
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

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

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

(** * Instructions *)

Definition label := positive.

(* FIXME - rewrite the comment *)
(** A note on immediates: there are various constraints on immediate
  operands to K1c instructions.  We do not attempt to capture these
  restrictions in the abstract syntax nor in the semantics.  The
  assembler will emit an error if immediate operands exceed the
  representable range.  Of course, our K1c generator (file
  [Asmgen]) is careful to respect this range. *)

(** Instructions to be expanded in control-flow 
*)
Inductive ex_instruction : Type :=
  (* Pseudo-instructions *)
(*| Ploadsymbol_high (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the high part of the address of a symbol *)
  | Pbtbl   (r: ireg)  (tbl: list label)            (**r N-way branch through a jump table *) *)

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

  (* Pgoto is for tailcalls, Pj_l is for jumping to a particular label *)
  | Pgoto   (l: label)                              (**r goto *)
  | Pigoto  (r: ireg)                               (**r goto from register *)
  | Pj_l    (l: label)                              (**r jump to label *)

  (* Conditional branches *)
  | Pcb     (bt: btest) (r: ireg) (l: label)        (**r branch based on btest *)
  | Pcbu    (bt: btest) (r: ireg) (l: label)        (**r branch based on btest with unsigned semantics *)
.

(** Loads **)
Inductive load_name_rro : Type :=
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
  | PLoadRRO   (i: load_name_rro) (rd: ireg) (ra: ireg) (ofs: offset)
.

Coercion PLoadRRO:       load_name_rro        >-> Funclass.

(** Stores **)
Inductive store_name_rro : Type :=
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
  | PStoreRRO  (i: store_name_rro) (rs: ireg) (ra: ireg) (ofs: offset)
.

Coercion PStoreRRO:       store_name_rro        >-> Funclass.

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

  | Pfabsd                                          (**r float absolute double *)
  | Pfabsw                                          (**r float absolute word *)
  | Pfnegd                                          (**r float negate double *)
  | Pfnegw                                          (**r float negate word *)
  | Pfnarrowdw                                      (**r float narrow 64 -> 32 bits *)
  | Pfwidenlwd                                      (**r Floating Point widen from 32 bits to 64 bits *)
  | Pfloatwrnsz                                     (**r Floating Point conversion from integer (int -> SINGLE) *)
  | Pfloatuwrnsz                                    (**r Floating Point conversion from integer (unsigned int -> SINGLE) *)
  | Pfloatudrnsz                                    (**r Floating Point Conversion from integer (unsigned long -> float) *)
  | Pfloatudrnsz_i32                                (**r Floating Point Conversion from integer (unsigned int -> float) *)
  | Pfloatdrnsz                                     (**r Floating Point Conversion from integer (long -> float) *)
  | Pfloatdrnsz_i32                                 (**r Floating Point Conversion from integer (int -> float) *)
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
  | Psubw                                           (**r sub word *)
  | Pmulw                                           (**r mul word *)
  | Pandw                                           (**r and word *)
  | Pnandw                                          (**r nand word *)
  | Porw                                            (**r or word *)
  | Pnorw                                           (**r nor word *)
  | Pxorw                                           (**r xor word *)
  | Pnxorw                                          (**r nxor word *)
  | Psraw                                           (**r shift right arithmetic word *)
  | Psrlw                                           (**r shift right logical word *)
  | Psllw                                           (**r shift left logical word *)

  | Paddl                                           (**r add long *)
  | Psubl                                           (**r sub long *)
  | Pandl                                           (**r and long *)
  | Pnandl                                          (**r nand long *)
  | Porl                                            (**r or long *)
  | Pnorl                                           (**r nor long *)
  | Pxorl                                           (**r xor long *)
  | Pnxorl                                          (**r nxor long *)
  | Pmull                                           (**r mul long (low part) *)
  | Pslll                                           (**r shift left logical long *)
  | Psrll                                           (**r shift right logical long *)
  | Psral                                           (**r shift right arithmetic long *)

  | Pfaddd                                          (**r float add double *)
  | Pfaddw                                          (**r float add word *)
  | Pfsbfd                                          (**r float sub double *)
  | Pfsbfw                                          (**r float sub word *)
  | Pfmuld                                          (**r float multiply double *)
  | Pfmulw                                          (**r float multiply word *)
.

Inductive arith_name_rri32 : Type :=
  | Pcompiw (it: itest)                             (**r comparison imm word *)

  | Paddiw                                          (**r add imm word *)
  | Pandiw                                          (**r and imm word *)
  | Pnandiw                                         (**r nand imm word *)
  | Poriw                                           (**r or imm word *)
  | Pnoriw                                          (**r nor imm word *)
  | Pxoriw                                          (**r xor imm word *)
  | Pnxoriw                                         (**r nxor imm word *)
  | Psraiw                                          (**r shift right arithmetic imm word *)
  | Psrliw                                          (**r shift right logical imm word *)
  | Pslliw                                          (**r shift left logical imm word *)
  | Proriw                                          (**r rotate right imm word *)
  | Psllil                                          (**r shift left logical immediate long *)
  | Psrlil                                          (**r shift right logical immediate long *)
  | Psrail                                          (**r shift right arithmetic immediate long *)
.

Inductive arith_name_rri64 : Type :=
  | Pcompil (it: itest)                             (**r comparison imm long *)
  | Paddil                                          (**r add immediate long *) 
  | Pandil                                          (**r and immediate long *) 
  | Pnandil                                         (**r nand immediate long *) 
  | Poril                                           (**r or immediate long *) 
  | Pnoril                                          (**r nor immediate long *) 
  | Pxoril                                          (**r xor immediate long *) 
  | Pnxoril                                         (**r nxor immediate long *) 
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
.

Coercion PArithR:       arith_name_r        >-> Funclass.
Coercion PArithRR:      arith_name_rr       >-> Funclass.
Coercion PArithRI32:    arith_name_ri32     >-> Funclass.
Coercion PArithRI64:    arith_name_ri64     >-> Funclass.
Coercion PArithRF32:    arith_name_rf32     >-> Funclass.
Coercion PArithRF64:    arith_name_rf64     >-> Funclass.
Coercion PArithRRR:     arith_name_rrr      >-> Funclass.
Coercion PArithRRI32:   arith_name_rri32    >-> Funclass.
Coercion PArithRRI64:   arith_name_rri64    >-> Funclass.

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


(** * Definition of a bblock *)

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

Definition builtin_aloneb (body: list basic) (exit: option control) :=
  match exit with
  | Some (PExpand (Pbuiltin _ _ _)) =>
    match body with
    | nil => true
    | _ => false
    end
  | _ => true
  end.

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
    + exploreInst.
        simpl. contradiction.
        discriminate.
    + intros. discriminate.
Qed.

Definition wf_bblockb (body: list basic) (exit: option control) :=
  (non_empty_bblockb body exit) && (builtin_aloneb body exit).

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

(** A bblock is well-formed if he contains at least one instruction,
    and if there is a builtin then it must be alone in this bblock. *)

Record bblock := mk_bblock {
  header: list label;
  body: list basic;
  exit: option control;
  correct: Is_true (wf_bblockb body exit)
}.

Ltac bblock_auto_correct := (apply non_empty_bblock_refl; try discriminate; try (left; discriminate); try (right; discriminate)).
(* Local Obligation Tactic := bblock_auto_correct. *)

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


(* FIXME: redundant with definition in Machblock *)
Definition length_opt {A} (o: option A) : nat :=
  match o with
  | Some o => 1
  | None => 0
  end.

(* WARNING: the notion of size is not the same than in Machblock !
   We ignore labels here...
   The result is in Z to be compatible with operations on PC
*)
Definition size (b:bblock): Z := Z.of_nat (length (body b) + length_opt (exit b)).
(*   match (body b, exit b) with
  | (nil, None) => 1
  | _ => 
  end.
 *)

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
(*     rewrite eq. (* inversion COR. *) (* inversion H. *)
  - assert ((length b > 0)%nat). apply length_nonil. auto.
    omega.
  - destruct e; simpl; try omega. contradict H; simpl; auto.
 *)Qed.


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

(** * Utility for Asmblockgen *)

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

(** This definition is not used anymore *)
(* Program Definition bblock_basic_ctl (c: list basic) (i: option control) :=
  match i with
  | Some i => {| header:=nil; body:=c; exit:=Some i |}
  | None =>
    match c with
    | _::_ => {| header:=nil; body:=c; exit:=None |}
    | nil => {| header:=nil; body:=Pnop::nil; exit:=None |}
    end
  end.
Next Obligation.
  bblock_auto_correct.
Qed. Next Obligation.
  bblock_auto_correct.
Qed. *)


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

(* TODO: Is it still useful ?? *)


(** Assigning multiple registers *)

(* Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.
 *)
(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.


(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome {rgset}: Type :=
  | Next (rs:rgset) (m:mem)
  | Stuck.
Arguments outcome: clear implicits.


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
  | ITall
  | ITnall
  | ITany
  | ITnone => Vundef
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

(** Execution of arith instructions *)

Variable ge: genv.

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
  | Pfnegd => Val.negf v
  | Pfnegw => Val.negfs v
  | Pfabsd => Val.absf v
  | Pfabsw => Val.absfs v
  | Pfnarrowdw => Val.singleoffloat v
  | Pfwidenlwd => Val.floatofsingle v
  | Pfloatwrnsz => match Val.singleofint v with Some f => f | _ => Vundef end
  | Pfloatuwrnsz => match Val.singleofintu v with Some f => f | _ => Vundef end
  | Pfloatudrnsz => match Val.floatoflongu v with Some f => f | _ => Vundef end
  | Pfloatdrnsz => match Val.floatoflong v with Some f => f | _ => Vundef end
  | Pfloatudrnsz_i32 => match Val.floatofintu v with Some f => f | _ => Vundef end
  | Pfloatdrnsz_i32 => match Val.floatofint v with Some f => f | _ => Vundef end
  | Pfixedwrzz => match Val.intofsingle v with Some i => i | _ => Vundef end
  | Pfixeduwrzz => match Val.intuofsingle v with Some i => i | _ => Vundef end
  | Pfixeddrzz => match Val.longoffloat v with Some i => i | _ => Vundef end
  | Pfixedudrzz => match Val.longuoffloat v with Some i => i | _ => Vundef end
  | Pfixeddrzz_i32 => match Val.intoffloat v with Some i => i | _ => Vundef end
  | Pfixedudrzz_i32 => match Val.intuoffloat v with Some i => i | _ => Vundef end
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
  | Psrlw  => Val.shru v1 v2
  | Psraw  => Val.shr  v1 v2
  | Psllw  => Val.shl  v1 v2

  | Paddl => Val.addl v1 v2
  | Psubl => Val.subl v1 v2
  | Pandl => Val.andl v1 v2
  | Pnandl => Val.notl (Val.andl v1 v2)
  | Porl  => Val.orl  v1 v2
  | Pnorl  => Val.notl (Val.orl  v1 v2)
  | Pxorl  => Val.xorl  v1 v2
  | Pnxorl  => Val.notl (Val.xorl  v1 v2)
  | Pmull => Val.mull v1 v2
  | Pslll => Val.shll v1 v2
  | Psrll => Val.shrlu v1 v2
  | Psral => Val.shrl v1 v2

  | Pfaddd => Val.addf v1 v2
  | Pfaddw => Val.addfs v1 v2
  | Pfsbfd => Val.subf v1 v2
  | Pfsbfw => Val.subfs v1 v2
  | Pfmuld => Val.mulf v1 v2
  | Pfmulw => Val.mulfs v1 v2
  end.

Definition arith_eval_rri32 n v i :=
  match n with
  | Pcompiw c => compare_int c v (Vint i)
  | Paddiw  => Val.add   v (Vint i)
  | Pandiw  => Val.and   v (Vint i)
  | Pnandiw => Val.notint (Val.and  v (Vint i))
  | Poriw   => Val.or    v (Vint i)
  | Pnoriw  => Val.notint (Val.or v (Vint i))
  | Pxoriw  => Val.xor   v (Vint i)
  | Pnxoriw => Val.notint (Val.xor v (Vint i))
  | Psraiw  => Val.shr   v (Vint i)
  | Psrliw  => Val.shru  v (Vint i)
  | Pslliw  => Val.shl   v (Vint i)
  | Proriw  => Val.ror   v (Vint i)
  | Psllil  => Val.shll  v (Vint i)
  | Psrlil  => Val.shrlu v (Vint i)
  | Psrail  => Val.shrl  v (Vint i)
  end.

Definition arith_eval_rri64 n v i :=
  match n with
  | Pcompil c => compare_long c v (Vlong i)
  | Paddil  => Val.addl v (Vlong i)
  | Pandil  => Val.andl v (Vlong i)
  | Pnandil  => Val.notl (Val.andl v (Vlong i))
  | Poril   => Val.orl  v (Vlong i)
  | Pnoril   => Val.notl (Val.orl  v (Vlong i))
  | Pxoril  => Val.xorl  v (Vlong i)
  | Pnxoril  => Val.notl (Val.xorl  v (Vlong i))
  end.

Definition exec_arith_instr (ai: ar_instruction) (rs: regset): regset :=
  match ai with
  | PArithR n d => rs#d <- (arith_eval_r n)

  | PArithRR n d s => rs#d <- (arith_eval_rr n rs#s)

  | PArithRI32 n d i => rs#d <- (arith_eval_ri32 n i)
  | PArithRI64 n d i => rs#d <- (arith_eval_ri64 n i)
  | PArithRF32 n d i => rs#d <- (arith_eval_rf32 n i)
  | PArithRF64 n d i => rs#d <- (arith_eval_rf64 n i)

  | PArithRRR n d s1 s2 => rs#d <- (arith_eval_rrr n rs#s1 rs#s2)

  | PArithRRI32 n d s i => rs#d <- (arith_eval_rri32 n rs#s i)

  | PArithRRI64 n d s i => rs#d <- (arith_eval_rri64 n rs#s i)
  end.

(** * load/store *)

(** Auxiliaries for memory accesses *)

Definition eval_offset (ofs: offset) : res ptrofs :=
  match ofs with
  | Ofsimm n => OK n
  | Ofslow id delta => 
      match (Genv.symbol_address ge id delta) with
      | Vptr b ofs => OK ofs
      | _ => Error (msg "Asmblock.eval_offset")
      end
  end.

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: ireg) (a: ireg) (ofs: offset) :=
  match (eval_offset ofs) with
  | OK ptr =>
    match Mem.loadv chunk m (Val.offset_ptr (rs a) ptr) with
    | None => Stuck
    | Some v => Next (rs#d <- v) m
    end
  | _ => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: ireg) (a: ireg) (ofs: offset) :=
  match (eval_offset ofs) with
  | OK ptr => 
    match Mem.storev chunk m (Val.offset_ptr (rs a) ptr) (rs s) with
    | None => Stuck
    | Some m' => Next rs m'
    end
  | _ => Stuck
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

Definition exec_basic_instr (bi: basic) (rs: regset) (m: mem) : outcome regset :=
  match bi with
  | PArith ai => Next (exec_arith_instr ai rs) m

  | PLoadRRO n d a ofs => exec_load (load_chunk n) rs m d a ofs

  | PStoreRRO n s a ofs => exec_store (store_chunk n) rs m s a ofs

  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (rs #FP <- (rs SP) #SP <- sp #RTMP <- Vundef) m2
      end

  | Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (rs#SP <- v #RTMP <- Vundef) m'
              end
          | _ => Stuck
          end
      end
  | Pget rd ra =>
    match ra with
    | RA => Next (rs#rd <- (rs#ra)) m
    | _  => Stuck
    end
  | Pset ra rd =>
    match ra with
    | RA => Next (rs#ra <- (rs#rd)) m
    | _  => Stuck
    end
  | Pnop => Next rs m
end.

Fixpoint exec_body (body: list basic) (rs: regset) (m: mem): outcome regset :=
  match body with
  | nil => Next rs m
  | bi::body' => 
     match exec_basic_instr bi rs m with
     | Next rs' m' => exec_body body' rs' m'
     | Stuck => Stuck
     end
  end.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextblock]) or branching to a label ([goto_label]). *)

Definition nextblock (b:bblock) (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC (Ptrofs.repr (size b))).

(** Looking up bblocks in a code sequence by position. *)
Fixpoint find_bblock (pos: Z) (lb: bblocks) {struct lb} : option bblock :=
  match lb with
  | nil => None
  | b :: il => 
    if zlt pos 0 then None  (* NOTE: It is impossible to branch inside a block *)
    else if zeq pos 0 then Some b
    else find_bblock (pos - (size b)) il
  end.


(** Position corresponding to a label *)

(** TODO: redundant w.r.t Machblock *)
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

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) : outcome regset :=
  match label_pos lbl 0 (fn_blocks f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Evaluating a branch 

Warning: in m PC is assumed to be already pointing on the next instruction !

*)
Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome regset :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next rs m
    | None => Stuck
  end.


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

Definition exec_control (f: function) (oc: option control) (rs: regset) (m: mem) : outcome regset :=
  match oc with
  | Some ic =>
(** Get/Set system registers *)
  match ic with


(** Branch Control Unit instructions *)
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  | Pcall s =>
      Next (rs#RA <- (rs#PC) #PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Picall r =>
      Next (rs#RA <- (rs#PC) #PC <- (rs#r)) m
  | Pgoto s =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pigoto r =>
      Next (rs#PC <- (rs#r)) m
  | Pj_l l =>
      goto_label f l rs m
  | Pcb bt r l =>
      match cmp_for_btest bt with
      | (Some c, Int)  => eval_branch f l rs m (Val.cmp_bool c rs#r (Vint (Int.repr 0)))
      | (Some c, Long) => eval_branch f l rs m (Val.cmpl_bool c rs#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end
  | Pcbu bt r l => 
      match cmpu_for_btest bt with
      | (Some c, Int) => eval_branch f l rs m (Val_cmpu_bool c rs#r (Vint (Int.repr 0)))
      | (Some c, Long) => eval_branch f l rs m (Val_cmplu_bool c rs#r (Vlong (Int64.repr 0)))
      | (None, _) => Stuck
      end


(** Pseudo-instructions *)
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)
  end
  | None => Next rs m
end.

Definition exec_bblock (f: function) (b: bblock) (rs0: regset) (m: mem) : outcome regset :=
  match exec_body (body b) rs0 m with
  | Next rs' m' =>
    let rs1 := nextblock b rs' in exec_control f (exit b) rs1 m'
  | Stuck => Stuck
  end.

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


(** TODO
 * For now, we consider a builtin is alone in a basic block.
 * Perhaps there is a way to avoid that ?
 *)

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
  + split. constructor. auto.
  + unfold exec_bblock in H4. destruct (exec_body _ _ _ _); try discriminate.
    rewrite H9 in H4. discriminate.
  + unfold exec_bblock in H13. destruct (exec_body _ _ _ _); try discriminate.
    rewrite H4 in H13. discriminate.
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
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

Definition data_preg (r: preg) : bool :=
  match r with
  | RA  => false
  | IR GPRA => false
  | IR RTMP => false
  | IR _   => true
  | PC     => false
  end.

(** Determinacy of the [Asm] semantics. *)

(* TODO.

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
*)
