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

(** * Abstract syntax for K1c textual assembly language.

    Each emittable instruction is defined here. ';;' is also defined as an instruction.
    The goal of this representation is to stay compatible with the rest of the generic backend of CompCert
    We define [unfold : list bblock -> list instruction]
    An Asm function is then defined as : [fn_sig], [fn_blocks], [fn_code], and a proof of [unfold fn_blocks = fn_code]
    [fn_code] has no semantic. Instead, the semantic of Asm is given by using the AsmVLIW semantic on [fn_blocks] *)

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
Require Import Asmvliw.
Require Import Linking.
Require Import Errors.

(** Definitions for OCaml code *)
Definition label := positive.
Definition preg := preg.

Inductive addressing : Type :=
  | AOff (ofs: offset)
  | AReg (ro: ireg)
  | ARegXS (ro: ireg)
.

(** Syntax *)
Inductive instruction : Type :=
  (** pseudo instructions *)
  | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)               (**r deallocate stack frame and restore previous frame *)
  | Plabel  (lbl: label)                            (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the address of a symbol *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction   (**r built-in function (pseudo) *)
  | Psemi                                           (**r semi colon separating bundles *)
  | Pnop                                            (**r instruction that does nothing *)

  (** Control flow instructions *)
  | Pget    (rd: ireg) (rs: preg)                   (**r get system register *)
  | Pset    (rd: preg) (rs: ireg)                   (**r set system register *)
  | Pret                                            (**r return *)
  | Pcall   (l: label)                              (**r function call *)
  | Picall  (rs: ireg)                              (**r function call on register *)
  (* Pgoto is for tailcalls, Pj_l is for jumping to a particular label *)
  | Pgoto   (l: label)                              (**r goto *)
  | Pigoto  (rs: ireg)                              (**r goto from register *)
  | Pj_l    (l: label)                              (**r jump to label *)
  | Pcb     (bt: btest) (r: ireg) (l: label)        (**r branch based on btest *)
  | Pcbu    (bt: btest) (r: ireg) (l: label)        (**r branch based on btest with unsigned semantics *)
  | Pjumptable (r: ireg) (labels: list label)

  (* For builtins *)
  | Ploopdo (count: ireg) (loopend: label)
  | Pgetn   (n: int) (dst: ireg)
  | Psetn   (n: int) (src: ireg)
  | Pwfxl   (n: int) (src: ireg)
  | Pwfxm   (n: int) (src: ireg)
  | Pldu    (dst: ireg) (addr: ireg)
  | Plbzu    (dst: ireg) (addr: ireg)
  | Plhzu    (dst: ireg) (addr: ireg)
  | Plwzu    (dst: ireg) (addr: ireg)
  | Pawait
  | Psleep
  | Pstop
  | Pbarrier
  | Pfence
  | Pdinval
  | Pdinvall (addr: ireg)
  | Pdtouchl (addr: ireg)
  | Piinval
  | Piinvals (addr: ireg)
  | Pitouchl (addr: ireg)
  | Pdzerol (addr: ireg)
(*| Pafaddd (addr: ireg) (incr_res: ireg)
  | Pafaddw (addr: ireg) (incr_res: ireg) *) (* see #157 *)
  | Palclrd (dst: ireg) (addr: ireg)
  | Palclrw (dst: ireg) (addr: ireg)
  | Pclzll (rd rs: ireg)
  | Pstsud (rd rs1 rs2: ireg)
            
  (** Loads **)
  | Plb     (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load byte *)
  | Plbu    (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load byte unsigned *)
  | Plh     (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load half word *)
  | Plhu    (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load half word unsigned *)
  | Plw     (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load int32 *)
  | Plw_a   (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load any32 *)
  | Pld     (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load int64 *)
  | Pld_a   (trap: trapping_mode) (rd: ireg) (ra: ireg) (ofs: addressing)     (**r load any64 *)
  | Pfls    (trap: trapping_mode) (rd: freg) (ra: ireg) (ofs: addressing)     (**r load float *)
  | Pfld    (trap: trapping_mode) (rd: freg) (ra: ireg) (ofs: addressing)    (**r load 64-bit float *)
  | Plq     (rs: gpreg_q) (ra: ireg) (ofs: addressing)  (**r load 2*64-bit *)
  | Plo     (rs: gpreg_o) (ra: ireg) (ofs: addressing)  (**r load 4*64-bit *)

  (** Stores **)
  | Psb     (rs: ireg) (ra: ireg) (ofs: addressing)     (**r store byte *)
  | Psh     (rs: ireg) (ra: ireg) (ofs: addressing)     (**r store half byte *)
  | Psw     (rs: ireg) (ra: ireg) (ofs: addressing)     (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (ofs: addressing)     (**r store any32 *)
  | Psd     (rs: ireg) (ra: ireg) (ofs: addressing)     (**r store int64 *)
  | Psd_a   (rs: ireg) (ra: ireg) (ofs: addressing)     (**r store any64 *)
  | Pfss    (rs: freg) (ra: ireg) (ofs: addressing)     (**r store float *)
  | Pfsd    (rs: freg) (ra: ireg) (ofs: addressing)    (**r store 64-bit float *)

  | Psq     (rs: gpreg_q) (ra: ireg) (ofs: addressing)  (**r store 2*64-bit *)
  | Pso     (rs: gpreg_o) (ra: ireg) (ofs: addressing)  (**r store 2*64-bit *)

  (** Arith RR *)
  | Pmv     (rd rs: ireg)                           (**r register move *)
  | Pnegw   (rd rs: ireg)                           (**r negate word *)
  | Pnegl   (rd rs: ireg)                           (**r negate long *)
  | Pcvtl2w (rd rs: ireg)                           (**r Convert Long to Word *)
  | Psxwd   (rd rs: ireg)                           (**r Sign Extend Word to Double Word *)
  | Pzxwd   (rd rs: ireg)                           (**r Zero Extend Word to Double Word *)

  | Pextfz  (rd : ireg) (rs : ireg) (stop : Z) (start : Z) (**r extract bitfields unsigned *)
  | Pextfs  (rd : ireg) (rs : ireg) (stop : Z) (start : Z) (**r extract bitfields signed *)

  | Pextfzl  (rd : ireg) (rs : ireg) (stop : Z) (start : Z) (**r extract bitfields unsigned *)
  | Pextfsl  (rd : ireg) (rs : ireg) (stop : Z) (start : Z) (**r extract bitfields signed *)

  | Pinsf  (rd : ireg) (rs : ireg) (stop : Z) (start : Z) (**r insert bitfield *)
  | Pinsfl  (rd : ireg) (rs : ireg) (stop : Z) (start : Z) (**r insert bitfield *)

  | Pfabsd  (rd rs: ireg)                           (**r float absolute double *)
  | Pfabsw  (rd rs: ireg)                           (**r float absolute word *)
  | Pfnegd  (rd rs: ireg)                           (**r float negate double *)
  | Pfnegw  (rd rs: ireg)                           (**r float negate word *)
  | Pfnarrowdw (rd rs: ireg)                        (**r float narrow 64 -> 32 bits *)
  | Pfwidenlwd (rd rs: ireg)                        (**r float widen 32 -> 64 bits *)
  | Pfloatwrnsz (rd rs: ireg)                       (**r Floating Point Conversion from integer (32 -> 32) *)
  | Pfloatuwrnsz (rd rs: ireg)                      (**r Floating Point Conversion from integer (u32 -> 32) *)
  | Pfloatudrnsz (rd rs: ireg)                       (**r Floating Point Conversion from unsigned integer (64 bits) *)
  | Pfloatdrnsz (rd rs: ireg)                       (**r Floating Point Conversion from integer (64 bits) *)
  | Pfixedwrzz (rd rs: ireg)                        (**r Integer conversion from floating point *)
  | Pfixeduwrzz (rd rs: ireg)                        (**r Integer conversion from floating point (f32 -> 32 bits unsigned *)
  | Pfixeddrzz (rd rs: ireg)                        (**r Integer conversion from floating point (i64 -> 64 bits) *)
  | Pfixeddrzz_i32 (rd rs: ireg)                        (**r Integer conversion from floating point (i32 -> f64) *)
  | Pfixedudrzz (rd rs: ireg)                        (**r unsigned Integer conversion from floating point (u64 -> 64 bits) *)
  | Pfixedudrzz_i32 (rd rs: ireg)                        (**r unsigned Integer conversion from floating point (u32 -> 64 bits) *)

  (** Arith RI32 *)
  | Pmake   (rd: ireg) (imm: int)                   (**r load immediate *)

  (** Arith RI64 *)
  | Pmakel  (rd: ireg) (imm: int64)                 (**r load immediate long *)

  (** Arith RF32 *)
  | Pmakefs (rd: ireg) (imm: float32)

  (** Arith RF64 *)
  | Pmakef  (rd: ireg) (imm: float)

  (** Arith RRR *)
  | Pcompw  (it: itest) (rd rs1 rs2: ireg)          (**r comparison word *)
  | Pcompl  (it: itest) (rd rs1 rs2: ireg)          (**r comparison long *)
  | Pfcompw (ft: ftest) (rd rs1 rs2: ireg)          (**r comparison float *)
  | Pfcompl (ft: ftest) (rd rs1 rs2: ireg)          (**r comparison float64 *)

  | Paddw               (rd rs1 rs2: ireg)          (**r add word *)
  | Paddxw (shift : shift1_4)  (rd rs1 rs2: ireg)          (**r add word *)
  | Psubw               (rd rs1 rs2: ireg)          (**r sub word *)
  | Prevsubxw (shift : shift1_4)  (rd rs1 rs2: ireg)          (**r add word *)
  | Pmulw               (rd rs1 rs2: ireg)          (**r mul word *)
  | Pandw               (rd rs1 rs2: ireg)          (**r and word *)
  | Pnandw              (rd rs1 rs2: ireg)          (**r nand word *)
  | Porw                (rd rs1 rs2: ireg)          (**r or word *)
  | Pnorw               (rd rs1 rs2: ireg)          (**r nor word *)
  | Pxorw               (rd rs1 rs2: ireg)          (**r xor word *)
  | Pnxorw              (rd rs1 rs2: ireg)          (**r xor word *)
  | Pandnw              (rd rs1 rs2: ireg)          (**r andn word *)
  | Pornw               (rd rs1 rs2: ireg)          (**r orn word *)
  | Psraw               (rd rs1 rs2: ireg)          (**r shift right arithmetic word *)
  | Psrxw               (rd rs1 rs2: ireg)          (**r shift right arithmetic word round to 0*)
  | Psrlw               (rd rs1 rs2: ireg)          (**r shift right logical word *)
  | Psllw               (rd rs1 rs2: ireg)          (**r shift left logical word *)
  | Pmaddw              (rd rs1 rs2: ireg)          (**r multiply-add words *)
  | Pmsubw              (rd rs1 rs2: ireg)          (**r multiply-add words *)
  | Pfmaddfw            (rd rs1 rs2: ireg)          (**r float fused multiply-add words *)
  | Pfmsubfw            (rd rs1 rs2: ireg)          (**r float fused multiply-subtract words *)
  | Pfmaddfl            (rd rs1 rs2: ireg)          (**r float fused multiply-add longs *)
  | Pfmsubfl            (rd rs1 rs2: ireg)          (**r float fused multiply-subtract longs *)

  | Paddl               (rd rs1 rs2: ireg)          (**r add long *)
  | Paddxl (shift : shift1_4)  (rd rs1 rs2: ireg)          (**r add long shift *)
  | Psubl               (rd rs1 rs2: ireg)          (**r sub long *)
  | Prevsubxl (shift : shift1_4)  (rd rs1 rs2: ireg)          (**r sub long shift *)
  | Pandl               (rd rs1 rs2: ireg)          (**r and long *)
  | Pnandl              (rd rs1 rs2: ireg)          (**r nand long *)
  | Porl                (rd rs1 rs2: ireg)          (**r or long *)
  | Pnorl               (rd rs1 rs2: ireg)          (**r nor long *)
  | Pxorl               (rd rs1 rs2: ireg)          (**r xor long *)
  | Pnxorl              (rd rs1 rs2: ireg)          (**r nxor long *)
  | Pandnl              (rd rs1 rs2: ireg)          (**r andn long *)
  | Pornl               (rd rs1 rs2: ireg)          (**r orn long *)
  | Pmull               (rd rs1 rs2: ireg)          (**r mul long (low part) *)
  | Pslll               (rd rs1 rs2: ireg)          (**r shift left logical long *)
  | Psrll               (rd rs1 rs2: ireg)          (**r shift right logical long *)
  | Psral               (rd rs1 rs2: ireg)          (**r shift right arithmetic long *)
  | Psrxl               (rd rs1 rs2: ireg)          (**r shift right arithmetic long round to 0*)
  | Pmaddl              (rd rs1 rs2: ireg)          (**r multiply-add long *)
  | Pmsubl              (rd rs1 rs2: ireg)          (**r multiply-add long *)

  | Pfaddd              (rd rs1 rs2: ireg)          (**r Float addition double *)
  | Pfaddw              (rd rs1 rs2: ireg)          (**r Float addition word *)
  | Pfsbfd              (rd rs1 rs2: ireg)          (**r Float sub double *)
  | Pfsbfw              (rd rs1 rs2: ireg)          (**r Float sub word *)
  | Pfmuld              (rd rs1 rs2: ireg)          (**r Float mul double *)
  | Pfmulw              (rd rs1 rs2: ireg)          (**r Float mul word *)
  | Pfmind              (rd rs1 rs2: ireg)          (**r Float min double *)
  | Pfminw              (rd rs1 rs2: ireg)          (**r Float min word *)
  | Pfmaxd              (rd rs1 rs2: ireg)          (**r Float max double *)
  | Pfmaxw              (rd rs1 rs2: ireg)          (**r Float max word *)
  | Pfinvw              (rd rs1: ireg)              (**r Float invert word *)
                        
  (** Arith RRI32 *)
  | Pcompiw (it: itest) (rd rs: ireg) (imm: int)    (**r comparison imm word *)

  | Paddiw              (rd rs: ireg) (imm: int)    (**r add imm word *)
  | Paddxiw (shift : shift1_4) (rd rs: ireg) (imm: int)    (**r add imm word *)
  | Prevsubiw              (rd rs: ireg) (imm: int)    (**r subtract imm word *)
  | Prevsubxiw (shift : shift1_4) (rd rs: ireg) (imm: int)    (**r subtract imm word *)
  | Pmuliw              (rd rs: ireg) (imm: int)    (**r mul imm word *)
  | Pandiw              (rd rs: ireg) (imm: int)    (**r and imm word *)
  | Pnandiw             (rd rs: ireg) (imm: int)    (**r nand imm word *)
  | Poriw               (rd rs: ireg) (imm: int)    (**r or imm word *)
  | Pnoriw              (rd rs: ireg) (imm: int)    (**r nor imm word *)
  | Pxoriw              (rd rs: ireg) (imm: int)    (**r xor imm word *)
  | Pnxoriw             (rd rs: ireg) (imm: int)    (**r nxor imm word *)
  | Pandniw             (rd rs: ireg) (imm: int)    (**r andn imm word *)
  | Porniw              (rd rs: ireg) (imm: int)    (**r orn imm word *)
  | Psraiw              (rd rs: ireg) (imm: int)    (**r shift right arithmetic imm word *)
  | Psrxiw              (rd rs: ireg) (imm: int)    (**r shift right arithmetic imm word round to 0*)
  | Psrliw              (rd rs: ireg) (imm: int)    (**r shift right logical imm word *)
  | Pslliw              (rd rs: ireg) (imm: int)    (**r shift left logical imm word *)
  | Proriw              (rd rs: ireg) (imm: int)    (**r rotate right imm word *) 
  | Pmaddiw             (rd rs: ireg) (imm: int)    (**r multiply add imm word *)
  | Psllil              (rd rs: ireg) (imm: int)    (**r shift left logical immediate long *)
  | Psrxil              (rd rs: ireg) (imm: int)    (**r shift right arithmetic imm word round to 0*)
  | Psrlil              (rd rs: ireg) (imm: int)    (**r shift right logical immediate long *)
  | Psrail              (rd rs: ireg) (imm: int)    (**r shift right arithmetic immediate long *)

  (** Arith RRI64 *)
  | Pcompil (it: itest) (rd rs: ireg) (imm: int64)  (**r comparison imm long *)
  | Paddil              (rd rs: ireg) (imm: int64)  (**r add immediate long *) 
  | Paddxil (shift : shift1_4) (rd rs: ireg) (imm: int64)  (**r add immediate long *) 
  | Prevsubil              (rd rs: ireg) (imm: int64)  (**r subtract imm long *)
  | Prevsubxil (shift : shift1_4) (rd rs: ireg) (imm: int64)  (**r subtract imm long *)
  | Pmulil              (rd rs: ireg) (imm: int64)  (**r add immediate long *) 
  | Pandil              (rd rs: ireg) (imm: int64)  (**r and immediate long *) 
  | Pnandil             (rd rs: ireg) (imm: int64)  (**r and immediate long *) 
  | Poril               (rd rs: ireg) (imm: int64)  (**r or immediate long *) 
  | Pnoril              (rd rs: ireg) (imm: int64)  (**r and immediate long *) 
  | Pxoril              (rd rs: ireg) (imm: int64)  (**r xor immediate long *)
  | Pnxoril             (rd rs: ireg) (imm: int64)  (**r xor immediate long *)
  | Pandnil             (rd rs: ireg) (imm: int64)  (**r andn long *)
  | Pornil              (rd rs: ireg) (imm: int64)  (**r orn long *)
  | Pmaddil             (rd rs: ireg) (imm: int64)  (**r multiply add imm long *)
  | Pcmove (bt: btest) (rcond rd rs : ireg) (** conditional move *) 
  | Pcmoveu (bt: btest) (rcond rd rs : ireg) (** conditional move, unsigned semantics *) 
  | Pcmoveiw (bt: btest) (rcond rd : ireg) (imm: int) (** conditional move *) 
  | Pcmoveuiw (bt: btest) (rcond rd : ireg) (imm: int) (** conditional move, unsigned semantics *) 
  | Pcmoveil (bt: btest) (rcond rd : ireg) (imm: int64) (** conditional move *) 
  | Pcmoveuil (bt: btest) (rcond rd : ireg) (imm: int64) (** conditional move, unsigned semantics *) 
.

(** Correspondance between Asmblock and Asm *)

Definition control_to_instruction (c: control) :=
  match c with
  | PExpand (Asmvliw.Pbuiltin ef args res) => Pbuiltin ef args res
  | PCtlFlow Asmvliw.Pret                  => Pret
  | PCtlFlow (Asmvliw.Pcall l)             => Pcall l
  | PCtlFlow (Asmvliw.Picall r)            => Picall r
  | PCtlFlow (Asmvliw.Pgoto l)             => Pgoto l
  | PCtlFlow (Asmvliw.Pigoto l)             => Pigoto l
  | PCtlFlow (Asmvliw.Pj_l l)              => Pj_l l
  | PCtlFlow (Asmvliw.Pcb bt r l)          => Pcb bt r l
  | PCtlFlow (Asmvliw.Pcbu bt r l)         => Pcbu bt r l
  | PCtlFlow (Asmvliw.Pjumptable r label)  => Pjumptable r label
  end.

Definition basic_to_instruction (b: basic) :=
  match b with
  (** Special basics *)
  | Asmvliw.Pget rd rs         => Pget rd rs
  | Asmvliw.Pset rd rs         => Pset rd rs
  | Asmvliw.Pnop               => Pnop
  | Asmvliw.Pallocframe sz pos => Pallocframe sz pos
  | Asmvliw.Pfreeframe sz pos  => Pfreeframe sz pos

  (** PArith basics *)
  (* R *)
  | PArithR (Asmvliw.Ploadsymbol id ofs) r => Ploadsymbol r id ofs

  (* RR *)
  | PArithRR Asmvliw.Pmv rd rs     => Pmv rd rs
  | PArithRR Asmvliw.Pnegw rd rs   => Pnegw rd rs
  | PArithRR Asmvliw.Pnegl rd rs   => Pnegl rd rs
  | PArithRR Asmvliw.Pcvtl2w rd rs => Pcvtl2w rd rs
  | PArithRR Asmvliw.Psxwd rd rs  => Psxwd rd rs
  | PArithRR Asmvliw.Pzxwd rd rs  => Pzxwd rd rs
  | PArithRR (Asmvliw.Pextfz stop start) rd rs => Pextfz rd rs stop start
  | PArithRR (Asmvliw.Pextfs stop start) rd rs => Pextfs rd rs stop start
  | PArithRR (Asmvliw.Pextfzl stop start) rd rs => Pextfzl rd rs stop start
  | PArithRR (Asmvliw.Pextfsl stop start) rd rs => Pextfsl rd rs stop start
  | PArithRR Asmvliw.Pfabsd rd rs => Pfabsd rd rs
  | PArithRR Asmvliw.Pfabsw rd rs => Pfabsw rd rs
  | PArithRR Asmvliw.Pfnegd rd rs  => Pfnegd rd rs
  | PArithRR Asmvliw.Pfnegw rd rs => Pfnegw rd rs
  | PArithRR Asmvliw.Pfinvw rd rs => Pfinvw rd rs
  | PArithRR Asmvliw.Pfnarrowdw rd rs => Pfnarrowdw rd rs
  | PArithRR Asmvliw.Pfwidenlwd rd rs => Pfwidenlwd rd rs
  | PArithRR Asmvliw.Pfloatuwrnsz rd rs => Pfloatuwrnsz rd rs
  | PArithRR Asmvliw.Pfloatwrnsz rd rs => Pfloatwrnsz rd rs
  | PArithRR Asmvliw.Pfloatudrnsz rd rs => Pfloatudrnsz rd rs
  | PArithRR Asmvliw.Pfloatdrnsz rd rs => Pfloatdrnsz rd rs
  | PArithRR Asmvliw.Pfixedwrzz rd rs => Pfixedwrzz rd rs
  | PArithRR Asmvliw.Pfixeduwrzz rd rs => Pfixeduwrzz rd rs
  | PArithRR Asmvliw.Pfixeddrzz rd rs => Pfixeddrzz rd rs
  | PArithRR Asmvliw.Pfixedudrzz rd rs => Pfixedudrzz rd rs
  | PArithRR Asmvliw.Pfixeddrzz_i32 rd rs => Pfixeddrzz_i32 rd rs
  | PArithRR Asmvliw.Pfixedudrzz_i32 rd rs => Pfixedudrzz_i32 rd rs

  (* RI32 *)
  | PArithRI32 Asmvliw.Pmake rd imm  => Pmake rd imm

  (* RI64 *)
  | PArithRI64 Asmvliw.Pmakel rd imm => Pmakel rd imm

  (* RF32 *)
  | PArithRF32 Asmvliw.Pmakefs rd imm => Pmakefs rd imm

  (* RF64 *)
  | PArithRF64 Asmvliw.Pmakef rd imm => Pmakef rd imm

  (* RRR *)
  | PArithRRR (Asmvliw.Pcompw it) rd rs1 rs2 => Pcompw it rd rs1 rs2
  | PArithRRR (Asmvliw.Pcompl it) rd rs1 rs2 => Pcompl it rd rs1 rs2
  | PArithRRR (Asmvliw.Pfcompw ft) rd rs1 rs2 => Pfcompw ft rd rs1 rs2
  | PArithRRR (Asmvliw.Pfcompl ft) rd rs1 rs2 => Pfcompl ft rd rs1 rs2
  | PArithRRR Asmvliw.Paddw rd rs1 rs2       => Paddw rd rs1 rs2
  | PArithRRR (Asmvliw.Paddxw shift) rd rs1 rs2 => Paddxw shift rd rs1 rs2
  | PArithRRR Asmvliw.Psubw rd rs1 rs2       => Psubw rd rs1 rs2
  | PArithRRR (Asmvliw.Prevsubxw shift) rd rs1 rs2 => Prevsubxw shift rd rs1 rs2
  | PArithRRR Asmvliw.Pmulw rd rs1 rs2       => Pmulw rd rs1 rs2
  | PArithRRR Asmvliw.Pandw rd rs1 rs2       => Pandw rd rs1 rs2
  | PArithRRR Asmvliw.Pnandw rd rs1 rs2      => Pnandw rd rs1 rs2
  | PArithRRR Asmvliw.Porw rd rs1 rs2        => Porw rd rs1 rs2
  | PArithRRR Asmvliw.Pnorw rd rs1 rs2       => Pnorw rd rs1 rs2
  | PArithRRR Asmvliw.Pxorw rd rs1 rs2       => Pxorw rd rs1 rs2
  | PArithRRR Asmvliw.Pnxorw rd rs1 rs2      => Pnxorw rd rs1 rs2
  | PArithRRR Asmvliw.Pandnw rd rs1 rs2      => Pandnw rd rs1 rs2
  | PArithRRR Asmvliw.Pornw rd rs1 rs2       => Pornw rd rs1 rs2
  | PArithRRR Asmvliw.Psraw rd rs1 rs2       => Psraw rd rs1 rs2
  | PArithRRR Asmvliw.Psrxw rd rs1 rs2       => Psrxw rd rs1 rs2
  | PArithRRR Asmvliw.Psrlw rd rs1 rs2       => Psrlw rd rs1 rs2
  | PArithRRR Asmvliw.Psllw rd rs1 rs2       => Psllw rd rs1 rs2

  | PArithRRR Asmvliw.Paddl rd rs1 rs2       => Paddl rd rs1 rs2
  | PArithRRR (Asmvliw.Paddxl shift) rd rs1 rs2 => Paddxl shift rd rs1 rs2
  | PArithRRR Asmvliw.Psubl rd rs1 rs2       => Psubl rd rs1 rs2
  | PArithRRR (Asmvliw.Prevsubxl shift) rd rs1 rs2 => Prevsubxl shift rd rs1 rs2
  | PArithRRR Asmvliw.Pandl rd rs1 rs2       => Pandl rd rs1 rs2
  | PArithRRR Asmvliw.Pnandl rd rs1 rs2      => Pnandl rd rs1 rs2
  | PArithRRR Asmvliw.Porl rd rs1 rs2        => Porl rd rs1 rs2
  | PArithRRR Asmvliw.Pnorl rd rs1 rs2       => Pnorl rd rs1 rs2
  | PArithRRR Asmvliw.Pxorl rd rs1 rs2       => Pxorl rd rs1 rs2
  | PArithRRR Asmvliw.Pnxorl rd rs1 rs2      => Pnxorl rd rs1 rs2
  | PArithRRR Asmvliw.Pandnl rd rs1 rs2      => Pandnl rd rs1 rs2
  | PArithRRR Asmvliw.Pornl rd rs1 rs2       => Pornl rd rs1 rs2
  | PArithRRR Asmvliw.Pmull rd rs1 rs2       => Pmull rd rs1 rs2
  | PArithRRR Asmvliw.Pslll rd rs1 rs2       => Pslll rd rs1 rs2
  | PArithRRR Asmvliw.Psrll rd rs1 rs2       => Psrll rd rs1 rs2
  | PArithRRR Asmvliw.Psral rd rs1 rs2       => Psral rd rs1 rs2
  | PArithRRR Asmvliw.Psrxl rd rs1 rs2       => Psrxl rd rs1 rs2

  | PArithRRR Asmvliw.Pfaddd rd rs1 rs2      => Pfaddd rd rs1 rs2
  | PArithRRR Asmvliw.Pfaddw rd rs1 rs2      => Pfaddw rd rs1 rs2
  | PArithRRR Asmvliw.Pfsbfd rd rs1 rs2      => Pfsbfd rd rs1 rs2
  | PArithRRR Asmvliw.Pfsbfw rd rs1 rs2      => Pfsbfw rd rs1 rs2
  | PArithRRR Asmvliw.Pfmuld rd rs1 rs2      => Pfmuld rd rs1 rs2
  | PArithRRR Asmvliw.Pfmulw rd rs1 rs2      => Pfmulw rd rs1 rs2
  | PArithRRR Asmvliw.Pfmind rd rs1 rs2      => Pfmind rd rs1 rs2
  | PArithRRR Asmvliw.Pfminw rd rs1 rs2      => Pfminw rd rs1 rs2
  | PArithRRR Asmvliw.Pfmaxd rd rs1 rs2      => Pfmaxd rd rs1 rs2
  | PArithRRR Asmvliw.Pfmaxw rd rs1 rs2      => Pfmaxw rd rs1 rs2

  (* RRI32 *)
  | PArithRRI32 (Asmvliw.Pcompiw it) rd rs imm => Pcompiw it rd rs imm
  | PArithRRI32 Asmvliw.Paddiw rd rs imm       => Paddiw rd rs imm
  | PArithRRI32 (Asmvliw.Paddxiw shift) rd rs imm => Paddxiw shift rd rs imm
  | PArithRRI32 Asmvliw.Prevsubiw rd rs imm       => Prevsubiw rd rs imm
  | PArithRRI32 (Asmvliw.Prevsubxiw shift) rd rs imm => Prevsubxiw shift rd rs imm
  | PArithRRI32 Asmvliw.Pmuliw rd rs imm       => Pmuliw rd rs imm
  | PArithRRI32 Asmvliw.Pandiw rd rs imm       => Pandiw rd rs imm
  | PArithRRI32 Asmvliw.Pnandiw rd rs imm      => Pnandiw rd rs imm
  | PArithRRI32 Asmvliw.Poriw rd rs imm        => Poriw rd rs imm
  | PArithRRI32 Asmvliw.Pnoriw rd rs imm       => Pnoriw rd rs imm
  | PArithRRI32 Asmvliw.Pxoriw rd rs imm       => Pxoriw rd rs imm
  | PArithRRI32 Asmvliw.Pnxoriw rd rs imm      => Pnxoriw rd rs imm
  | PArithRRI32 Asmvliw.Pandniw rd rs imm      => Pandniw rd rs imm
  | PArithRRI32 Asmvliw.Porniw rd rs imm       => Porniw rd rs imm
  | PArithRRI32 Asmvliw.Psraiw rd rs imm       => Psraiw rd rs imm
  | PArithRRI32 Asmvliw.Psrxiw rd rs imm       => Psrxiw rd rs imm
  | PArithRRI32 Asmvliw.Psrliw rd rs imm       => Psrliw rd rs imm
  | PArithRRI32 Asmvliw.Pslliw rd rs imm       => Pslliw rd rs imm
  | PArithRRI32 Asmvliw.Proriw rd rs imm       => Proriw rd rs imm
  | PArithRRI32 Asmvliw.Psllil rd rs imm       => Psllil rd rs imm
  | PArithRRI32 Asmvliw.Psrlil rd rs imm       => Psrlil rd rs imm
  | PArithRRI32 Asmvliw.Psrxil rd rs imm       => Psrxil rd rs imm
  | PArithRRI32 Asmvliw.Psrail rd rs imm       => Psrail rd rs imm

  (* RRI64 *)
  | PArithRRI64 (Asmvliw.Pcompil it) rd rs imm => Pcompil it rd rs imm
  | PArithRRI64 Asmvliw.Paddil rd rs imm       => Paddil rd rs imm
  | PArithRRI64 (Asmvliw.Paddxil shift) rd rs imm => Paddxil shift rd rs imm
  | PArithRRI64 Asmvliw.Prevsubil rd rs imm       => Prevsubil rd rs imm
  | PArithRRI64 (Asmvliw.Prevsubxil shift) rd rs imm => Prevsubxil shift rd rs imm
  | PArithRRI64 Asmvliw.Pmulil rd rs imm       => Pmulil rd rs imm
  | PArithRRI64 Asmvliw.Pandil rd rs imm       => Pandil rd rs imm
  | PArithRRI64 Asmvliw.Pnandil rd rs imm      => Pnandil rd rs imm
  | PArithRRI64 Asmvliw.Poril rd rs imm        => Poril rd rs imm
  | PArithRRI64 Asmvliw.Pnoril rd rs imm       => Pnoril rd rs imm
  | PArithRRI64 Asmvliw.Pxoril rd rs imm       => Pxoril rd rs imm
  | PArithRRI64 Asmvliw.Pnxoril rd rs imm      => Pnxoril rd rs imm
  | PArithRRI64 Asmvliw.Pandnil rd rs imm      => Pandnil rd rs imm
  | PArithRRI64 Asmvliw.Pornil rd rs imm       => Pornil rd rs imm

  (** ARRR *)
  | PArithARRR Asmvliw.Pmaddw rd rs1 rs2       => Pmaddw rd rs1 rs2
  | PArithARRR Asmvliw.Pmaddl rd rs1 rs2       => Pmaddl rd rs1 rs2
  | PArithARRR Asmvliw.Pmsubw rd rs1 rs2       => Pmsubw rd rs1 rs2
  | PArithARRR Asmvliw.Pmsubl rd rs1 rs2       => Pmsubl rd rs1 rs2
  | PArithARRR Asmvliw.Pfmaddfw rd rs1 rs2     => Pfmaddfw rd rs1 rs2
  | PArithARRR Asmvliw.Pfmaddfl rd rs1 rs2     => Pfmaddfl rd rs1 rs2
  | PArithARRR Asmvliw.Pfmsubfw rd rs1 rs2     => Pfmsubfw rd rs1 rs2
  | PArithARRR Asmvliw.Pfmsubfl rd rs1 rs2     => Pfmsubfl rd rs1 rs2
  | PArithARRR (Asmvliw.Pcmove cond) rd rs1 rs2=> Pcmove cond rd rs1 rs2
  | PArithARRR (Asmvliw.Pcmoveu cond) rd rs1 rs2=> Pcmoveu cond rd rs1 rs2

  (** ARR *)
  | PArithARR (Asmvliw.Pinsf stop start) rd rs  => Pinsf rd rs stop start
  | PArithARR (Asmvliw.Pinsfl stop start) rd rs  => Pinsfl rd rs stop start

  (** ARRI32 *)
  | PArithARRI32 Asmvliw.Pmaddiw rd rs1 imm    => Pmaddiw rd rs1 imm
  | PArithARRI32 (Asmvliw.Pcmoveiw cond) rd rs1 imm => Pcmoveiw cond rd rs1 imm
  | PArithARRI32 (Asmvliw.Pcmoveuiw cond) rd rs1 imm => Pcmoveuiw cond rd rs1 imm

  (** ARRI64 *)
  | PArithARRI64 Asmvliw.Pmaddil rd rs1 imm    => Pmaddil rd rs1 imm
  | PArithARRI64 (Asmvliw.Pcmoveil cond) rd rs1 imm => Pcmoveil cond rd rs1 imm
  | PArithARRI64 (Asmvliw.Pcmoveuil cond) rd rs1 imm => Pcmoveuil cond rd rs1 imm                                                          
  (** Load *)
  | PLoadRRO trap Asmvliw.Plb rd ra ofs   => Plb trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Plbu rd ra ofs  => Plbu trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Plh rd ra ofs   => Plh trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Plhu rd ra ofs  => Plhu trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Plw rd ra ofs   => Plw trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Plw_a rd ra ofs => Plw_a trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Pld rd ra ofs   => Pld trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Pld_a rd ra ofs => Pld_a trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Pfls rd ra ofs  => Pfls trap rd ra (AOff ofs)
  | PLoadRRO trap Asmvliw.Pfld rd ra ofs  => Pfld trap rd ra (AOff ofs)

  | PLoadQRRO qrs ra ofs => Plq qrs ra (AOff ofs)
  | PLoadORRO qrs ra ofs => Plo qrs ra (AOff ofs)

  | PLoadRRR trap Asmvliw.Plb rd ra ro   => Plb trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Plbu rd ra ro  => Plbu trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Plh rd ra ro   => Plh trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Plhu rd ra ro  => Plhu trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Plw rd ra ro   => Plw trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Plw_a rd ra ro => Plw_a trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Pld rd ra ro   => Pld trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Pld_a rd ra ro => Pld_a trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Pfls rd ra ro  => Pfls trap rd ra (AReg ro)
  | PLoadRRR trap Asmvliw.Pfld rd ra ro  => Pfld trap rd ra (AReg ro)

  | PLoadRRRXS trap Asmvliw.Plb rd ra ro   => Plb trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Plbu rd ra ro  => Plbu trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Plh rd ra ro   => Plh trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Plhu rd ra ro  => Plhu trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Plw rd ra ro   => Plw trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Plw_a rd ra ro => Plw_a trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Pld rd ra ro   => Pld trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Pld_a rd ra ro => Pld_a trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Pfls rd ra ro  => Pfls trap rd ra (ARegXS ro)
  | PLoadRRRXS trap Asmvliw.Pfld rd ra ro  => Pfld trap rd ra (ARegXS ro)

  (** Store *)
  | PStoreRRO Asmvliw.Psb rd ra ofs  => Psb rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Psh rd ra ofs => Psh rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Psw rd ra ofs => Psw rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Psw_a rd ra ofs => Psw_a rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Psd rd ra ofs => Psd rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Psd_a rd ra ofs => Psd_a rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Pfss rd ra ofs => Pfss rd ra (AOff ofs)
  | PStoreRRO Asmvliw.Pfsd rd ra ofs => Pfsd rd ra (AOff ofs)

  | PStoreRRR Asmvliw.Psb rd ra ro  => Psb rd ra (AReg ro)
  | PStoreRRR Asmvliw.Psh rd ra ro => Psh rd ra (AReg ro)
  | PStoreRRR Asmvliw.Psw rd ra ro => Psw rd ra (AReg ro)
  | PStoreRRR Asmvliw.Psw_a rd ra ro => Psw_a rd ra (AReg ro)
  | PStoreRRR Asmvliw.Psd rd ra ro => Psd rd ra (AReg ro)
  | PStoreRRR Asmvliw.Psd_a rd ra ro => Psd_a rd ra (AReg ro)
  | PStoreRRR Asmvliw.Pfss rd ra ro => Pfss rd ra (AReg ro)
  | PStoreRRR Asmvliw.Pfsd rd ra ro => Pfsd rd ra (AReg ro)

  | PStoreRRRXS Asmvliw.Psb rd ra ro  => Psb rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Psh rd ra ro => Psh rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Psw rd ra ro => Psw rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Psw_a rd ra ro => Psw_a rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Psd rd ra ro => Psd rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Psd_a rd ra ro => Psd_a rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Pfss rd ra ro => Pfss rd ra (ARegXS ro)
  | PStoreRRRXS Asmvliw.Pfsd rd ra ro => Pfsd rd ra (ARegXS ro)

  | PStoreQRRO qrs ra ofs => Psq qrs ra (AOff ofs)
  | PStoreORRO qrs ra ofs => Pso qrs ra (AOff ofs)
  end.

Section RELSEM.

Definition code := list instruction.

Fixpoint unfold_label (ll: list label) :=
  match ll with
  | nil => nil
  | l :: ll => Plabel l :: unfold_label ll
  end.

Fixpoint unfold_body (lb: list basic) :=
  match lb with
  | nil => nil
  | b :: lb => basic_to_instruction b :: unfold_body lb
  end.

Definition unfold_exit (oc: option control) :=
  match oc with
  | None => nil
  | Some c => control_to_instruction c :: nil
  end.

Definition unfold_bblock (b: bblock) := unfold_label (header b) ++
  (match (body b), (exit b) with
   | (((Asmvliw.Pfreeframe _ _ | Asmvliw.Pallocframe _ _)::nil) as bo), None =>
     unfold_body bo
   | bo, ex => unfold_body bo ++ unfold_exit ex ++ Psemi :: nil
  end).

Fixpoint unfold (lb: bblocks) :=
  match lb with
  | nil => nil
  | b :: lb => (unfold_bblock b) ++ unfold lb
  end.

Record function : Type := mkfunction { fn_sig: signature; fn_blocks: bblocks; fn_code: code; 
                                       correct: unfold fn_blocks = fn_code }.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
Definition genv := Genv.t fundef unit.

Definition function_proj (f: function) := Asmvliw.mkfunction (fn_sig f) (fn_blocks f).

Definition fundef_proj (fu: fundef) : Asmvliw.fundef := 
  match fu with
  | Internal f => Internal (function_proj f)
  | External ef => External ef
  end.

Definition globdef_proj (gd: globdef fundef unit) : globdef Asmvliw.fundef unit :=
  match gd with
  | Gfun f => Gfun (fundef_proj f)
  | Gvar gu => Gvar gu
  end.

Program Definition genv_trans (ge: genv) : Asmvliw.genv :=
  {|  Genv.genv_public := Genv.genv_public ge;
      Genv.genv_symb := Genv.genv_symb ge;
      Genv.genv_defs := PTree.map1 globdef_proj (Genv.genv_defs ge);
      Genv.genv_next := Genv.genv_next ge |}.
Next Obligation.
  destruct ge. simpl in *. eauto.
Qed. Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gmap1 in H.
  destruct (genv_defs ! b) eqn:GEN.
  - eauto.
  - discriminate.
Qed. Next Obligation.
  destruct ge; simpl in *.
  eauto.
Qed.

Fixpoint prog_defs_proj (l: list (ident * globdef fundef unit))
                          : list (ident * globdef Asmvliw.fundef unit) :=
  match l with
  | nil => nil
  | (i, gd) :: l => (i, globdef_proj gd) :: prog_defs_proj l
  end.

Definition program_proj (p: program) : Asmvliw.program :=
  {|  prog_defs := prog_defs_proj (prog_defs p);
      prog_public := prog_public p;
      prog_main := prog_main p
  |}.

End RELSEM.

Definition semantics (p: program) := Asmvliw.semantics (program_proj p).

(** Determinacy of the [Asm] semantics. *)

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
  intros. apply semantics_determinate.
Qed.

(** transf_program *)

Program Definition transf_function (f: Asmvliw.function) : function :=
     {| fn_sig := Asmvliw.fn_sig f; fn_blocks := Asmvliw.fn_blocks f; 
        fn_code := unfold (Asmvliw.fn_blocks f) |}.

Lemma transf_function_proj: forall f, function_proj (transf_function f) = f.
Proof.
  intros f. destruct f as [sig blks]. unfold function_proj. simpl. auto.
Qed.

Definition transf_fundef : Asmvliw.fundef -> fundef := AST.transf_fundef transf_function.

Lemma transf_fundef_proj: forall f, fundef_proj (transf_fundef f) = f.
Proof.
  intros f. destruct f as [f|e]; simpl; auto.
  rewrite transf_function_proj. auto.
Qed.

Definition transf_program : Asmvliw.program -> program := transform_program transf_fundef.

Lemma program_equals {A B: Type} : forall (p1 p2: AST.program A B),
  prog_defs p1 = prog_defs p2 ->
  prog_public p1 = prog_public p2 ->
  prog_main p1 = prog_main p2 ->
  p1 = p2.
Proof.
  intros. destruct p1. destruct p2. simpl in *. subst. auto.
Qed.

Lemma transf_program_proj: forall p, program_proj (transf_program p) = p.
Proof.
  intros p. destruct p as [defs pub main]. unfold program_proj. simpl.
  apply program_equals; simpl; auto.
  induction defs.
  - simpl; auto.
  - simpl. rewrite IHdefs. 
    destruct a as [id gd]; simpl.
    destruct gd as [f|v]; simpl; auto.
    rewrite transf_fundef_proj. auto.
Qed.

Definition match_prog (p: Asmvliw.program) (tp: program) :=
  match_program (fun _ f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. rewrite <- H. eapply match_transform_program; eauto.
Qed.

Lemma cons_extract {A: Type} : forall (l: list A) a b, a = b -> a::l = b::l.
Proof.
  intros. congruence.
Qed.

Lemma match_program_transf:
  forall p tp, match_prog p tp -> transf_program p = tp.
Proof.
  intros p tp H. inversion_clear H. inv H1.
  destruct p as [defs pub main]. destruct tp as [tdefs tpub tmain]. simpl in *.
  subst. unfold transf_program. unfold transform_program. simpl.
  apply program_equals; simpl; auto.
  induction H0; simpl; auto.
  rewrite IHlist_forall2. apply cons_extract.
  destruct a1 as [ida gda]. destruct b1 as [idb gdb].
  simpl in *.
  inv H. inv H2.
  - simpl in *. subst. auto.
  - simpl in *. subst. inv H. auto.
Qed.

Section PRESERVATION.

Variable prog: Asmvliw.program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Definition match_states (s1 s2: state) := s1 = s2.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).


Theorem transf_program_correct:
  forward_simulation (Asmvliw.semantics prog) (semantics tprog).
Proof.
  pose proof (match_program_transf prog tprog TRANSF) as TR.
  subst. unfold semantics. rewrite transf_program_proj.

  eapply forward_simulation_step with (match_states := match_states); simpl; auto.
  - intros. exists s1. split; auto. congruence.
  - intros. inv H. auto.
  - intros. exists s1'. inv H0. split; auto. congruence.
Qed.

End PRESERVATION.
