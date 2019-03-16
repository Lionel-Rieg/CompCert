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
Require Import Asmblock.
Require Import Linking.
Require Import Errors.

(** Definitions for OCaml code *)
Definition label := positive.
Definition preg := preg.

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

  (** builtins *)
  | Pclzll (rd rs: ireg)
  | Pstsud (rd rs1 rs2: ireg)

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
  | Ploopdo (count: ireg) (loopend: label)

  (** Loads **)
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

  (** Stores **)
  | Psb     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store byte *)
  | Psh     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store half byte *)
  | Psw     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any32 *)
  | Psd     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int64 *)
  | Psd_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any64 *)
  | Pfss    (rs: freg) (ra: ireg) (ofs: offset)     (**r store float *)
  | Pfsd     (rd: freg) (ra: ireg) (ofs: offset)    (**r store 64-bit float *)

  (** Arith RR *)
  | Pmv     (rd rs: ireg)                           (**r register move *)
  | Pnegw   (rd rs: ireg)                           (**r negate word *)
  | Pnegl   (rd rs: ireg)                           (**r negate long *)
  | Pcvtl2w (rd rs: ireg)                           (**r Convert Long to Word *)
  | Psxwd   (rd rs: ireg)                           (**r Sign Extend Word to Double Word *)
  | Pzxwd   (rd rs: ireg)                           (**r Zero Extend Word to Double Word *)
  | Pfabsd  (rd rs: ireg)                           (**r float absolute double *)
  | Pfabsw  (rd rs: ireg)                           (**r float absolute word *)
  | Pfnegd  (rd rs: ireg)                           (**r float negate double *)
  | Pfnegw  (rd rs: ireg)                           (**r float negate word *)
  | Pfnarrowdw (rd rs: ireg)                        (**r float narrow 64 -> 32 bits *)
  | Pfwidenlwd (rd rs: ireg)                        (**r float widen 32 -> 64 bits *)
  | Pfloatwrnsz (rd rs: ireg)                       (**r Floating Point Conversion from integer (32 -> 32) *)
  | Pfloatuwrnsz (rd rs: ireg)                      (**r Floating Point Conversion from integer (u32 -> 32) *)
  | Pfloatudrnsz (rd rs: ireg)                       (**r Floating Point Conversion from unsigned integer (64 bits) *)
  | Pfloatudrnsz_i32 (rd rs: ireg)                       (**r Floating Point Conversion from unsigned integer (32 bits) *)
  | Pfloatdrnsz (rd rs: ireg)                       (**r Floating Point Conversion from integer (64 bits) *)
  | Pfloatdrnsz_i32 (rd rs: ireg)                       (**r Floating Point Conversion from integer (32 bits) *)
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
  | Psubw               (rd rs1 rs2: ireg)          (**r sub word *)
  | Pmulw               (rd rs1 rs2: ireg)          (**r mul word *)
  | Pandw               (rd rs1 rs2: ireg)          (**r and word *)
  | Pnandw              (rd rs1 rs2: ireg)          (**r nand word *)
  | Porw                (rd rs1 rs2: ireg)          (**r or word *)
  | Pnorw               (rd rs1 rs2: ireg)          (**r nor word *)
  | Pxorw               (rd rs1 rs2: ireg)          (**r xor word *)
  | Psraw               (rd rs1 rs2: ireg)          (**r shift right arithmetic word *)
  | Psrlw               (rd rs1 rs2: ireg)          (**r shift right logical word *)
  | Psllw               (rd rs1 rs2: ireg)          (**r shift left logical word *)

  | Paddl               (rd rs1 rs2: ireg)          (**r add long *)
  | Psubl               (rd rs1 rs2: ireg)          (**r sub long *)
  | Pandl               (rd rs1 rs2: ireg)          (**r and long *)
  | Porl                (rd rs1 rs2: ireg)          (**r or long *)
  | Pxorl               (rd rs1 rs2: ireg)          (**r xor long *)
  | Pmull               (rd rs1 rs2: ireg)          (**r mul long (low part) *)
  | Pslll               (rd rs1 rs2: ireg)          (**r shift left logical long *)
  | Psrll               (rd rs1 rs2: ireg)          (**r shift right logical long *)
  | Psral               (rd rs1 rs2: ireg)          (**r shift right arithmetic long *)

  | Pfaddd              (rd rs1 rs2: ireg)          (**r Float addition double *)
  | Pfaddw              (rd rs1 rs2: ireg)          (**r Float addition word *)
  | Pfsbfd              (rd rs1 rs2: ireg)          (**r Float sub double *)
  | Pfsbfw              (rd rs1 rs2: ireg)          (**r Float sub word *)
  | Pfmuld              (rd rs1 rs2: ireg)          (**r Float mul double *)
  | Pfmulw              (rd rs1 rs2: ireg)          (**r Float mul word *)

  (** Arith RRI32 *)
  | Pcompiw (it: itest) (rd rs: ireg) (imm: int)    (**r comparison imm word *)

  | Paddiw              (rd rs: ireg) (imm: int)    (**r add imm word *)
  | Pandiw              (rd rs: ireg) (imm: int)    (**r and imm word *)
  | Pnandiw             (rd rs: ireg) (imm: int)    (**r nand imm word *)
  | Poriw               (rd rs: ireg) (imm: int)    (**r or imm word *)
  | Pnoriw              (rd rs: ireg) (imm: int)    (**r nor imm word *)
  | Pxoriw              (rd rs: ireg) (imm: int)    (**r xor imm word *)
  | Psraiw              (rd rs: ireg) (imm: int)    (**r shift right arithmetic imm word *)
  | Psrliw              (rd rs: ireg) (imm: int)    (**r shift right logical imm word *)
  | Pslliw              (rd rs: ireg) (imm: int)    (**r shift left logical imm word *)
  | Proriw              (rd rs: ireg) (imm: int)    (**r rotate right imm word *) 
  | Psllil              (rd rs: ireg) (imm: int)    (**r shift left logical immediate long *)
  | Psrlil              (rd rs: ireg) (imm: int)    (**r shift right logical immediate long *)
  | Psrail              (rd rs: ireg) (imm: int)    (**r shift right arithmetic immediate long *)

  (** Arith RRI64 *)
  | Pcompil (it: itest) (rd rs: ireg) (imm: int64)  (**r comparison imm long *)
  | Paddil              (rd rs: ireg) (imm: int64)  (**r add immediate long *) 
  | Pandil              (rd rs: ireg) (imm: int64)  (**r and immediate long *) 
  | Poril               (rd rs: ireg) (imm: int64)  (**r or immediate long *) 
  | Pxoril              (rd rs: ireg) (imm: int64)  (**r xor immediate long *)
  .

(** Correspondance between Asmblock and Asm *)

Definition control_to_instruction (c: control) :=
  match c with
  | PExpand (Asmblock.Pbuiltin ef args res) => Pbuiltin ef args res
  | PCtlFlow Asmblock.Pret                  => Pret
  | PCtlFlow (Asmblock.Pcall l)             => Pcall l
  | PCtlFlow (Asmblock.Picall r)            => Picall r
  | PCtlFlow (Asmblock.Pgoto l)             => Pgoto l
  | PCtlFlow (Asmblock.Pigoto l)             => Pigoto l
  | PCtlFlow (Asmblock.Pj_l l)              => Pj_l l
  | PCtlFlow (Asmblock.Pcb bt r l)          => Pcb bt r l
  | PCtlFlow (Asmblock.Pcbu bt r l)         => Pcbu bt r l
  end.

Definition basic_to_instruction (b: basic) :=
  match b with
  (** Special basics *)
  | Asmblock.Pget rd rs         => Pget rd rs
  | Asmblock.Pset rd rs         => Pset rd rs
  | Asmblock.Pnop               => Pnop
  | Asmblock.Pallocframe sz pos => Pallocframe sz pos
  | Asmblock.Pfreeframe sz pos  => Pfreeframe sz pos

  (** PArith basics *)
  (* R *)
  | PArithR (Asmblock.Ploadsymbol id ofs) r => Ploadsymbol r id ofs

  (* RR *)
  | PArithRR Asmblock.Pmv rd rs     => Pmv rd rs
  | PArithRR Asmblock.Pnegw rd rs   => Pnegw rd rs
  | PArithRR Asmblock.Pnegl rd rs   => Pnegl rd rs
  | PArithRR Asmblock.Pcvtl2w rd rs => Pcvtl2w rd rs
  | PArithRR Asmblock.Psxwd rd rs  => Psxwd rd rs
  | PArithRR Asmblock.Pzxwd rd rs  => Pzxwd rd rs
  | PArithRR Asmblock.Pfabsd rd rs => Pfabsd rd rs
  | PArithRR Asmblock.Pfabsw rd rs => Pfabsw rd rs
  | PArithRR Asmblock.Pfnegd rd rs  => Pfnegd rd rs
  | PArithRR Asmblock.Pfnegw rd rs => Pfnegw rd rs
  | PArithRR Asmblock.Pfnarrowdw rd rs => Pfnarrowdw rd rs
  | PArithRR Asmblock.Pfwidenlwd rd rs => Pfwidenlwd rd rs
  | PArithRR Asmblock.Pfloatuwrnsz rd rs => Pfloatuwrnsz rd rs
  | PArithRR Asmblock.Pfloatwrnsz rd rs => Pfloatwrnsz rd rs
  | PArithRR Asmblock.Pfloatudrnsz rd rs => Pfloatudrnsz rd rs
  | PArithRR Asmblock.Pfloatdrnsz rd rs => Pfloatdrnsz rd rs
  | PArithRR Asmblock.Pfloatudrnsz_i32 rd rs => Pfloatudrnsz_i32 rd rs
  | PArithRR Asmblock.Pfloatdrnsz_i32 rd rs => Pfloatdrnsz_i32 rd rs
  | PArithRR Asmblock.Pfixedwrzz rd rs => Pfixedwrzz rd rs
  | PArithRR Asmblock.Pfixeduwrzz rd rs => Pfixeduwrzz rd rs
  | PArithRR Asmblock.Pfixeddrzz rd rs => Pfixeddrzz rd rs
  | PArithRR Asmblock.Pfixedudrzz rd rs => Pfixedudrzz rd rs
  | PArithRR Asmblock.Pfixeddrzz_i32 rd rs => Pfixeddrzz_i32 rd rs
  | PArithRR Asmblock.Pfixedudrzz_i32 rd rs => Pfixedudrzz_i32 rd rs

  (* RI32 *)
  | PArithRI32 Asmblock.Pmake rd imm  => Pmake rd imm

  (* RI64 *)
  | PArithRI64 Asmblock.Pmakel rd imm => Pmakel rd imm

  (* RF32 *)
  | PArithRF32 Asmblock.Pmakefs rd imm => Pmakefs rd imm

  (* RF64 *)
  | PArithRF64 Asmblock.Pmakef rd imm => Pmakef rd imm

  (* RRR *)
  | PArithRRR (Asmblock.Pcompw it) rd rs1 rs2 => Pcompw it rd rs1 rs2
  | PArithRRR (Asmblock.Pcompl it) rd rs1 rs2 => Pcompl it rd rs1 rs2
  | PArithRRR (Asmblock.Pfcompw ft) rd rs1 rs2 => Pfcompw ft rd rs1 rs2
  | PArithRRR (Asmblock.Pfcompl ft) rd rs1 rs2 => Pfcompl ft rd rs1 rs2
  | PArithRRR Asmblock.Paddw rd rs1 rs2       => Paddw rd rs1 rs2
  | PArithRRR Asmblock.Psubw rd rs1 rs2       => Psubw rd rs1 rs2
  | PArithRRR Asmblock.Pmulw rd rs1 rs2       => Pmulw rd rs1 rs2
  | PArithRRR Asmblock.Pandw rd rs1 rs2       => Pandw rd rs1 rs2
  | PArithRRR Asmblock.Pnandw rd rs1 rs2      => Pnandw rd rs1 rs2
  | PArithRRR Asmblock.Porw rd rs1 rs2        => Porw rd rs1 rs2
  | PArithRRR Asmblock.Pnorw rd rs1 rs2       => Pnorw rd rs1 rs2
  | PArithRRR Asmblock.Pxorw rd rs1 rs2       => Pxorw rd rs1 rs2
  | PArithRRR Asmblock.Psraw rd rs1 rs2       => Psraw rd rs1 rs2
  | PArithRRR Asmblock.Psrlw rd rs1 rs2       => Psrlw rd rs1 rs2
  | PArithRRR Asmblock.Psllw rd rs1 rs2       => Psllw rd rs1 rs2

  | PArithRRR Asmblock.Paddl rd rs1 rs2       => Paddl rd rs1 rs2
  | PArithRRR Asmblock.Psubl rd rs1 rs2       => Psubl rd rs1 rs2
  | PArithRRR Asmblock.Pandl rd rs1 rs2       => Pandl rd rs1 rs2
  | PArithRRR Asmblock.Porl rd rs1 rs2        => Porl rd rs1 rs2
  | PArithRRR Asmblock.Pxorl rd rs1 rs2       => Pxorl rd rs1 rs2
  | PArithRRR Asmblock.Pmull rd rs1 rs2       => Pmull rd rs1 rs2
  | PArithRRR Asmblock.Pslll rd rs1 rs2       => Pslll rd rs1 rs2
  | PArithRRR Asmblock.Psrll rd rs1 rs2       => Psrll rd rs1 rs2
  | PArithRRR Asmblock.Psral rd rs1 rs2       => Psral rd rs1 rs2

  | PArithRRR Asmblock.Pfaddd rd rs1 rs2      => Pfaddd rd rs1 rs2
  | PArithRRR Asmblock.Pfaddw rd rs1 rs2      => Pfaddw rd rs1 rs2
  | PArithRRR Asmblock.Pfsbfd rd rs1 rs2      => Pfsbfd rd rs1 rs2
  | PArithRRR Asmblock.Pfsbfw rd rs1 rs2      => Pfsbfw rd rs1 rs2
  | PArithRRR Asmblock.Pfmuld rd rs1 rs2      => Pfmuld rd rs1 rs2
  | PArithRRR Asmblock.Pfmulw rd rs1 rs2      => Pfmulw rd rs1 rs2

  (* RRI32 *)
  | PArithRRI32 (Asmblock.Pcompiw it) rd rs imm => Pcompiw it rd rs imm
  | PArithRRI32 Asmblock.Paddiw rd rs imm       => Paddiw rd rs imm
  | PArithRRI32 Asmblock.Pandiw rd rs imm       => Pandiw rd rs imm
  | PArithRRI32 Asmblock.Pnandiw rd rs imm      => Pnandiw rd rs imm
  | PArithRRI32 Asmblock.Poriw rd rs imm        => Poriw rd rs imm
  | PArithRRI32 Asmblock.Pnoriw rd rs imm       => Pnoriw rd rs imm
  | PArithRRI32 Asmblock.Pxoriw rd rs imm       => Pxoriw rd rs imm
  | PArithRRI32 Asmblock.Psraiw rd rs imm       => Psraiw rd rs imm
  | PArithRRI32 Asmblock.Psrliw rd rs imm       => Psrliw rd rs imm
  | PArithRRI32 Asmblock.Pslliw rd rs imm       => Pslliw rd rs imm
  | PArithRRI32 Asmblock.Proriw rd rs imm       => Proriw rd rs imm
  | PArithRRI32 Asmblock.Psllil rd rs imm       => Psllil rd rs imm
  | PArithRRI32 Asmblock.Psrlil rd rs imm       => Psrlil rd rs imm
  | PArithRRI32 Asmblock.Psrail rd rs imm       => Psrail rd rs imm

  (* RRI64 *)
  | PArithRRI64 (Asmblock.Pcompil it) rd rs imm => Pcompil it rd rs imm
  | PArithRRI64 Asmblock.Paddil rd rs imm       => Paddil rd rs imm
  | PArithRRI64 Asmblock.Pandil rd rs imm       => Pandil rd rs imm
  | PArithRRI64 Asmblock.Poril rd rs imm        => Poril rd rs imm
  | PArithRRI64 Asmblock.Pxoril rd rs imm       => Pxoril rd rs imm

  (** Load *)
  | PLoadRRO Asmblock.Plb rd ra ofs   => Plb rd ra ofs
  | PLoadRRO Asmblock.Plbu rd ra ofs  => Plbu rd ra ofs
  | PLoadRRO Asmblock.Plh rd ra ofs   => Plh rd ra ofs
  | PLoadRRO Asmblock.Plhu rd ra ofs  => Plhu rd ra ofs
  | PLoadRRO Asmblock.Plw rd ra ofs   => Plw rd ra ofs
  | PLoadRRO Asmblock.Plw_a rd ra ofs => Plw_a rd ra ofs
  | PLoadRRO Asmblock.Pld rd ra ofs   => Pld rd ra ofs
  | PLoadRRO Asmblock.Pld_a rd ra ofs => Pld_a rd ra ofs
  | PLoadRRO Asmblock.Pfls rd ra ofs  => Pfls rd ra ofs
  | PLoadRRO Asmblock.Pfld rd ra ofs  => Pfld rd ra ofs

  (** Store *)
  | PStoreRRO Asmblock.Psb rd ra ofs  => Psb rd ra ofs
  | PStoreRRO Asmblock.Psh rd ra ofs => Psh rd ra ofs
  | PStoreRRO Asmblock.Psw rd ra ofs => Psw rd ra ofs
  | PStoreRRO Asmblock.Psw_a rd ra ofs => Psw_a rd ra ofs
  | PStoreRRO Asmblock.Psd rd ra ofs => Psd rd ra ofs
  | PStoreRRO Asmblock.Psd_a rd ra ofs => Psd_a rd ra ofs
  | PStoreRRO Asmblock.Pfss rd ra ofs => Pfss rd ra ofs
  | PStoreRRO Asmblock.Pfsd rd ra ofs => Pfsd rd ra ofs

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

Definition unfold_bblock (b: bblock) := unfold_label (header b) ++ unfold_body (body b) ++ unfold_exit (exit b) ++ Psemi :: nil.

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

Definition function_proj (f: function) := Asmblock.mkfunction (fn_sig f) (fn_blocks f).

(* 
Definition fundef_proj (fu: fundef) : Asmblock.fundef := transf_fundef function_proj fu.

Definition program_proj (p: program) : Asmblock.program := transform_program fundef_proj p.
 *)

Definition fundef_proj (fu: fundef) : Asmblock.fundef := 
  match fu with
  | Internal f => Internal (function_proj f)
  | External ef => External ef
  end.

Definition globdef_proj (gd: globdef fundef unit) : globdef Asmblock.fundef unit :=
  match gd with
  | Gfun f => Gfun (fundef_proj f)
  | Gvar gu => Gvar gu
  end.

Program Definition genv_trans (ge: genv) : Asmblock.genv :=
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
                          : list (ident * globdef Asmblock.fundef unit) :=
  match l with
  | nil => nil
  | (i, gd) :: l => (i, globdef_proj gd) :: prog_defs_proj l
  end.

Definition program_proj (p: program) : Asmblock.program :=
  {|  prog_defs := prog_defs_proj (prog_defs p);
      prog_public := prog_public p;
      prog_main := prog_main p
  |}.

End RELSEM.

Definition semantics (p: program) := Asmblock.semantics (program_proj p).

(** Determinacy of the [Asm] semantics. *)

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
  intros. apply semantics_determinate.
Qed.

(** transf_program *)

Program Definition transf_function (f: Asmblock.function) : function :=
     {| fn_sig := Asmblock.fn_sig f; fn_blocks := Asmblock.fn_blocks f; 
        fn_code := unfold (Asmblock.fn_blocks f) |}.

Lemma transf_function_proj: forall f, function_proj (transf_function f) = f.
Proof.
  intros f. destruct f as [sig blks]. unfold function_proj. simpl. auto.
Qed.

Definition transf_fundef : Asmblock.fundef -> fundef := AST.transf_fundef transf_function.

Lemma transf_fundef_proj: forall f, fundef_proj (transf_fundef f) = f.
Proof.
  intros f. destruct f as [f|e]; simpl; auto.
  rewrite transf_function_proj. auto.
Qed.

(* Definition transf_globdef (gd: globdef Asmblock.fundef unit) : globdef fundef unit :=
  match gd with
  | Gfun f => Gfun (transf_fundef f)
  | Gvar gu => Gvar gu
  end.

Lemma transf_globdef_proj: forall gd, globdef_proj (transf_globdef gd) = gd.
Proof.
  intros gd. destruct gd as [f|v]; simpl; auto.
  rewrite transf_fundef_proj; auto.
Qed.

Fixpoint transf_prog_defs (l: list (ident * globdef Asmblock.fundef unit))
                            : list (ident * globdef fundef unit) :=
  match l with
  | nil => nil
  | (i, gd) :: l => (i, transf_globdef gd) :: transf_prog_defs l
  end.

Lemma transf_prog_proj: forall p, prog_defs p = prog_defs_proj (transf_prog_defs (prog_defs p)).
Proof.
  intros p. destruct p as [defs pub main]. simpl.
  induction defs; simpl; auto.
  destruct a as [i gd]. simpl.
  rewrite transf_globdef_proj.
  congruence.
Qed.
 *)

Definition transf_program : Asmblock.program -> program := transform_program transf_fundef.

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

Definition match_prog (p: Asmblock.program) (tp: program) :=
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

(* I think it is a special case of Asmblock -> Asm. Very handy to have *)
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

Variable prog: Asmblock.program.
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
  forward_simulation (Asmblock.semantics prog) (semantics tprog).
Proof.
  pose proof (match_program_transf prog tprog TRANSF) as TR.
  subst. unfold semantics. rewrite transf_program_proj.

  eapply forward_simulation_step with (match_states := match_states); simpl; auto.
  - intros. exists s1. split; auto. congruence.
  - intros. inv H. auto.
  - intros. exists s1'. inv H0. split; auto. congruence.
Qed.

End PRESERVATION.
