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

(* Printing RISC-V assembly code in asm syntax *)

open Printf
open Camlcoq
open Sections
open AST
open Asm
open PrintAsmaux
open Fileinfo

(* Module containing the printing functions *)

module Target : TARGET =
  struct

(* Basic printing functions *)

    let comment = "#"

    let symbol        = elf_symbol
    let symbol_offset = elf_symbol_offset
    let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let int_reg_name = function
      | GPR0  -> "$r0"  | GPR1  -> "$r1"  | GPR2  -> "$r2"  | GPR3  -> "$r3"
      | GPR4  -> "$r4"  | GPR5  -> "$r5"  | GPR6  -> "$r6"  | GPR7  -> "$r7"
      | GPR8  -> "$r8"  | GPR9  -> "$r9"  | GPR10 -> "$r10" | GPR11 -> "$r11"
      | GPR12 -> "$r12" | GPR13 -> "$r13" | GPR14 -> "$r14" | GPR15 -> "$r15"
      | GPR16 -> "$r16" | GPR17 -> "$r17" | GPR18 -> "$r18" | GPR19 -> "$r19"
      | GPR20 -> "$r20" | GPR21 -> "$r21" | GPR22 -> "$r22" | GPR23 -> "$r23"
      | GPR24 -> "$r24" | GPR25 -> "$r25" | GPR26 -> "$r26" | GPR27 -> "$r27"
      | GPR28 -> "$r28" | GPR29 -> "$r29" | GPR30 -> "$r30" | GPR31 -> "$r31"
      | GPR32 -> "$r32" | GPR33 -> "$r33" | GPR34 -> "$r34" | GPR35 -> "$r35"
      | GPR36 -> "$r36" | GPR37 -> "$r37" | GPR38 -> "$r38" | GPR39 -> "$r39"
      | GPR40 -> "$r40" | GPR41 -> "$r41" | GPR42 -> "$r42" | GPR43 -> "$r43"
      | GPR44 -> "$r44" | GPR45 -> "$r45" | GPR46 -> "$r46" | GPR47 -> "$r47"
      | GPR48 -> "$r48" | GPR49 -> "$r49" | GPR50 -> "$r50" | GPR51 -> "$r51"
      | GPR52 -> "$r52" | GPR53 -> "$r53" | GPR54 -> "$r54" | GPR55 -> "$r55"
      | GPR56 -> "$r56" | GPR57 -> "$r57" | GPR58 -> "$r58" | GPR59 -> "$r59"
      | GPR60 -> "$r60" | GPR61 -> "$r61" | GPR62 -> "$r62" | GPR63 -> "$r63"

    let ireg oc r = output_string oc (int_reg_name r)

    let ireg = ireg

    let preg oc = function
      | IR r -> ireg oc r
      | FR r -> ireg oc r
      | RA   -> output_string oc "$ra"
      | _    -> assert false

    let preg_annot = function
      | IR r -> int_reg_name r
      | FR r -> int_reg_name r
      | RA   -> "$ra"
      | _ -> assert false

(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else "COMM"
      | Section_const i | Section_small_const i ->
          if i then ".section	.rodata" else "COMM"
      | Section_string       -> ".section	.rodata"
      | Section_literal      -> ".section	.rodata"
      | Section_jumptable    -> ".section	.rodata"
      | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
      | Section_debug_loc    -> ".section	.debug_loc,\"\",%progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
      | Section_debug_str    -> ".section	.debug_str,\"MS\",%progbits,1"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* Associate labels to floating-point constants and to symbols. *)

    let emit_constants oc lit =
      if exists_constants () then begin
         section oc lit;
         if Hashtbl.length literal64_labels > 0 then
           begin
             fprintf oc "	.align 3\n";
             Hashtbl.iter
               (fun bf lbl -> fprintf oc "%a:	.quad	0x%Lx\n" label lbl bf)
               literal64_labels
           end;
         if Hashtbl.length literal32_labels > 0 then
           begin
             fprintf oc "	.align	2\n";
             Hashtbl.iter
               (fun bf lbl ->
                  fprintf oc "%a:	.long	0x%lx\n" label lbl bf)
               literal32_labels
           end;
         reset_literals ()
      end

(* Generate code to load the address of id + ofs in register r *)

  (*let loadsymbol oc r id ofs =
      if Archi.pic_code () then begin
        assert (ofs = Integers.Ptrofs.zero);
        fprintf oc "	la	%a, %s\n" ireg r (extern_atom id)
      end else begin
        fprintf oc "	lui	%a, %%hi(%a)\n"
                                ireg r symbol_offset (id, ofs);
        fprintf oc "	addi	%a, %a, %%lo(%a)\n"
                                ireg r ireg r symbol_offset (id, ofs)
      end
  *)
(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

(*
    let print_location oc loc =
      if loc <> Cutil.no_loc then print_file_line oc (fst loc) (snd loc)
*)

(* Add "w" suffix to 32-bit instructions if we are in 64-bit mode *)
  
  (*let w oc =
      if Archi.ptr64 then output_string oc "w"
  *)
(* Offset part of a load or store *)

    let offset oc = function
    | Ofsimm n -> ptrofs oc n
    | Ofslow(id, ofs) -> fprintf oc "%%lo(%a)" symbol_offset (id, ofs)

(* Printing of instructions *)
    let print_instruction oc = function
      | Pcall(s) ->
         fprintf oc "	call	%a\n;;\n" symbol s
      | Pgoto(s) | Pj_l(s) ->
         fprintf oc "	goto	%a\n;;\n" symbol s
      | Pret ->
         fprintf oc "	ret\n;;\n"
      | Pget (rd, rs) ->
         fprintf oc "	get	%a = %a\n;;\n" ireg rd preg rs
      | Pset (rd, rs) ->
         fprintf oc "	set	%a = %a\n;;\n" preg rd ireg rs
      | Pmv(rd, rs) ->
         fprintf oc "	addd	%a = %a, 0\n;;\n"     ireg rd ireg rs

      (* 32-bit integer register-immediate instructions *)
      | Paddiw (rd, rs, imm) ->
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs coqint64 imm
    (*| Psltiw (rd, rs, imm) ->
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg rs coqint imm
      | Psltiuw (rd, rs, imm) ->
         fprintf oc "	sltiu	%a, %a, %a\n" ireg rd ireg rs coqint imm
      | Pandiw (rd, rs, imm) ->
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg rs coqint imm
      | Poriw (rd, rs, imm) ->
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg rs coqint imm
      | Pxoriw (rd, rs, imm) ->
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg rs coqint imm
      | Pslliw (rd, rs, imm) ->
         fprintf oc "	slli%t	%a, %a, %a\n" w ireg rd ireg rs coqint imm
      | Psrliw (rd, rs, imm) ->
         fprintf oc "	srli%t	%a, %a, %a\n" w ireg rd ireg rs coqint imm
      | Psraiw (rd, rs, imm) ->
         fprintf oc "	srai%t	%a, %a, %a\n" w ireg rd ireg rs coqint imm
      | Pluiw (rd, imm) ->
         fprintf oc "	lui	%a, %a\n"     ireg rd coqint imm

      (* 32-bit integer register-register instructions *)
    *)| Paddw(rd, rs1, rs2) ->
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs1 ireg rs2
    (*| Psubw(rd, rs1, rs2) ->
         fprintf oc "	sub%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2

      | Pmulw(rd, rs1, rs2) ->
         fprintf oc "	mul%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2
      | Pmulhw(rd, rs1, rs2) ->  assert (not Archi.ptr64);
         fprintf oc "	mulh	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmulhuw(rd, rs1, rs2) ->  assert (not Archi.ptr64);
         fprintf oc "	mulhu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pdivw(rd, rs1, rs2) ->
         fprintf oc "	div%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2
      | Pdivuw(rd, rs1, rs2) ->
         fprintf oc "	divu%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2
      | Premw(rd, rs1, rs2) ->
         fprintf oc "	rem%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2
      | Premuw(rd, rs1, rs2) ->
         fprintf oc "	remu%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2

      | Psltw(rd, rs1, rs2) ->
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psltuw(rd, rs1, rs2) ->
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pandw(rd, rs1, rs2) ->
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Porw(rd, rs1, rs2) ->
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pxorw(rd, rs1, rs2) ->
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psllw(rd, rs1, rs2) ->
         fprintf oc "	sll%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2
      | Psrlw(rd, rs1, rs2) ->
         fprintf oc "	srl%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2
      | Psraw(rd, rs1, rs2) ->
         fprintf oc "	sra%t	%a, %a, %a\n" w ireg rd ireg rs1 ireg rs2

    *)(* 64-bit integer register-immediate instructions *)
      | Paddil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs coqint64 imm
    (*| Psltil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psltiul (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	sltiu	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pandil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Poril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pxoril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psllil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	slli	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrlil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	srli	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrail (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	srai	%a, %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pluil (rd, imm) -> assert Archi.ptr64;
         fprintf oc "	lui	%a, %a\n"     ireg rd coqint64 imm
    *)
      | Pmake (rd, imm) ->
         fprintf oc "	make	%a, %a\n;;\n" ireg rd coqint imm
      | Pmakel (rd, imm) ->
         fprintf oc "	make	%a, %a\n;;\n" ireg rd coqint64 imm
      (* 64-bit integer register-register instructions *)
      | Paddl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs1 ireg rs2
    (*| Psubl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sub	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pmull(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	mul	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmulhl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	mulh	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmulhul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	mulhu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pdivl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	div	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pdivul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	divu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Preml(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	rem	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Premul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	remu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Psltl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psltul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pandl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Porl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pxorl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pslll(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sll	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrll(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	srl	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psral(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sra	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2
  
      (* Unconditional jumps.  Links are always to X1/RA. *)
      (* TODO: fix up arguments for calls to variadics, to move *)
      (* floating point arguments to integer registers.  How? *)
      | Pj_l(l) ->
         fprintf oc "	j	%a\n" print_label l
      | Pj_s(s, sg) ->
         fprintf oc "	j	%a\n" symbol s
      | Pj_r(r, sg) ->
         fprintf oc "	jr	%a\n" ireg r
      | Pjal_s(s, sg) ->
         fprintf oc "	call	%a\n" symbol s
      | Pjal_r(r, sg) ->
         fprintf oc "	jalr	%a\n" ireg r

      (* Conditional branches, 32-bit comparisons *)
      | Pbeqw(rs1, rs2, l) ->
         fprintf oc "	beq	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbnew(rs1, rs2, l) ->
         fprintf oc "	bne	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbltw(rs1, rs2, l) ->
         fprintf oc "	blt	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbltuw(rs1, rs2, l) ->
         fprintf oc "	bltu	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbgew(rs1, rs2, l) ->
         fprintf oc "	bge	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbgeuw(rs1, rs2, l) ->
         fprintf oc "	bgeu	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l

      (* Conditional branches, 64-bit comparisons *)
      | Pbeql(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	beq	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbnel(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bne	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbltl(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	blt	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbltul(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bltu	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbgel(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bge	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l
      | Pbgeul(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bgeu	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l

      (* Loads and stores *)
      | Plb(rd, ra, ofs) ->
         fprintf oc "	lb	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plbu(rd, ra, ofs) ->
         fprintf oc "	lbu	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plh(rd, ra, ofs) ->
         fprintf oc "	lh	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plhu(rd, ra, ofs) ->
         fprintf oc "	lhu	%a, %a(%a)\n" ireg rd offset ofs ireg ra
    *)| Plw(rd, ra, ofs) | Plw_a(rd, ra, ofs) | Pfls(rd, ra, ofs) ->
         fprintf oc "	lws	%a = %a[%a]\n" ireg rd offset ofs ireg ra
      | Pld(rd, ra, ofs) | Pfld(rd, ra, ofs) | Pld_a(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	ld	%a = %a[%a]\n;;\n" ireg rd offset ofs ireg ra

    (*| Psb(rd, ra, ofs) ->
         fprintf oc "	sb	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Psh(rd, ra, ofs) ->
         fprintf oc "	sh	%a, %a(%a)\n" ireg rd offset ofs ireg ra
    *)| Psw(rd, ra, ofs) | Psw_a(rd, ra, ofs) | Pfss(rd, ra, ofs) ->
         fprintf oc "	sw	%a[%a] = %a\n" offset ofs ireg ra ireg rd
      | Psd(rd, ra, ofs) | Psd_a(rd, ra, ofs) | Pfsd(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	sd	%a[%a] = %a\n;;\n" offset ofs ireg ra ireg rd


      (* Synchronization *)
    (*| Pfence ->
         fprintf oc "	fence\n"

      (* floating point register move.
         fmv.d preserves single-precision register contents, and hence
         is applicable to both single- and double-precision moves.
       *)
      | Pfmv (fd,fs) ->
         fprintf oc "	fmv.d	%a, %a\n"     freg fd freg fs
      | Pfmvxs (rd,fs) ->
         fprintf oc "	fmv.x.s	%a, %a\n"     ireg rd freg fs
      | Pfmvxd (rd,fs) ->
         fprintf oc "	fmv.x.d	%a, %a\n"     ireg rd freg fs

      (* 32-bit (single-precision) floating point *)
      | Pfls (fd, ra, ofs) ->
         fprintf oc "	flw	%a, %a(%a)\n" freg fd offset ofs ireg ra
      | Pfss (fs, ra, ofs) ->
         fprintf oc "	fsw	%a, %a(%a)\n" freg fs offset ofs ireg ra

      | Pfnegs (fd, fs) ->
         fprintf oc "	fneg.s	%a, %a\n"     freg fd freg fs
      | Pfabss (fd, fs) ->
         fprintf oc "	fabs.s	%a, %a\n"     freg fd freg fs

      | Pfadds (fd, fs1, fs2) ->
         fprintf oc "	fadd.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfsubs (fd, fs1, fs2) ->
         fprintf oc "	fsub.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmuls (fd, fs1, fs2) ->
         fprintf oc "	fmul.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfdivs (fd, fs1, fs2) ->
         fprintf oc "	fdiv.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmins (fd, fs1, fs2) ->
         fprintf oc "	fmin.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmaxs (fd, fs1, fs2) ->
         fprintf oc "	fmax.s	%a, %a, %a\n" freg fd freg fs1 freg fs2

      | Pfeqs (rd, fs1, fs2) ->
         fprintf oc "	feq.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pflts (rd, fs1, fs2) ->
         fprintf oc "	flt.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pfles (rd, fs1, fs2) ->
         fprintf oc "	fle.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2

      | Pfsqrts (fd, fs) ->
         fprintf oc "	fsqrt.s %a, %a\n"     freg fd freg fs

      | Pfmadds (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmadd.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfmsubs (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmsub.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmadds (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmadd.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmsubs (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmsub.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3

      | Pfcvtws (rd, fs) ->
         fprintf oc "	fcvt.w.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtwus (rd, fs) ->
         fprintf oc "	fcvt.wu.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtsw (fd, rs) ->
         fprintf oc "	fcvt.s.w	%a, %a\n" freg fd ireg rs
      | Pfcvtswu (fd, rs) ->
         fprintf oc "	fcvt.s.wu	%a, %a\n" freg fd ireg rs

      | Pfcvtls (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.l.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtlus (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.lu.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtsl (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.s.l	%a, %a\n" freg fd ireg rs
      | Pfcvtslu (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.s.lu	%a, %a\n" freg fd ireg rs

      (* 64-bit (double-precision) floating point *)
      | Pfld (fd, ra, ofs) | Pfld_a (fd, ra, ofs) ->
         fprintf oc "	fld	%a, %a(%a)\n" freg fd offset ofs ireg ra
      | Pfsd (fs, ra, ofs) | Pfsd_a (fs, ra, ofs) ->
         fprintf oc "	fsd	%a, %a(%a)\n" freg fs offset ofs ireg ra

      | Pfnegd (fd, fs) ->
         fprintf oc "	fneg.d	%a, %a\n"     freg fd freg fs
      | Pfabsd (fd, fs) ->
         fprintf oc "	fabs.d	%a, %a\n"     freg fd freg fs

      | Pfaddd (fd, fs1, fs2) ->
         fprintf oc "	fadd.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfsubd (fd, fs1, fs2) ->
         fprintf oc "	fsub.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmuld (fd, fs1, fs2) ->
         fprintf oc "	fmul.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfdivd (fd, fs1, fs2) ->
         fprintf oc "	fdiv.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmind (fd, fs1, fs2) ->
         fprintf oc "	fmin.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmaxd (fd, fs1, fs2) ->
         fprintf oc "	fmax.d	%a, %a, %a\n" freg fd freg fs1 freg fs2

      | Pfeqd (rd, fs1, fs2) ->
         fprintf oc "	feq.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pfltd (rd, fs1, fs2) ->
         fprintf oc "	flt.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pfled (rd, fs1, fs2) ->
         fprintf oc "	fle.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2

      | Pfsqrtd (fd, fs) ->
         fprintf oc "	fsqrt.d	%a, %a\n" freg fd freg fs

      | Pfmaddd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmadd.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfmsubd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmsub.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmaddd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmadd.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmsubd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmsub.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3

      | Pfcvtwd (rd, fs) ->
         fprintf oc "	fcvt.w.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtwud (rd, fs) ->
         fprintf oc "	fcvt.wu.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtdw (fd, rs) ->
         fprintf oc "	fcvt.d.w	%a, %a\n" freg fd ireg rs
      | Pfcvtdwu (fd, rs) ->
         fprintf oc "	fcvt.d.wu	%a, %a\n" freg fd ireg rs

      | Pfcvtld (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.l.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtlud (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.lu.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtdl (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.d.l	%a, %a\n" freg fd ireg rs
      | Pfcvtdlu (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.d.lu	%a, %a\n" freg fd ireg rs

      | Pfcvtds (fd, fs) ->
         fprintf oc "	fcvt.d.s	%a, %a\n" freg fd freg fs
      | Pfcvtsd (fd, fs) ->
         fprintf oc "	fcvt.s.d	%a, %a\n" freg fd freg fs

      (* Pseudo-instructions expanded in Asmexpand *)
    *)| Pallocframe(sz, ofs) ->
         assert false
      | Pfreeframe(sz, ofs) ->
         assert false
    (*| Pseqw _ | Psnew _ | Pseql _ | Psnel _ | Pcvtl2w _ | Pcvtw2l _ ->
         assert false

      (* Pseudo-instructions that remain *)
    *)| Plabel lbl ->
         fprintf oc "%a:\n" print_label lbl
    (*| Ploadsymbol(rd, id, ofs) ->
         loadsymbol oc rd id ofs
      | Ploadsymbol_high(rd, id, ofs) ->
         fprintf oc "	lui	%a, %%hi(%a)\n" ireg rd symbol_offset (id, ofs)
      | Ploadli(rd, n) ->
         let d = camlint64_of_coqint n in
         let lbl = label_literal64 d in
         fprintf oc "	ld	%a, %a %s %Lx\n" ireg rd label lbl comment d
      | Ploadfi(rd, f) ->
         let d   = camlint64_of_coqint(Floats.Float.to_bits f) in
         let lbl = label_literal64 d in
         fprintf oc "	fld	%a, %a, x31 %s %.18g\n"
                    freg rd label lbl comment (camlfloat_of_coqfloat f)
      | Ploadsi(rd, f) ->
         let s   = camlint_of_coqint(Floats.Float32.to_bits f) in
         let lbl = label_literal32 s in
         fprintf oc "	flw	%a, %a, x31 %s %.18g\n"
                    freg rd label lbl comment (camlfloat_of_coqfloat32 f)
      | Pbtbl(r, tbl) ->
         let lbl = new_label() in
         fprintf oc "%s jumptable [ " comment;
         List.iter (fun l -> fprintf oc "%a " print_label l) tbl;
         fprintf oc "]\n";
         fprintf oc "	sll	x5, %a, 2\n" ireg r;
         fprintf oc "	la	x31, %a\n" label lbl;
         fprintf oc "	add	x5, x31, x5\n";
         fprintf oc "	lw	x5, 0(x5)\n";
         fprintf oc "	add	x5, x31, x5\n";
         fprintf oc "	jr	x5\n";
         jumptables := (lbl, tbl) :: !jumptables;
         fprintf oc "%s end pseudoinstr btbl\n" comment
    *)| Pbuiltin(ef, args, res) ->
         begin match ef with
           | EF_annot(kind,txt, targs) ->
             let annot =
             begin match (P.to_int kind) with
               | 1 -> annot_text preg_annot "sp" (camlstring_of_coqstring txt) args
               | 2 -> let lbl = new_label () in
                 fprintf oc "%a: " label lbl;
                 ais_annot_text lbl preg_annot "r1" (camlstring_of_coqstring txt) args
               | _ -> assert false
             end in
             fprintf oc "%s annotation: %S\n" comment annot
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg_annot "sp" oc
                               (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | _ ->
              assert false
         end

    let get_section_names name =
      let (text, lit) =
        match C2C.atom_sections name with
        | t :: l :: _ -> (t, l)
        | _    -> (Section_text, Section_literal) in
      text,lit,Section_jumptable

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment

    let print_jumptable oc jmptbl =
      let print_tbl oc (lbl, tbl) =
        fprintf oc "%a:\n" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a - %a\n"
                               print_label l label lbl)
          tbl in
      if !jumptables <> [] then
        begin
          section oc jmptbl;
          fprintf oc "	.balign 4\n";
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end

    let print_fun_info = elf_print_fun_info

    let print_optional_fun_info _ = ()

    let print_var_info = elf_print_var_info

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name then
        fprintf oc "	.local	%a\n" symbol name;
        fprintf oc "	.comm	%a, %s, %d\n"
        symbol name
        (Z.to_string sz)
        align

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      List.iter (print_instruction oc) fn.fn_code


(* Data *)

    let address = if Archi.ptr64 then ".quad" else ".long"

    let print_prologue oc =
   (* fprintf oc "	.option %s\n" (if Archi.pic_code() then "pic" else "nopic"); *)
      if !Clflags.option_g then begin
        section oc Section_text;
      end

    let print_epilogue oc =
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let default_falignment = 2

    let cfi_startproc oc = ()
    let cfi_endproc oc = ()

  end

let sel_target () =
  (module Target:TARGET)
