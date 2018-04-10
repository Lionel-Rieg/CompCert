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

    let icond_name = function
      | ITne | ITneu -> "ne"
      | ITeq | ITequ -> "eq"
      | ITlt   -> "lt"
      | ITge   -> "ge"
      | ITle   -> "le"
      | ITgt   -> "gt"
      | ITltu  -> "ltu"
      | ITgeu  -> "geu"
      | ITleu  -> "leu"
      | ITgtu  -> "gtu"
      | ITall  -> "all"
      | ITnall -> "nall"
      | ITany  -> "any"
      | ITnone -> "none"

    let icond oc c = fprintf oc "%s" (icond_name c)
  
    let bcond_name = function
      | BTwnez -> "wnez"
      | BTweqz -> "weqz"
      | BTwltz -> "wltz"
      | BTwgez -> "wgez"
      | BTwlez -> "wlez"
      | BTwgtz -> "wgtz"
      | BTdnez -> "dnez"
      | BTdeqz -> "deqz"
      | BTdltz -> "dltz"
      | BTdgez -> "dgez"
      | BTdlez -> "dlez"
      | BTdgtz -> "dgtz"

    let bcond oc c = fprintf oc "%s" (bcond_name c)

(* Printing of instructions *)
    let print_instruction oc = function
      | Pcall(s) ->
         fprintf oc "	call	%a\n;;\n" symbol s
      | Pgoto(s) | Pj_l(s) ->
         fprintf oc "	goto	%a\n;;\n" print_label s
      | Pret ->
         fprintf oc "	ret\n;;\n"
      | Pget (rd, rs) ->
         fprintf oc "	get	%a = %a\n;;\n" ireg rd preg rs
      | Pset (rd, rs) ->
         fprintf oc "	set	%a = %a\n;;\n" preg rd ireg rs
      | Pmv(rd, rs) ->
         fprintf oc "	addd	%a = %a, 0\n;;\n"     ireg rd ireg rs

      | Paddiw (rd, rs, imm) ->
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs coqint64 imm
      | Paddw(rd, rs1, rs2) ->
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs1 ireg rs2
      | Paddil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs coqint64 imm
      | Pmake (rd, imm) ->
         fprintf oc "	make	%a, %a\n;;\n" ireg rd coqint imm
      | Pmakel (rd, imm) ->
         fprintf oc "	make	%a, %a\n;;\n" ireg rd coqint64 imm
      | Paddl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n;;\n" ireg rd ireg rs1 ireg rs2
      | Pnegl(rd, rs) -> assert Archi.ptr64;
         fprintf oc "	negd	%a = %a\n;;\n" ireg rd ireg rs
      | Pnegw(rd, rs) ->
         fprintf oc "	negw	%a = %a\n;;\n" ireg rd ireg rs

      | Pcompw (it, rd, rs1, rs2) ->
         fprintf oc "	compw.%a	%a = %a, %a\n;;\n" icond it ireg rd ireg rs1 ireg rs2
      | Pcompd (it, rd, rs1, rs2) ->
         fprintf oc "	compd.%a	%a = %a, %a\n;;\n" icond it ireg rd ireg rs1 ireg rs2
      | Pcb (bt, r, lbl) ->
         fprintf oc "	cb.%a	%a?%a\n;;\n" bcond bt ireg r print_label lbl

      | Plw(rd, ra, ofs) | Plw_a(rd, ra, ofs) | Pfls(rd, ra, ofs) ->
         fprintf oc "	lws	%a = %a[%a]\n;;\n" ireg rd offset ofs ireg ra
      | Pld(rd, ra, ofs) | Pfld(rd, ra, ofs) | Pld_a(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	ld	%a = %a[%a]\n;;\n" ireg rd offset ofs ireg ra
      | Psw(rd, ra, ofs) | Psw_a(rd, ra, ofs) | Pfss(rd, ra, ofs) ->
         fprintf oc "	sw	%a[%a] = %a\n;;\n" offset ofs ireg ra ireg rd
      | Psd(rd, ra, ofs) | Psd_a(rd, ra, ofs) | Pfsd(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	sd	%a[%a] = %a\n;;\n" offset ofs ireg ra ireg rd

      (* Pseudo-instructions expanded in Asmexpand *)
      | Pallocframe(sz, ofs) ->
         assert false
      | Pfreeframe(sz, ofs) ->
         assert false

      (* Pseudo-instructions that remain *)
      | Plabel lbl ->
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
         (*| EF_annot(kind,txt, targs) ->
             begin match (P.to_int kind) with
               | 1 -> let annot = annot_text preg_annot "x2" (camlstring_of_coqstring txt) args  in
                 fprintf oc "%s annotation: %S\n" comment annot
               | 2 -> let lbl = new_label () in
                 fprintf oc "%a: " label lbl;
                 add_ais_annot lbl preg_annot "x2" (camlstring_of_coqstring txt) args
               | _ -> assert false
             end
        *)| EF_debug(kind, txt, targs) ->
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
