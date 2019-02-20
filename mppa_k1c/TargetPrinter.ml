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

module Target (*: TARGET*) =
  struct

(* Basic printing functions *)

    let comment = "#"

    let symbol        = elf_symbol
    let symbol_offset = elf_symbol_offset
    let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let int_reg_name = let open Asmblock in function
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

    let preg oc = let open Asmblock in function
      | IR r -> ireg oc r
      | RA   -> output_string oc "$ra"
      | _ -> assert false

    let preg_annot = let open Asmblock in function
      | IR r -> int_reg_name r
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

(* FIXME DMonniaux ugly ugly hack to get at standard __thread data *)
    let loadsymbol oc r id ofs =
      if Archi.pic_code () then begin
        assert (ofs = Integers.Ptrofs.zero);
        fprintf oc "	make	%a = %s\n" ireg r (extern_atom id)
      end else begin
        if (extern_atom id) = "_impure_thread_data" then begin
            fprintf oc "	make	%a = @tprel(%a)\n;;\n	addd	%a = %a, $r13\n" ireg r symbol_offset (id, ofs) ireg r ireg r               
        end else begin            
            fprintf oc "	make	%a = %a\n" ireg r symbol_offset (id, ofs)
        end
      end
    
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

    let offset oc = let open Asmblock in function
    | Ofsimm n -> ptrofs oc n
    | Ofslow(id, ofs) -> fprintf oc "%%lo(%a)" symbol_offset (id, ofs)

    let icond_name = let open Asmblock in function
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
  
    let bcond_name = let open Asmblock in function
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
    exception ShouldBeExpanded

    let print_instruction oc = function
      (* Pseudo-instructions expanded in Asmexpand *)
      | Pallocframe(sz, ofs) -> assert false
      | Pfreeframe(sz, ofs) -> assert false

      (* Pseudo-instructions that remain *)
      | Plabel lbl ->
         fprintf oc "%a:\n" print_label lbl
      | Ploadsymbol(rd, id, ofs) ->
         loadsymbol oc rd id ofs
      | Pbuiltin(ef, args, res) ->
         begin match ef with
          | EF_annot(kind,txt, targs) ->
            begin match (P.to_int kind) with
              | 1 -> let annot = annot_text preg_annot "x2" (camlstring_of_coqstring txt) args  in
                fprintf oc "%s annotation: %S\n" comment annot
            (*| 2 -> let lbl = new_label () in
                fprintf oc "%a: " label lbl;
                add_ais_annot lbl preg_annot "x2" (camlstring_of_coqstring txt) args
            *)| _ -> assert false
            end
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
      | Pnop -> fprintf oc "	nop\n"
      | Psemi -> fprintf oc ";;\n"

      | Pclzll (rd, rs) -> fprintf oc "	clzd %a = %a\n" ireg rd ireg rs
      | Pstsud (rd, rs1, rs2) -> fprintf oc "	stsud %a = %a, %a\n" ireg rd ireg rs1 ireg rs2


      (* Control flow instructions *)
      | Pget (rd, rs) ->
         fprintf oc "	get	%a = %a\n" ireg rd preg rs
      | Pset (rd, rs) ->
         fprintf oc "	set	%a = %a\n" preg rd ireg rs
      | Pret ->
         fprintf oc "	ret	\n"
      | Pcall(s) ->
         fprintf oc "	call	%a\n" symbol s
      | Picall(rs) ->
         fprintf oc "	icall	%a\n" ireg rs
      | Pgoto(s) ->
         fprintf oc "	goto	%a\n" symbol s
      | Pigoto(rs) ->
         fprintf oc "	igoto	%a\n" ireg rs
      | Pj_l(s) ->
         fprintf oc "	goto	%a\n" print_label s
      | Pcb (bt, r, lbl) | Pcbu (bt, r, lbl) ->
         fprintf oc "	cb.%a	%a? %a\n" bcond bt ireg r print_label lbl
      | Ploopdo (r, lbl) ->
         fprintf oc "	loopdo	%a, %a\n" ireg r print_label lbl        

      (* Load/Store instructions *)
      | Plb(rd, ra, ofs) ->
         fprintf oc "	lbs	%a = %a[%a]\n" ireg rd offset ofs ireg ra
      | Plbu(rd, ra, ofs) ->
         fprintf oc "	lbz	%a = %a[%a]\n" ireg rd offset ofs ireg ra
      | Plh(rd, ra, ofs) ->
         fprintf oc "	lhs	%a = %a[%a]\n" ireg rd offset ofs ireg ra
      | Plhu(rd, ra, ofs) ->
         fprintf oc "	lhz	%a = %a[%a]\n" ireg rd offset ofs ireg ra
      | Plw(rd, ra, ofs) | Plw_a(rd, ra, ofs) | Pfls(rd, ra, ofs) ->
         fprintf oc "	lws	%a = %a[%a]\n" ireg rd offset ofs ireg ra
      | Pld(rd, ra, ofs) | Pfld(rd, ra, ofs) | Pld_a(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	ld	%a = %a[%a]\n" ireg rd offset ofs ireg ra
    
      | Psb(rd, ra, ofs) ->
         fprintf oc "	sb	%a[%a] = %a\n" offset ofs ireg ra ireg rd
      | Psh(rd, ra, ofs) ->
         fprintf oc "	sh	%a[%a] = %a\n" offset ofs ireg ra ireg rd
      | Psw(rd, ra, ofs) | Psw_a(rd, ra, ofs) | Pfss(rd, ra, ofs) ->
         fprintf oc "	sw	%a[%a] = %a\n" offset ofs ireg ra ireg rd
      | Psd(rd, ra, ofs) | Psd_a(rd, ra, ofs) | Pfsd(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	sd	%a[%a] = %a\n" offset ofs ireg ra ireg rd

      (* Arith R instructions *)

      (* Arith RR instructions *)
      | Pmv(rd, rs) ->
         fprintf oc "	addd	%a = %a, 0\n"     ireg rd ireg rs
      | Pcvtl2w(rd, rs) -> assert false
      | Pnegl(rd, rs) -> assert Archi.ptr64;
         fprintf oc "	negd	%a = %a\n" ireg rd ireg rs
      | Pnegw(rd, rs) ->
         fprintf oc "	negw	%a = %a\n" ireg rd ireg rs
      | Psxwd(rd, rs) ->
         fprintf oc "	sxwd	%a = %a\n" ireg rd ireg rs
      | Pzxwd(rd, rs) ->
         fprintf oc "	zxwd	%a = %a\n" ireg rd ireg rs
      | Pfabsd(rd, rs) ->
         fprintf oc "	fabsd	%a = %a\n" ireg rd ireg rs
      | Pfabsw(rd, rs) ->
         fprintf oc "	fabsw	%a = %a\n" ireg rd ireg rs
      | Pfnegd(rd, rs) ->
         fprintf oc "	fnegd	%a = %a\n" ireg rs ireg rd
      | Pfnegw(rd, rs) ->
         fprintf oc "	fnegw	%a = %a\n" ireg rs ireg rd
      | Pfnarrowdw(rd, rs) ->
         fprintf oc "	fnarrowdw	%a = %a\n" ireg rs ireg rd
      | Pfwidenlwd(rd, rs) ->
         fprintf oc "	fwidenlwd	%a = %a\n" ireg rs ireg rd
      | Pfloatwrnsz(rd, rs) ->
         fprintf oc "	floatw.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfloatudrnsz(rd, rs) ->
         fprintf oc "	floatud.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfloatdrnsz(rd, rs) ->
         fprintf oc "	floatd.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfixedwrzz(rd, rs) ->
         fprintf oc "	fixedw.rz	%a = %a, 0\n" ireg rd ireg rs
      | Pfixeddrzz(rd, rs) ->
         fprintf oc "	fixedd.rz	%a = %a, 0\n" ireg rd ireg rs

      (* Arith RI32 instructions *)
      | Pmake (rd, imm) ->
         fprintf oc "	make	%a, %a\n" ireg rd coqint imm

      (* Arith RI64 instructions *)
      | Pmakel (rd, imm) ->
         fprintf oc "	make	%a, %a\n" ireg rd coqint64 imm

      (* Arith RF32 instructions *)
      | Pmakefs (rd, f) ->
         let d   = Floats.Float32.to_bits f in
         fprintf oc "	make	%a, %a %s %.18g\n"
                    ireg rd coqint d comment (camlfloat_of_coqfloat32 f)

      (* Arith RF64 instructions *)
      | Pmakef (rd, f) ->
         let d   = Floats.Float.to_bits f in
         fprintf oc "	make	%a, %a %s %.18g\n"
                    ireg rd coqint64 d comment (camlfloat_of_coqfloat f)

      (* Arith RRR instructions *)
      | Pcompw (it, rd, rs1, rs2) ->
         fprintf oc "	compw.%a	%a = %a, %a\n" icond it ireg rd ireg rs1 ireg rs2
      | Pcompl (it, rd, rs1, rs2) ->
         fprintf oc "	compd.%a	%a = %a, %a\n" icond it ireg rd ireg rs1 ireg rs2

      | Paddw (rd, rs1, rs2) ->
         fprintf oc "	addw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psubw (rd, rs1, rs2) ->
         fprintf oc "	sbfw	%a = %a, %a\n" ireg rd ireg rs2 ireg rs1
      | Pmulw (rd, rs1, rs2) ->
         fprintf oc "	mulw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pandw (rd, rs1, rs2) ->
         fprintf oc "	andw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Porw (rd, rs1, rs2) -> 
         fprintf oc "	orw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pxorw (rd, rs1, rs2) -> 
         fprintf oc "	xorw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psraw (rd, rs1, rs2) ->
         fprintf oc "	sraw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrlw (rd, rs1, rs2) ->
         fprintf oc "	srlw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psllw (rd, rs1, rs2) ->
         fprintf oc "	sllw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Paddl (rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psubl (rd, rs1, rs2) ->
         fprintf oc "	sbfd	%a = %a, %a\n" ireg rd ireg rs2 ireg rs1
      | Pandl (rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	andd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Porl (rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	ord	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pxorl (rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	xord	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmull (rd, rs1, rs2) ->
         fprintf oc "	muld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pslll  (rd, rs1, rs2) ->
         fprintf oc "	slld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrll  (rd, rs1, rs2) ->
         fprintf oc "	srld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psral   (rd, rs1, rs2) ->
         fprintf oc "	srad	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pfaddd (rd, rs1, rs2) ->
         fprintf oc "	faddd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfaddw (rd, rs1, rs2) ->
         fprintf oc "	faddw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfsbfd (rd, rs1, rs2) ->
         fprintf oc "	fsbfd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfsbfw (rd, rs1, rs2) ->
         fprintf oc "	fsbfw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmuld (rd, rs1, rs2) ->
         fprintf oc "	fmuld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmulw (rd, rs1, rs2) ->
         fprintf oc "	fmulw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2

      (* Arith RRI32 instructions *)
      | Pcompiw (it, rd, rs, imm) ->
         fprintf oc "	compw.%a	%a = %a, %a\n" icond it ireg rd ireg rs coqint64 imm
      | Paddiw (rd, rs, imm) ->
         fprintf oc "	addw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pandiw (rd, rs, imm) ->
         fprintf oc "	andw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Poriw (rd, rs, imm) -> 
         fprintf oc "	orw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pxoriw (rd, rs, imm) -> 
         fprintf oc "	xorw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psraiw (rd, rs, imm) ->
         fprintf oc "	sraw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrliw (rd, rs, imm) ->
         fprintf oc "	srlw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pslliw (rd, rs, imm) ->
         fprintf oc "	sllw	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psllil (rd, rs, imm) ->
         fprintf oc "	slld	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrlil (rd, rs, imm) ->
         fprintf oc "	srld	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrail (rd, rs, imm) ->
         fprintf oc "	srad	%a = %a, %a\n" ireg rd ireg rs coqint64 imm

    (* Arith RRI64 instructions *)
      | Pcompil (it, rd, rs, imm) ->
         fprintf oc "	compd.%a	%a = %a, %a\n" icond it ireg rd ireg rs coqint64 imm
      | Paddil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pandil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	andd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Poril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	ord	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pxoril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	xord	%a = %a, %a\n" ireg rd ireg rs coqint64 imm

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
