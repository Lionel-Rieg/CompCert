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

    type idiv_function_kind =
      | Idiv_system
      | Idiv_stsud
      | Idiv_fp;;

    let idiv_function_kind = function
        "stsud" -> Idiv_stsud
      | "system" -> Idiv_system
      | "fp" -> Idiv_fp
      | _ -> failwith "unknown integer division kind";;
    
    let idiv_function_kind_32bit () = idiv_function_kind !Clflags.option_div_i32;;
    let idiv_function_kind_64bit () = idiv_function_kind !Clflags.option_div_i64;;
    
    let subst_symbol = function
        "__compcert_i64_udiv" ->
        (match idiv_function_kind_64bit () with
         | Idiv_system | Idiv_fp -> "__udivdi3"
         | Idiv_stsud -> "__compcert_i64_udiv_stsud")
      | "__compcert_i64_sdiv" ->
        (match idiv_function_kind_64bit() with
         | Idiv_system | Idiv_fp -> "__divdi3"
         | Idiv_stsud -> "__compcert_i64_sdiv_stsud")
      | "__compcert_i64_umod" ->
        (match idiv_function_kind_64bit() with
         | Idiv_system | Idiv_fp -> "__umoddi3"
         | Idiv_stsud -> "__compcert_i64_umod_stsud")
      | "__compcert_i64_smod" ->
        (match idiv_function_kind_64bit() with
         | Idiv_system | Idiv_fp -> "__moddi3"
         | Idiv_stsud -> "__compcert_i64_smod_stsud")
      | "__compcert_i32_sdiv" as s ->
        (match idiv_function_kind_32bit() with
         | Idiv_system -> s
         | Idiv_fp -> "__compcert_i32_sdiv_fp"
         | Idiv_stsud -> "__compcert_i32_sdiv_stsud")
      | "__compcert_i32_udiv" as s ->
        (match idiv_function_kind_32bit() with
         | Idiv_system -> s
         | Idiv_fp -> "__compcert_i32_udiv_fp"
         | Idiv_stsud -> "__compcert_i32_udiv_stsud")
      | "__compcert_i32_smod" as s ->
        (match idiv_function_kind_32bit() with
         | Idiv_system -> s
         | Idiv_fp -> "__compcert_i32_smod_fp"
         | Idiv_stsud -> "__compcert_i32_smod_stsud")
      | "__compcert_i32_umod" as s ->
        (match idiv_function_kind_32bit() with
         | Idiv_system -> s
         | Idiv_fp -> "__compcert_i32_umod_fp"
         | Idiv_stsud -> "__compcert_i32_umod_stsud")
      | "__compcert_f64_div" -> "__divdf3"
      | "__compcert_f32_div" -> "__divsf3"
      | x -> x;;
    
    let symbol oc symb =
      fprintf oc "%s" (subst_symbol (extern_atom symb))

    let symbol_offset oc (symb, ofs) =
      symbol oc symb;
      let ofs = camlint64_of_ptrofs ofs in
      if ofs <> 0L then fprintf oc " + %Ld" ofs

  let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let int_reg_name = let open Asmvliw in function
                                          
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

    let int_gpreg_q_name =
      let open Asmvliw in
      function
      | R0R1 -> "$r0r1"
      | R2R3 -> "$r2r3"
      | R4R5 -> "$r4r5"
      | R6R7 -> "$r6r7"
      | R8R9 -> "$r8r9"
      | R10R11 -> "$r10r11"
      | R12R13 -> "$r12r13"
      | R14R15 -> "$r14r15"
      | R16R17 -> "$r16r17"
      | R18R19 -> "$r18r19"
      | R20R21 -> "$r20r21"
      | R22R23 -> "$r22r23"
      | R24R25 -> "$r24r25"
      | R26R27 -> "$r26r27"
      | R28R29 -> "$r28r29"
      | R30R31 -> "$r30r31"
      | R32R33 -> "$r32r33"
      | R34R35 -> "$r34r35"
      | R36R37 -> "$r36r37"
      | R38R39 -> "$r38r39"
      | R40R41 -> "$r40r41"
      | R42R43 -> "$r42r43"
      | R44R45 -> "$r44r45"
      | R46R47 -> "$r46r47"
      | R48R49 -> "$r48r49"
      | R50R51 -> "$r50r51"
      | R52R53 -> "$r52r53"
      | R54R55 -> "$r54r55"
      | R56R57 -> "$r56r57"
      | R58R59 -> "$r58r59"
      | R60R61 -> "$r60r61"
      | R62R63 -> "$r62r63"

    let int_gpreg_o_name =
      let open Asmvliw in
      function
      | R0R1R2R3 -> "$r0r1r2r3"
      | R4R5R6R7 -> "$r4r5r6r7"
      | R8R9R10R11 -> "$r8r9r10r11"
      | R12R13R14R15 -> "$r12r13r14r15" 
      | R16R17R18R19 -> "$r16r17r18r19" 
      | R20R21R22R23 -> "$r20r21r22r23"
      | R24R25R26R27 -> "$r24r25r26r27" 
      | R28R29R30R31 -> "$r28r29r30r31"
      | R32R33R34R35 -> "$r32r33r34r35"
      | R36R37R38R39 -> "$r36r37r38r39" 
      | R40R41R42R43 -> "$r40r41r42r43"
      | R44R45R46R47 -> "$r44r45r46r47" 
      | R48R49R50R51 -> "$r48r49r50r51" 
      | R52R53R54R55 -> "$r52r53r54r55" 
      | R56R57R58R59 -> "$r56r57r58r59"
      | R60R61R62R63 -> "$r60r61r62r63";;
        
    let gpreg_q oc r = output_string oc (int_gpreg_q_name r)
    let gpreg_o oc r = output_string oc (int_gpreg_o_name r)

    let preg oc = let open Asmvliw in function
      | IR r -> ireg oc r
      | RA   -> output_string oc "$ra"
      | _ -> assert false

    let preg_asm oc ty = preg oc
              
    let preg_annot = let open Asmvliw in function
      | IR r -> int_reg_name r
      | RA   -> "$ra"
      | _ -> assert false

    let scale_of_shift1_4 = let open ExtValues in function
      | SHIFT1 -> 2
      | SHIFT2 -> 4
      | SHIFT3 -> 8
      | SHIFT4 -> 16;;
    
(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data(true, true) ->
         ".section .tdata,\"awT\",@progbits"
      | Section_data(false, true) ->        
         ".section .tbss,\"awT\",@nobits"
      | Section_data(i, false) | Section_small_data(i) ->
         (if i then ".data" else "COMM")
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

    let print_tbl oc (lbl, tbl) =
      fprintf oc "	.balign 8\n";
      fprintf oc "%a:\n" label lbl;
      List.iter
        (fun l -> fprintf oc "	.8byte	%a\n"
                    print_label l)
        tbl

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

    let loadsymbol oc r id ofs =
      if Archi.pic_code () then begin
        assert (ofs = Integers.Ptrofs.zero);
        if C2C.atom_is_thread_local id then begin
            (* fprintf oc "	addd	%a = $r13, @tprel(%s)\n" ireg r (extern_atom id) *)
            fprintf oc "	addd	%a = $r13, @tlsle(%s)\n" ireg r (extern_atom id)
        end else begin
            fprintf oc "	make	%a = %s\n" ireg r (extern_atom id)
        end
     end else
     begin
        if C2C.atom_is_thread_local id then begin
            (* fprintf oc "	addd	%a = $r13, @tprel(%a)\n" ireg r symbol_offset (id, ofs) *)
            fprintf oc "	addd	%a = $r13, @tlsle(%a)\n" ireg r symbol_offset (id, ofs)
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

    (* Profiling *)
    

    let k1c_profiling_stub oc nr_items
          profiling_id_table_name
          profiling_counter_table_name =
          fprintf oc "	make $r0 = %d\n" nr_items;
          fprintf oc "	make $r1 = %s\n" profiling_id_table_name;
          fprintf oc "	make $r2 = %s\n" profiling_counter_table_name;
          fprintf oc "	goto	%s\n" profiling_write_table_helper;
          fprintf oc "	;;\n";;

    (* Offset part of a load or store *)

    let offset oc n = ptrofs oc n 

    let addressing oc = function
    | AOff ofs -> offset oc ofs
    | AReg ro | ARegXS ro -> ireg oc ro

    let xscale oc = function
    | ARegXS _ -> fprintf oc ".xs"
    | _ -> ()

    let lsvariant oc = function
      | TRAP -> ()
      | NOTRAP -> output_string oc ".s"
      
    let icond_name = let open Asmvliw in function
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

    let icond oc c = fprintf oc "%s" (icond_name c)

    let fcond_name = let open Asmvliw in function
      | FTone -> "one"
      | FTueq -> "ueq"
      | FToeq -> "oeq"
      | FTune -> "une"
      | FTolt -> "olt"
      | FTuge -> "uge"
      | FToge -> "oge"
      | FTult -> "ult"

    let fcond oc c = fprintf oc "%s" (fcond_name c)
  
    let bcond_name = let open Asmvliw in function
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
              print_inline_asm preg_asm oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | EF_profiling(id, coq_kind) ->
             let kind = Z.to_int coq_kind in
             assert (kind >= 0);
             assert (kind <= 1);
             fprintf oc "%s profiling %a %d\n" comment
               Profilingaux.pp_id id kind;
             fprintf oc "	make	$r63 = %s\n" profiling_counter_table_name;
             fprintf oc "	make	$r62 = 1\n";
             fprintf oc "	;;\n";
             fprintf oc "	afaddd	%d[$r63] = $r62\n"
               (profiling_offset id kind);
             fprintf oc "	;;\n"
          | _ ->
              assert false
         end
      | Pnop -> (* FIXME fprintf oc "	nop\n" *) ()
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

      (* For builtins *)
      | Ploopdo (r, lbl) ->
         fprintf oc "	loopdo	%a, %a\n" ireg r print_label lbl
      | Pgetn(n, dst) ->
         fprintf oc "	get	%a = $s%ld\n" ireg dst (camlint_of_coqint n)
      | Psetn(n, dst) ->
         fprintf oc "	set	$s%ld = %a\n" (camlint_of_coqint n) ireg dst
      | Pwfxl(n, dst) ->
         fprintf oc "	wfxl	$s%ld = %a\n" (camlint_of_coqint n) ireg dst
      | Pwfxm(n, dst) ->
         fprintf oc "	wfxm	$s%ld = %a\n" (camlint_of_coqint n) ireg dst
      | Pldu(dst, addr) ->
         fprintf oc "	ld.u	%a = 0[%a]\n" ireg dst ireg addr
      | Plbzu(dst, addr) ->
         fprintf oc "	lbz.u	%a = 0[%a]\n" ireg dst ireg addr
      | Plhzu(dst, addr) ->
         fprintf oc "	lhz.u	%a = 0[%a]\n" ireg dst ireg addr
      | Plwzu(dst, addr) ->
         fprintf oc "	lwz.u	%a = 0[%a]\n" ireg dst ireg addr
      | Pawait ->
         fprintf oc "	await\n"
      | Psleep ->
         fprintf oc "	sleep\n"
      | Pstop ->
         fprintf oc "	stop\n"
      | Pbarrier ->
         fprintf oc "	barrier\n"
      | Pfence ->
         fprintf oc "	fence\n"
      | Pdinval ->
         fprintf oc "	dinval\n"
      | Pdinvall addr ->
         fprintf oc "	dinvall	0[%a]\n" ireg addr
      | Pdtouchl addr ->
         fprintf oc "	dtouchl	0[%a]\n" ireg addr
      | Piinval ->
         fprintf oc "	iinval\n"
      | Piinvals addr ->
         fprintf oc "	iinvals	0[%a]\n" ireg addr
      | Pitouchl addr ->
         fprintf oc "	itouchl	0[%a]\n" ireg addr
      | Pdzerol addr ->
         fprintf oc "	dzerol	0[%a]\n" ireg addr
(*    | Pafaddd(addr, incr_res) ->
         fprintfoc "	afaddd	0[%a] = %a\n" ireg addr ireg incr_res
      | Pafaddw(addr, incr_res) ->
         fprintfoc "	afaddw	0[%a] = %a\n" ireg addr ireg incr_res *) (* see #157 *)
      | Palclrd(res, addr) ->
         fprintf oc "	alclrd	%a = 0[%a]\n" ireg res ireg addr
      | Palclrw(res, addr) ->
         fprintf oc "	alclrw	%a = 0[%a]\n" ireg res ireg addr
      | Pjumptable (idx_reg, tbl) ->
         let lbl = new_label() in
         (* jumptables := (lbl, tbl) :: !jumptables; *)
         let base_reg = if idx_reg=Asmvliw.GPR63 then Asmvliw.GPR62 else Asmvliw.GPR63 in
         fprintf oc "%s jumptable [ " comment;
         List.iter (fun l -> fprintf oc "%a " print_label l) tbl;
         fprintf oc "]\n";
         fprintf oc "    make	%a = %a\n    ;;\n" ireg base_reg label lbl; 
         fprintf oc "    ld.xs	%a = %a[%a]\n    ;;\n" ireg base_reg ireg idx_reg ireg base_reg;
         fprintf oc "    igoto	%a\n    ;;\n" ireg base_reg;
         section oc Section_jumptable;
         print_tbl oc (lbl, tbl);
         section oc Section_text

      (* Load/Store instructions *)
      | Plb(trap, rd, ra, adr) ->
         fprintf oc "	lbs%a%a	%a = %a[%a]\n" lsvariant trap xscale adr ireg rd addressing adr ireg ra
      | Plbu(trap, rd, ra, adr) ->
         fprintf oc "	lbz%a%a	%a = %a[%a]\n" lsvariant trap xscale adr ireg rd addressing adr ireg ra
      | Plh(trap, rd, ra, adr) ->
         fprintf oc "	lhs%a%a	%a = %a[%a]\n" lsvariant trap xscale adr ireg rd addressing adr ireg ra
      | Plhu(trap, rd, ra, adr) ->
         fprintf oc "	lhz%a%a	%a = %a[%a]\n" lsvariant trap xscale adr ireg rd addressing adr ireg ra
      | Plw(trap, rd, ra, adr) | Plw_a(trap, rd, ra, adr) | Pfls(trap, rd, ra, adr) ->
         fprintf oc "	lws%a%a	%a = %a[%a]\n" lsvariant trap xscale adr ireg rd addressing adr ireg ra
      | Pld(trap, rd, ra, adr) | Pfld(trap, rd, ra, adr) | Pld_a(trap, rd, ra, adr) -> assert Archi.ptr64;
         fprintf oc "	ld%a%a	%a = %a[%a]\n" lsvariant trap xscale adr ireg rd addressing adr ireg ra
      | Plq(rd, ra, adr) ->
         fprintf oc "	lq%a	%a = %a[%a]\n" xscale adr gpreg_q rd addressing adr ireg ra
      | Plo(rd, ra, adr) ->
         fprintf oc "	lo%a	%a = %a[%a]\n" xscale adr gpreg_o rd addressing adr ireg ra
    
      | Psb(rd, ra, adr) ->
         fprintf oc "	sb%a	%a[%a] = %a\n" xscale adr addressing adr ireg ra ireg rd
      | Psh(rd, ra, adr) ->
         fprintf oc "	sh%a	%a[%a] = %a\n" xscale adr addressing adr ireg ra ireg rd
      | Psw(rd, ra, adr) | Psw_a(rd, ra, adr) | Pfss(rd, ra, adr) ->
         fprintf oc "	sw%a	%a[%a] = %a\n" xscale adr addressing adr ireg ra ireg rd
      | Psd(rd, ra, adr) | Psd_a(rd, ra, adr) | Pfsd(rd, ra, adr) -> assert Archi.ptr64;
         fprintf oc "	sd%a	%a[%a] = %a\n" xscale adr addressing adr ireg ra ireg rd
      | Psq(rd, ra, adr) ->
         fprintf oc "	sq%a	%a[%a] = %a\n" xscale adr addressing adr ireg ra gpreg_q rd
      | Pso(rd, ra, adr) ->
         fprintf oc "	so%a	%a[%a] = %a\n" xscale adr addressing adr ireg ra gpreg_o rd
      
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
      | Pextfz(rd, rs, stop, start) | Pextfzl(rd, rs, stop, start) ->
         fprintf oc "	extfz	%a = %a, %ld, %ld\n" ireg rd ireg rs (camlint_of_coqint stop) (camlint_of_coqint start)
      | Pextfs(rd, rs, stop, start) | Pextfsl(rd, rs, stop, start) ->
         fprintf oc "	extfs	%a = %a, %ld, %ld\n" ireg rd ireg rs (camlint_of_coqint stop) (camlint_of_coqint start)
      | Pinsf(rd, rs, stop, start) | Pinsfl(rd, rs, stop, start) ->
         fprintf oc "	insf	%a = %a, %ld, %ld\n" ireg rd ireg rs (camlint_of_coqint stop) (camlint_of_coqint start)
      | Pfabsd(rd, rs) ->
         fprintf oc "	fabsd	%a = %a\n" ireg rd ireg rs
      | Pfabsw(rd, rs) ->
         fprintf oc "	fabsw	%a = %a\n" ireg rd ireg rs
      | Pfnegd(rd, rs) ->
         fprintf oc "	fnegd	%a = %a\n" ireg rd ireg rs
      | Pfnegw(rd, rs) ->
         fprintf oc "	fnegw	%a = %a\n" ireg rd ireg rs
      | Pfnarrowdw(rd, rs) ->
         fprintf oc "	fnarrowdw	%a = %a\n" ireg rd ireg rs
      | Pfwidenlwd(rd, rs) ->
         fprintf oc "	fwidenlwd	%a = %a\n" ireg rd ireg rs
      | Pfloatuwrnsz(rd, rs) ->
         fprintf oc "	floatuw.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfloatwrnsz(rd, rs) ->
         fprintf oc "	floatw.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfloatudrnsz(rd, rs) ->
         fprintf oc "	floatud.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfloatdrnsz(rd, rs) ->
          fprintf oc "	floatd.rn.s	%a = %a, 0\n" ireg rd ireg rs
      | Pfixedwrzz(rd, rs) ->
         fprintf oc "	fixedw.rz	%a = %a, 0\n" ireg rd ireg rs
      | Pfixeduwrzz(rd, rs) ->
         fprintf oc "	fixeduw.rz	%a = %a, 0\n" ireg rd ireg rs
      | Pfixeddrzz(rd, rs) | Pfixeddrzz_i32(rd, rs) ->
         fprintf oc "	fixedd.rz	%a = %a, 0\n" ireg rd ireg rs
      | Pfixedudrzz(rd, rs) | Pfixedudrzz_i32(rd, rs) ->
         fprintf oc "	fixedud.rz	%a = %a, 0\n" ireg rd ireg rs

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

      | Pfcompw (ft, rd, rs1, rs2) ->
         fprintf oc "	fcompw.%a	%a = %a, %a\n" fcond ft ireg rd ireg rs1 ireg rs2
      | Pfcompl (ft, rd, rs1, rs2) ->
         fprintf oc "	fcompd.%a	%a = %a, %a\n" fcond ft ireg rd ireg rs1 ireg rs2

      | Paddw (rd, rs1, rs2) ->
         fprintf oc "	addw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Paddxw (s14, rd, rs1, rs2) ->
         fprintf oc "	addx%dw	%a = %a, %a\n" (scale_of_shift1_4 s14)
           ireg rd ireg rs1 ireg rs2
      | Psubw (rd, rs1, rs2) ->
         fprintf oc "	sbfw	%a = %a, %a\n" ireg rd ireg rs2 ireg rs1
      | Prevsubxw (s14, rd, rs1, rs2) ->
         fprintf oc "	sbfx%dw	%a = %a, %a\n" (scale_of_shift1_4 s14)
           ireg rd ireg rs1 ireg rs2
      | Pmulw (rd, rs1, rs2) ->
         fprintf oc "	mulw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pandw (rd, rs1, rs2) ->
         fprintf oc "	andw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pnandw (rd, rs1, rs2) ->
         fprintf oc "	nandw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Porw (rd, rs1, rs2) -> 
         fprintf oc "	orw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pnorw (rd, rs1, rs2) -> 
         fprintf oc "	norw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pxorw (rd, rs1, rs2) -> 
         fprintf oc "	xorw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pnxorw (rd, rs1, rs2) -> 
         fprintf oc "	nxorw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pandnw (rd, rs1, rs2) -> 
         fprintf oc "	andnw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pornw (rd, rs1, rs2) -> 
         fprintf oc "	ornw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psraw (rd, rs1, rs2) ->
         fprintf oc "	sraw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrxw (rd, rs1, rs2) ->
         fprintf oc "	srsw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrlw (rd, rs1, rs2) ->
         fprintf oc "	srlw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psllw (rd, rs1, rs2) ->
         fprintf oc "	sllw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmaddw (rd, rs1, rs2) ->
         fprintf oc "	maddw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmsubw (rd, rs1, rs2) ->
         fprintf oc "	msbfw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmaddfw (rd, rs1, rs2) ->
         fprintf oc "	ffmaw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmsubfw (rd, rs1, rs2) ->
         fprintf oc "	ffmsw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Paddl (rd, rs1, rs2) ->
         fprintf oc "	addd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Paddxl (s14, rd, rs1, rs2) ->
         fprintf oc "	addx%dd	%a = %a, %a\n" (scale_of_shift1_4 s14)
           ireg rd ireg rs1 ireg rs2
      | Psubl (rd, rs1, rs2) ->
         fprintf oc "	sbfd	%a = %a, %a\n" ireg rd ireg rs2 ireg rs1
      | Prevsubxl (s14, rd, rs1, rs2) ->
         fprintf oc "	sbfx%dd	%a = %a, %a\n" (scale_of_shift1_4 s14)
           ireg rd ireg rs1 ireg rs2
      | Pandl (rd, rs1, rs2) ->
         fprintf oc "	andd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pnandl (rd, rs1, rs2) ->
         fprintf oc "	nandd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Porl (rd, rs1, rs2) ->
         fprintf oc "	ord	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pnorl (rd, rs1, rs2) ->
         fprintf oc "	nord	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pxorl (rd, rs1, rs2) ->
         fprintf oc "	xord	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pnxorl (rd, rs1, rs2) -> 
         fprintf oc "	nxord	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pandnl (rd, rs1, rs2) -> 
         fprintf oc "	andnd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pornl (rd, rs1, rs2) -> 
         fprintf oc "	ornd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmull (rd, rs1, rs2) ->
         fprintf oc "	muld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pslll  (rd, rs1, rs2) ->
         fprintf oc "	slld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrll  (rd, rs1, rs2) ->
         fprintf oc "	srld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psrxl  (rd, rs1, rs2) ->
         fprintf oc "	srsd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Psral   (rd, rs1, rs2) ->
         fprintf oc "	srad	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmaddl (rd, rs1, rs2) ->
         fprintf oc "	maddd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pmsubl (rd, rs1, rs2) ->
         fprintf oc "	msbfd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmaddfl (rd, rs1, rs2) ->
         fprintf oc "	ffmad	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmsubfl (rd, rs1, rs2) ->
         fprintf oc "	ffmsd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2

      | Pfaddd (rd, rs1, rs2) ->
         fprintf oc "	faddd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfaddw (rd, rs1, rs2) ->
         fprintf oc "	faddw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfsbfd (rd, rs1, rs2) ->
         fprintf oc "	fsbfd	%a = %a, %a\n" ireg rd ireg rs2 ireg rs1
      | Pfsbfw (rd, rs1, rs2) ->
         fprintf oc "	fsbfw	%a = %a, %a\n" ireg rd ireg rs2 ireg rs1
      | Pfmuld (rd, rs1, rs2) ->
         fprintf oc "	fmuld	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmulw (rd, rs1, rs2) ->
         fprintf oc "	fmulw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmind (rd, rs1, rs2) ->
         fprintf oc "	fmind	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfminw (rd, rs1, rs2) ->
         fprintf oc "	fminw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmaxd (rd, rs1, rs2) ->
         fprintf oc "	fmaxd	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfmaxw (rd, rs1, rs2) ->
         fprintf oc "	fmaxw	%a = %a, %a\n" ireg rd ireg rs1 ireg rs2
      | Pfinvw (rd, rs1) ->
         fprintf oc "	finvw	%a = %a\n" ireg rd ireg rs1

      (* Arith RRI32 instructions *)
      | Pcompiw (it, rd, rs, imm) ->
         fprintf oc "	compw.%a	%a = %a, %a\n" icond it ireg rd ireg rs coqint imm
      | Paddiw (rd, rs, imm) ->
         fprintf oc "	addw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Paddxiw (s14, rd, rs, imm) ->
         fprintf oc "	addx%dw	%a = %a, %a\n"  (scale_of_shift1_4 s14)
           ireg rd ireg rs coqint imm
      | Prevsubiw (rd, rs, imm) ->
         fprintf oc "	sbfw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Prevsubxiw (s14, rd, rs, imm) ->
         fprintf oc "	sbfx%dw	%a = %a, %a\n"  (scale_of_shift1_4 s14)
           ireg rd ireg rs coqint imm
      | Pmuliw (rd, rs, imm) ->
         fprintf oc "	mulw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pandiw (rd, rs, imm) ->
         fprintf oc "	andw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pnandiw (rd, rs, imm) ->
         fprintf oc "	nandw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Poriw (rd, rs, imm) -> 
         fprintf oc "	orw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pnoriw (rd, rs, imm) -> 
         fprintf oc "	norw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pxoriw (rd, rs, imm) -> 
         fprintf oc "	xorw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pnxoriw (rd, rs, imm) -> 
         fprintf oc "	nxorw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pandniw (rd, rs, imm) -> 
         fprintf oc "	andnw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Porniw (rd, rs, imm) -> 
         fprintf oc "	ornw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Psraiw (rd, rs, imm) ->
         fprintf oc "	sraw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Psrxiw (rd, rs, imm) ->
         fprintf oc "	srsw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Psrliw (rd, rs, imm) ->
         fprintf oc "	srlw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pslliw (rd, rs, imm) ->
         fprintf oc "	sllw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Proriw (rd, rs, imm) ->
         fprintf oc "	rorw	%a = %a, %a\n" ireg rd ireg rs coqint imm
      | Pmaddiw (rd, rs, imm) ->
         fprintf oc "	maddw	%a = %a, %a\n" ireg rd ireg rs coqint imm

      | Psllil (rd, rs, imm) ->
         fprintf oc "	slld	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrlil (rd, rs, imm) ->
         fprintf oc "	srld	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrail (rd, rs, imm) ->
         fprintf oc "	srad	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Psrxil (rd, rs, imm) ->
         fprintf oc "	srsd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm

    (* Arith RRI64 instructions *)
      | Pcompil (it, rd, rs, imm) ->
         fprintf oc "	compd.%a	%a = %a, %a\n" icond it ireg rd ireg rs coqint64 imm
      | Paddil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	addd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Paddxil (s14, rd, rs, imm) ->
         fprintf oc "	addx%dd	%a = %a, %a\n"  (scale_of_shift1_4 s14)
           ireg rd ireg rs coqint imm
      | Prevsubil (rd, rs, imm) ->
         fprintf oc "	sbfd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Prevsubxil (s14, rd, rs, imm) ->
         fprintf oc "	sbfx%dd	%a = %a, %a\n"  (scale_of_shift1_4 s14)
           ireg rd ireg rs coqint64 imm
      | Pmulil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	muld	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pandil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	andd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pnandil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	nandd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Poril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	ord	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pnoril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	nord	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pxoril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	xord	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pnxoril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	nxord	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pandnil (rd, rs, imm) -> 
         fprintf oc "	andnd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pornil (rd, rs, imm) -> 
         fprintf oc "	ornd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm
      | Pmaddil (rd, rs, imm) ->
         fprintf oc "	maddd	%a = %a, %a\n" ireg rd ireg rs coqint64 imm

      | Pcmove (bt, rd, rcond, rs) | Pcmoveu (bt, rd, rcond, rs) ->
         fprintf oc "	cmoved.%a %a? %a = %a\n"
           bcond bt ireg rcond ireg rd ireg rs
      | Pcmoveiw (bt, rd, rcond, imm) | Pcmoveuiw (bt, rd, rcond, imm) ->
         fprintf oc "	cmoved.%a %a? %a = %a\n"
           bcond bt ireg rcond ireg rd coqint imm
      | Pcmoveil (bt, rd, rcond, imm) | Pcmoveuil (bt, rd, rcond, imm) ->
         fprintf oc "	cmoved.%a %a? %a = %a\n"
           bcond bt ireg rcond ireg rd coqint64 imm
        
    let get_section_names name =
      let (text, lit) =
        match C2C.atom_sections name with
        | t :: l :: _ -> (t, l)
        | _    -> (Section_text, Section_literal) in
      text,lit,Section_jumptable

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment
      
    let print_jumptable oc jmptbl = () 
      (* if !jumptables <> [] then
        begin
          section oc jmptbl;
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end *)

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
      print_profiling_epilogue elf_text_print_fun_info Dtors k1c_profiling_stub oc;
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
