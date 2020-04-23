(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the RISC-V assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq

exception Error of string
                  
(* Useful constants and helper functions *)

let _0  = Integers.Int.zero
let _1  = Integers.Int.one
let _2  = coqint_of_camlint 2l
let _4  = coqint_of_camlint 4l
let _8  = coqint_of_camlint 8l
let _16  = coqint_of_camlint 16l
let _m1 = coqint_of_camlint (-1l)

let wordsize = if Archi.ptr64 then 8 else 4

let align n a = (n + a - 1) land (-a)

let stack_pointer = Asmvliw.GPR12
                  
(* Emit instruction sequences that set or offset a register by a constant. *)
(*
  let expand_loadimm32 dst n =
  List.iter emit (Asmgen.loadimm32 dst n [])
*)
let expand_addptrofs dst src n =
  List.iter emit (basic_to_instruction (Asmvliw.PArith (Asmblockgen.addptrofs dst src n)) :: [])
let expand_storeind_ptr src base ofs =
  List.iter emit (basic_to_instruction (Asmblockgen.storeind_ptr src base ofs) :: [])
let expand_loadind_ptr dst base ofs =
  List.iter emit (basic_to_instruction (Asmblockgen.loadind_ptr base ofs dst) :: [])

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Fix-up code around calls to variadic functions.  Floating-point arguments
   residing in FP registers need to be moved to integer registers. *)

let int_param_regs   = let open Asmvliw in [| GPR0; GPR1; GPR2; GPR3; GPR4; GPR5; GPR6; GPR7; GPR8; GPR9; GPR10; GPR11 |]
(* let float_param_regs = [| F10; F11; F12; F13; F14; F15; F16; F17 |] *)
let float_param_regs = [| |]

let fixup_variadic_call pos tyl = assert false
(*if pos < 8 then
    match tyl with
    | [] ->
        ()
    | (Tint | Tany32) :: tyl ->
        fixup_variadic_call (pos + 1) tyl
    | Tsingle :: tyl ->
        let rs =float_param_regs.(pos)
        and rd = int_param_regs.(pos) in
        emit (Pfmvxs(rd, rs));
        fixup_variadic_call (pos + 1) tyl
    | Tlong :: tyl ->
        let pos' = if Archi.ptr64 then pos + 1 else align pos 2 + 2 in
        fixup_variadic_call pos' tyl
    | (Tfloat | Tany64) :: tyl ->
        if Archi.ptr64 then begin
          let rs = float_param_regs.(pos)
          and rd = int_param_regs.(pos) in
          emit (Pfmvxd(rd, rs));
          fixup_variadic_call (pos + 1) tyl
        end else begin
          let pos = align pos 2 in
          if pos < 8 then begin
            let rs = float_param_regs.(pos)
            and rd1 = int_param_regs.(pos)
            and rd2 = int_param_regs.(pos + 1) in
            emit (Paddiw(X2, X X2, Integers.Int.neg _16));
            emit (Pfsd(rs, X2, Ofsimm _0));
            emit (Plw(rd1, X2, Ofsimm _0));
            emit (Plw(rd2, X2, Ofsimm _4));
            emit (Paddiw(X2, X X2, _16));
            fixup_variadic_call (pos + 2) tyl
          end
        end
*)
        
let fixup_call sg =
  if sg.sig_cc.cc_vararg then fixup_variadic_call 0 sg.sig_args

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(Asmvliw.IR src)], BR(Asmvliw.IR dst) ->
     if dst <> src then emit (Pmv (dst, src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Handling of memcpy *)

let emit_move dst r =
  if dst <> r
  then emit (Paddil(dst, r, Z.zero));;

(* FIXME DMonniaux this is probably not complete *)
let get_builtin_arg dst arg =
  match arg with
  | BA (Asmvliw.IR reg) -> emit_move dst reg
  | BA (ireg) ->  failwith "get_builtin_arg: BA_int(not ireg)"
  | BA_int _ -> failwith "get_builtin_arg: BA_int"
  | BA_long _ -> failwith "get_builtin_arg: BA_long"
  | BA_float _ -> failwith "get_builtin_arg: BA_float"
  | BA_single _ -> failwith "get_builtin_arg: BA_single"
  | BA_loadstack _ -> failwith "get_builtin_arg: BA_loadstack"
  | BA_addrstack ofs -> emit (Paddil(dst, stack_pointer, ofs))
  | BA_loadglobal _ -> failwith "get_builtin_arg: BA_loadglobal"
  | BA_addrglobal _ -> failwith "get_builtin_arg: BA_addrglobal"
  | BA_splitlong _ -> failwith "get_builtin_arg: BA_splitlong"
  | BA_addptr _ -> failwith "get_builtin_arg: BA_addptr";;

let smart_memcpy = true
                 
(* FIXME DMonniaux this is really suboptimal (byte per byte) *)
let expand_builtin_memcpy_big sz al src dst =
  assert (sz > Z.zero);
  let dstptr = Asmvliw.GPR62
  and srcptr = Asmvliw.GPR63
  and tmpbuf = Asmvliw.GPR61
  and tmpbuf2 = Asmvliw.R60R61
  and caml_sz = camlint64_of_coqint sz in
  get_builtin_arg dstptr dst;
  get_builtin_arg srcptr src;
  let caml_sz_div16 = Int64.shift_right caml_sz 4
  and sixteen = coqint_of_camlint64 16L in
  if smart_memcpy
  then
    let remaining = ref caml_sz
    and offset = ref 0L in
    let cpy buf size load store =
      (if !remaining >= size
      then
        let zofs = coqint_of_camlint64 !offset in
        begin
          emit Psemi;
          emit (load buf srcptr (AOff zofs));
          emit Psemi;
          emit (store buf dstptr (AOff zofs));
          remaining := Int64.sub !remaining size;
          offset := Int64.add !offset size
        end) in
    begin
      (if caml_sz_div16 >= 2L
      then
        begin
          emit (Pmake (tmpbuf, (coqint_of_camlint64 caml_sz_div16)));
          emit Psemi; 
          let lbl = new_label() in
          emit (Ploopdo (tmpbuf, lbl));
          emit Psemi;
          emit (Plq (tmpbuf2, srcptr, AOff Z.zero));
          emit (Paddil (srcptr, srcptr, sixteen));
          emit Psemi;
          emit (Psq (tmpbuf2, dstptr, AOff Z.zero));
          emit (Paddil (dstptr, dstptr, sixteen));
          emit Psemi;
          emit (Plabel lbl);
          remaining := Int64.sub !remaining (Int64.shift_left caml_sz_div16 4)
        end);
    
      cpy tmpbuf2 16L (fun x y z -> Plq(x, y, z)) (fun x y z -> Psq(x, y, z));
      cpy tmpbuf 8L (fun x y z -> Pld(TRAP, x, y, z)) (fun x y z -> Psd(x, y, z));
      cpy tmpbuf 4L (fun x y z -> Plw(TRAP, x, y, z)) (fun x y z -> Psw(x, y, z));
      cpy tmpbuf 2L (fun x y z -> Plh(TRAP, x, y, z)) (fun x y z -> Psh(x, y, z));
      cpy tmpbuf 1L (fun x y z -> Plb(TRAP, x, y, z)) (fun x y z -> Psb(x, y, z));
      assert (!remaining = 0L)
    end
  else
    begin
      emit (Pmake (tmpbuf, sz));
      emit Psemi; 
      let lbl = new_label() in
      emit (Ploopdo (tmpbuf, lbl));
      emit Psemi;
      emit (Plb (TRAP, tmpbuf, srcptr, AOff Z.zero));
      emit (Paddil (srcptr, srcptr, Z.one));
      emit Psemi;
      emit (Psb (tmpbuf, dstptr, AOff Z.zero));
      emit (Paddil (dstptr, dstptr, Z.one));
      emit Psemi;
      emit (Plabel lbl);
    end;;
  
let expand_builtin_memcpy  sz al args =
  match args with
  | [dst; src] ->
    expand_builtin_memcpy_big sz al src dst
  | _ -> assert false;;

(* Handling of volatile reads and writes *)
(* FIXME probably need to check for size of displacement *)
let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8unsigned, BR(Asmvliw.IR res) ->
     emit (Plbu (TRAP, res, base, AOff ofs))
  | Mint8signed, BR(Asmvliw.IR res) ->
     emit (Plb  (TRAP, res, base, AOff ofs))
  | Mint16unsigned, BR(Asmvliw.IR res) ->
     emit (Plhu (TRAP, res, base, AOff ofs))
  | Mint16signed, BR(Asmvliw.IR res) ->
     emit (Plh  (TRAP, res, base, AOff ofs))
  | Mint32, BR(Asmvliw.IR res) ->
     emit (Plw  (TRAP, res, base, AOff ofs))
  | Mint64, BR(Asmvliw.IR res) ->
     emit (Pld  (TRAP, res, base, AOff ofs))
  | Mint64, BR_splitlong(BR(Asmvliw.IR res1), BR(Asmvliw.IR res2)) ->
     let ofs' = Integers.Ptrofs.add ofs _4 in
     if base <> res2 then begin
         emit (Plw (TRAP, res2, base, AOff ofs));
         emit (Plw (TRAP, res1, base, AOff ofs'))
       end else begin
         emit (Plw (TRAP, res1, base, AOff ofs'));
         emit (Plw (TRAP, res2, base, AOff ofs))
       end
  | Mfloat32, BR(Asmvliw.IR res) ->
     emit (Pfls (TRAP, res, base, AOff ofs))
  | Mfloat64, BR(Asmvliw.IR res) ->
     emit (Pfld (TRAP, res, base, AOff ofs))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(Asmvliw.IR addr)] ->
      expand_builtin_vload_common chunk addr _0 res
  | [BA_addrstack ofs] ->
     expand_builtin_vload_common chunk stack_pointer ofs res
  | [BA_addptr(BA(Asmvliw.IR addr), (BA_int ofs | BA_long ofs))] ->
     expand_builtin_vload_common chunk addr ofs res
  | _ ->
      assert false


let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(Asmvliw.IR src) ->
     emit (Psb (src, base, AOff ofs))
  | (Mint16signed | Mint16unsigned), BA(Asmvliw.IR src) ->
     emit (Psh (src, base, AOff ofs))
  | Mint32, BA(Asmvliw.IR src) ->
     emit (Psw (src, base, AOff ofs))
  | Mint64, BA(Asmvliw.IR src) ->
     emit (Psd (src, base, AOff ofs))
  | Mint64, BA_splitlong(BA(Asmvliw.IR src1), BA(Asmvliw.IR src2)) ->
     let ofs' = Integers.Ptrofs.add ofs _4 in
     emit (Psw (src2, base, AOff ofs));
     emit (Psw (src1, base, AOff ofs'))
  | Mfloat32, BA(Asmvliw.IR src) ->
     emit (Pfss (src, base, AOff ofs))
  | Mfloat64, BA(Asmvliw.IR src) ->
     emit (Pfsd (src, base, AOff ofs))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(Asmvliw.IR addr); src] ->
      expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
     expand_builtin_vstore_common chunk stack_pointer ofs src
  | [BA_addptr(BA(Asmvliw.IR addr), (BA_int ofs | BA_long ofs)); src] ->
     expand_builtin_vstore_common chunk addr ofs src
  | _ ->
      assert false

(* Handling of varargs *)

(* Size in words of the arguments to a function.  This includes both
   arguments passed in registers and arguments passed on stack. *)

let rec args_size sz = function
  | [] -> sz
  | (Tint | Tsingle | Tany32) :: l ->
      args_size (sz + 1) l
  | (Tlong | Tfloat | Tany64) :: l ->
      args_size (if Archi.ptr64 then sz + 1 else align sz 2 + 2) l

let arguments_size sg =
  args_size 0 sg.sig_args

let _nbregargs_ = 12
let _alignment_ = 8

let save_arguments first_reg base_ofs = let open Asmvliw in
  for i = first_reg to (_nbregargs_ - 1) do begin
    expand_storeind_ptr
      int_param_regs.(i)
      GPR12
      (Integers.Ptrofs.repr (Z.add base_ofs (Z.of_uint ((i - first_reg) * wordsize))));
    emit Psemi
  end done

let vararg_start_ofs : Z.t option ref = ref None

let expand_builtin_va_start r = (* assert false *)
match !vararg_start_ofs with
  | None ->
      invalid_arg "Fatal error: va_start used in non-vararg function"
  | Some ofs ->
      expand_addptrofs Asmvliw.GPR32 stack_pointer (Integers.Ptrofs.repr ofs);
      emit Psemi;
      expand_storeind_ptr Asmvliw.GPR32 r Integers.Ptrofs.zero

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through X31 to hold the low 32 bits of the result.
*)

let expand_int64_arith conflict rl fn = assert false
(*if conflict then (fn X31; emit (Pmv(rl, X31))) else fn rl *)

(* Byte swaps.  There are no specific instructions, so we use standard,
   not-very-efficient formulas. *)

let expand_bswap16 d s = let open Asmvliw in
  (* d = (s & 0xFF) << 8 | (s >> 8) & 0xFF *)
  emit (Pandiw(GPR32, s, coqint_of_camlint 0xFFl)); emit Psemi;
  emit (Pslliw(GPR32, GPR32, _8)); emit Psemi;
  emit (Psrliw(d, s, _8)); emit Psemi;
  emit (Pandiw(d, d, coqint_of_camlint 0xFFl));
  emit (Porw(d, GPR32, d)); emit Psemi

let expand_bswap32 d s = let open Asmvliw in
  (* d = (s << 24)
       | (((s >> 8) & 0xFF) << 16)
       | (((s >> 16) & 0xFF) << 8)
       | (s >> 24)  *)
  emit (Pslliw(GPR16, s, coqint_of_camlint 24l)); emit Psemi;
  emit (Psrliw(GPR32, s, _8)); emit Psemi;
  emit (Pandiw(GPR32, GPR32, coqint_of_camlint 0xFFl)); emit Psemi;
  emit (Pslliw(GPR32, GPR32, _16)); emit Psemi;
  emit (Porw(GPR16, GPR16, GPR31)); emit Psemi;
  emit (Psrliw(GPR32, s, _16)); emit Psemi;
  emit (Pandiw(GPR32, GPR32, coqint_of_camlint 0xFFl)); emit Psemi;
  emit (Pslliw(GPR32, GPR32, _8)); emit Psemi;
  emit (Porw(GPR16, GPR16, GPR32)); emit Psemi;
  emit (Psrliw(GPR32, s, coqint_of_camlint 24l)); emit Psemi;
  emit (Porw(d, GPR16, GPR32)); emit Psemi

let expand_bswap64 d s = let open Asmvliw in
  (* d = s << 56
         | (((s >> 8) & 0xFF) << 48)
         | (((s >> 16) & 0xFF) << 40)
         | (((s >> 24) & 0xFF) << 32)
         | (((s >> 32) & 0xFF) << 24)
         | (((s >> 40) & 0xFF) << 16)
         | (((s >> 48) & 0xFF) << 8)
         | s >> 56 *)
  emit (Psllil(GPR16, s, coqint_of_camlint 56l)); emit Psemi;
  List.iter
    (fun (n1, n2) ->
      emit (Psrlil(GPR32, s, coqint_of_camlint n1)); emit Psemi;
      emit (Pandil(GPR32, GPR32, coqint_of_camlint 0xFFl)); emit Psemi;
      emit (Psllil(GPR32, GPR32, coqint_of_camlint n2)); emit Psemi;
      emit (Porl(GPR16, GPR16, GPR32)); emit Psemi;)
    [(8l,48l); (16l,40l); (24l,32l); (32l,24l); (40l,16l); (48l,8l)];
  emit (Psrlil(GPR32, s, coqint_of_camlint 56l)); emit Psemi;
  emit (Porl(d, GPR16, GPR32)); emit Psemi

(* Handling of compiler-inlined builtins *)
let last_system_register = 511l
let not_system_register cn  =cn<0l || cn>last_system_register
  
let expand_builtin_inline name args res = let open Asmvliw in
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  | "__builtin_clzll", [BA(IR a)], BR(IR res) ->
     emit (Pclzll(res, a))
  | "__builtin_k1_stsud", [BA(IR a1); BA(IR a2)], BR(IR res) ->
     emit (Pstsud(res, a1, a2))
  | "__builtin_k1_get", [BA_int(n)], BR(IR res) ->
     let cn = camlint_of_coqint n in
     (if not_system_register cn
      then failwith (Printf.sprintf "__builtin_k1_get(n): n must be between 0 and %ld, was %ld" last_system_register cn)
      else emit (Pgetn(n, res)))
  | "__builtin_k1_set", [BA_int(n); BA(IR src)], _ ->
     let cn = camlint_of_coqint n in
     (if not_system_register cn
      then failwith (Printf.sprintf "__builtin_k1_set(n, val): n must be between 0 and %ld, was %ld" last_system_register cn)
      else emit (Psetn(n, src)))
  | "__builtin_k1_wfxl", [BA_int(n); BA(IR src)], _ ->
     let cn = camlint_of_coqint n in
     (if not_system_register cn
      then failwith (Printf.sprintf "__builtin_k1_wfxl(n, val): n must be between 0 and %ld, was %ld" last_system_register cn)
      else emit (Pwfxl(n, src)))
  | "__builtin_k1_wfxm", [BA_int(n); BA(IR src)], _ ->
     let cn = camlint_of_coqint n in
     (if not_system_register cn
      then failwith (Printf.sprintf "__builtin_k1_wfxm(n, val): n must be between 0 and %ld, was %ld" last_system_register cn)
      else emit (Pwfxm(n, src)))
  | "__builtin_k1_ldu", [BA(IR addr)], BR(IR res) ->
     emit (Pldu(res, addr))
  | "__builtin_k1_lbzu", [BA(IR addr)], BR(IR res) ->
     emit (Plbzu(res, addr))
  | "__builtin_k1_lhzu", [BA(IR addr)], BR(IR res) ->
     emit (Plhzu(res, addr))
  | "__builtin_k1_lwzu", [BA(IR addr)], BR(IR res) ->
     emit (Plwzu(res, addr))
  | "__builtin_k1_alclrd", [BA(IR addr)], BR(IR res) ->
     emit (Palclrd(res, addr))
  | "__builtin_k1_alclrw", [BA(IR addr)], BR(IR res) ->
     emit (Palclrw(res, addr))
  | "__builtin_k1_await", [], _ ->
     emit Pawait
  | "__builtin_k1_sleep", [], _ ->
     emit Psleep
  | "__builtin_k1_stop", [], _ ->
     emit Pstop
  | "__builtin_k1_barrier", [], _ ->
     emit Pbarrier
  | "__builtin_k1_fence", [], _ ->
     emit Pfence
  | "__builtin_k1_dinval", [], _ ->
     emit Pdinval
  | "__builtin_k1_dinvall", [BA(IR addr)], _ ->
     emit (Pdinvall addr)
  | "__builtin_k1_dtouchl", [BA(IR addr)], _ ->
     emit (Pdtouchl addr)
  | "__builtin_k1_iinval", [], _ ->
     emit Piinval
  | "__builtin_k1_iinvals", [BA(IR addr)], _ ->
     emit (Piinvals addr)
  | "__builtin_k1_itouchl", [BA(IR addr)], _ ->
     emit (Pitouchl addr)
  | "__builtin_k1_dzerol", [BA(IR addr)], _ ->
     emit (Pdzerol addr)
(*| "__builtin_k1_afaddd", [BA(IR addr); BA (IR incr_res)], BR(IR res) ->
     (if res <> incr_res
      then (emit (Asm.Pmv(res, incr_res)); emit Psemi));
     emit (Pafaddd(addr, res))
  | "__builtin_k1_afaddw", [BA(IR addr); BA (IR incr_res)], BR(IR res) ->
     (if res <> incr_res
      then (emit (Asm.Pmv(res, incr_res)); emit Psemi));
     emit (Pafaddw(addr, res)) *) (* see #157 *)
  | "__builtin_alclrd", [BA(IR addr)], BR(IR res) ->
     emit (Palclrd(res, addr))
  | "__builtin_alclrw", [BA(IR addr)], BR(IR res) ->
     emit (Palclrw(res, addr))
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     expand_bswap16 res a1
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     expand_bswap32 res a1
  | "__builtin_bswap64", [BA(IR src)], BR(IR res) ->
     expand_bswap64 res src
	  
  (* Byte swaps *)
(*| "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     expand_bswap16 res a1
  | "__builtin_fabs",  [BA(FR a1)], BR(FR res) ->
     emit (Pfabsd(res, a1))
*)
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
      let sg = get_current_function_sig() in
      emit (Pmv (Asmvliw.GPR17, stack_pointer));
      if sg.sig_cc.cc_vararg then begin
        let n = arguments_size sg in
        let extra_sz = if n >= _nbregargs_ then 0 else (* align _alignment_ *) ((_nbregargs_ - n) * wordsize) in
        let full_sz = Z.add sz (Z.of_uint extra_sz) in
        expand_addptrofs stack_pointer stack_pointer (Integers.Ptrofs.repr (Z.neg full_sz));
        emit Psemi;
        expand_storeind_ptr Asmvliw.GPR17 stack_pointer ofs;
        emit Psemi;
        let va_ofs =
          let extra_ofs = if n <= _nbregargs_ then 0 else ((n - _nbregargs_) * wordsize) in
          Z.add sz (Z.of_sint extra_ofs) in
        vararg_start_ofs := Some va_ofs;
        save_arguments n va_ofs
      end else begin
        let below = Integers.Ptrofs.repr (Z.neg sz) in
        expand_addptrofs stack_pointer stack_pointer below;
        emit Psemi; (* Psemi required to fit in resource constraints *)
        expand_storeind_ptr stack_pointer stack_pointer (Integers.Ptrofs.add ofs below);
        vararg_start_ofs := None
      end
  | Pfreeframe (sz, ofs) ->
     let sg = get_current_function_sig() in
     let extra_sz =
      if sg.sig_cc.cc_vararg then begin
        let n = arguments_size sg in
        if n >= _nbregargs_ then 0 else (* align _alignment_ *) ((_nbregargs_ - n) * wordsize)
      end else 0 in
     expand_addptrofs stack_pointer stack_pointer (Integers.Ptrofs.repr (Z.add sz (Z.of_uint extra_sz)))

(*| Pseqw(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltiuw(rd, rs1, Int.one))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltiuw(rd, X rd, Int.one))
      end
  | Psnew(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltuw(rd, X0, rs1))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltuw(rd, X0, X rd))
      end
  | Pseql(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltiul(rd, rs1, Int64.one))
      end else begin
        emit (Pxorl(rd, rs1, rs2)); emit (Psltiul(rd, X rd, Int64.one))
      end
  | Psnel(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltul(rd, X0, rs1))
      end else begin
        emit (Pxorl(rd, rs1, rs2)); emit (Psltul(rd, X0, X rd))
      end
*)| Pcvtl2w (rd, rs) ->
      assert Archi.ptr64;
      emit (Paddiw (rd, rs, Integers.Int.zero))  (* 32-bit sign extension *)

(*| Pjal_r(r, sg) ->
      fixup_call sg; emit instr
  | Pjal_s(symb, sg) ->
      fixup_call sg; emit instr
  | Pj_r(r, sg) when r <> X1 ->
      fixup_call sg; emit instr
  | Pj_s(symb, sg) ->
      fixup_call sg; emit instr

*)| Pbuiltin (ef,args,res) ->
     begin match ef with
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
(*     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res *)
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy sz al args
 (*  | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
    *)
     | EF_malloc -> failwith "asmexpand: malloc"
     | EF_free -> failwith "asmexpand: free"
     | EF_debug _ -> failwith "asmexpand: debug"
     | EF_annot _ -> emit instr
     | EF_annot_val (kind, txt, targ) -> expand_annot_val kind txt targ args res
     | EF_external _ -> failwith "asmexpand: external"
     | EF_inline_asm _ -> emit instr
     | EF_runtime _ -> failwith "asmexpand: runtime"
     | EF_profiling _ -> emit instr
     end
  | _ ->
     emit instr

(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)
let int_reg_to_dwarf = let open Asmvliw in function
   | GPR0  -> 1   | GPR1  -> 2   | GPR2  -> 3   | GPR3  -> 4   | GPR4  -> 5
   | GPR5  -> 6   | GPR6  -> 7   | GPR7  -> 8   | GPR8  -> 9   | GPR9  -> 10
   | GPR10 -> 11  | GPR11 -> 12  | GPR12 -> 13  | GPR13 -> 14  | GPR14 -> 15
   | GPR15 -> 16  | GPR16 -> 17  | GPR17 -> 18  | GPR18 -> 19  | GPR19 -> 20
   | GPR20 -> 21  | GPR21 -> 22  | GPR22 -> 23  | GPR23 -> 24  | GPR24 -> 25
   | GPR25 -> 26  | GPR26 -> 27  | GPR27 -> 28  | GPR28 -> 29  | GPR29 -> 30
   | GPR30 -> 31  | GPR31 -> 32  | GPR32 -> 33  | GPR33 -> 34  | GPR34 -> 35
   | GPR35 -> 36  | GPR36 -> 37  | GPR37 -> 38  | GPR38 -> 39  | GPR39 -> 40
   | GPR40 -> 41  | GPR41 -> 42  | GPR42 -> 43  | GPR43 -> 44  | GPR44 -> 45
   | GPR45 -> 46  | GPR46 -> 47  | GPR47 -> 48  | GPR48 -> 49  | GPR49 -> 50
   | GPR50 -> 51  | GPR51 -> 52  | GPR52 -> 53  | GPR53 -> 54  | GPR54 -> 55
   | GPR55 -> 56  | GPR56 -> 57  | GPR57 -> 58  | GPR58 -> 59  | GPR59 -> 60
   | GPR60 -> 61  | GPR61 -> 62  | GPR62 -> 63  | GPR63 -> 64

let preg_to_dwarf = let open Asmvliw in function
   | IR r -> int_reg_to_dwarf r
   | RA   -> 65 (* FIXME - No idea what is $ra DWARF number in k1-gdb *)
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    expand id (* sp= *) 2 preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
