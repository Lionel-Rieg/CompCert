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

(* Processor-dependent builtin C functions *)

open C

let builtins = {
  builtin_typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  (* The builtin list is inspired from the GCC file builtin_k1.h *)
  builtin_functions = [ (* Some builtins are commented out because their opcode is not present (yet?) *)
      (* BCU Instructions *)
      "__builtin_k1_await", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_barrier", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_doze", (TVoid [], [], false); (* opcode not supported in assembly, not in documentation *)
      "__builtin_k1_wfxl", (TVoid [], [TInt(IUChar, []); TInt(ILongLong, [])], false); (* DONE *)
      "__builtin_k1_wfxm", (TVoid [], [TInt(IUChar, []); TInt(ILongLong, [])], false); (* DONE *)
      "__builtin_k1_sleep", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_stop", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_syncgroup", (TVoid [], [TInt(IULongLong, [])], false);
      "__builtin_k1_tlbread", (TVoid [], [], false);
      "__builtin_k1_tlbwrite", (TVoid [], [], false);
      "__builtin_k1_tlbprobe", (TVoid [], [], false);
      "__builtin_k1_tlbdinval", (TVoid [], [], false);
      "__builtin_k1_tlbiinval", (TVoid [], [], false);
      
      "__builtin_k1_get", (TInt(IULongLong, []), [TInt(IInt, [])], false); (* DONE *)
      "__builtin_k1_set", (TVoid [], [TInt(IInt, []); TInt(IULongLong, [])], false); (* DONE *)
      
      (* LSU Instructions *)
      (* acswapd and acswapw done using headers and assembly *)
(*     "__builtin_k1_afaddd", (TInt(IULongLong, []), [TPtr(TVoid [], []); TInt(ILongLong, [])], false);
       "__builtin_k1_afaddw", (TInt(IUInt, []), [TPtr(TVoid [], []); TInt(IInt, [])], false); *) (* see #157 *)
      "__builtin_k1_alclrd", (TInt(IULongLong, []), [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_alclrw", (TInt(IUInt, []), [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_dinval", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_dinvall", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_dtouchl", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_dzerol", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_fence", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_iinval", (TVoid [], [], false); (* DONE *)
      "__builtin_k1_iinvals", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_itouchl", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE [not supported by assembler but in documentation] *)
      "__builtin_k1_lbsu", (TInt(IChar, []), [TPtr(TVoid [], [])], false);
      "__builtin_k1_lbzu", (TInt(IUChar, []), [TPtr(TVoid [], [])], false);
      "__builtin_k1_ldu", (TInt(IULongLong, []), [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_k1_lhsu", (TInt(IShort, []), [TPtr(TVoid [], [])], false);
      "__builtin_k1_lhzu", (TInt(IUShort, []), [TPtr(TVoid [], [])], false);
      "__builtin_k1_lwzu", (TInt(IUInt, []), [TPtr(TVoid [], [])], false);

      (* ALU Instructions *)
      (* "__builtin_k1_addhp", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_k1_adds", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_k1_bwlu", (TInt(IUInt, []), 
        [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, []); TInt(IUShort, [])], false); *)
      (* "__builtin_k1_bwluhp", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_k1_bwluwp", (TInt(IULongLong, []), 
        [TInt(IULongLong, []); TInt(IULongLong, []); TInt(IUInt, [])], false); *)
      (* "__builtin_k1_cbs", (TInt(IInt, []), [TInt(IUInt, [])], false); *)
      (* "__builtin_k1_cbsdl", (TInt(ILongLong, []), [TInt(IULongLong, [])], false); *)
      (* "__builtin_k1_clz", (TInt(IInt, []), [TInt(IUInt, [])], false); *)
      "__builtin_clzw", (TInt(IInt, []), [TInt(IUInt, [])], false);
      "__builtin_clzll", (TInt(ILongLong, []), [TInt(IULongLong, [])], false);
      (* "__builtin_k1_clzdl", (TInt(ILongLong, []), [TInt(IULongLong, [])], false); *)
      (* "__builtin_k1_cmove", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_k1_ctz", (TInt(IInt, []), [TInt(IUInt, [])], false); *)
      "__builtin_k1_ctzw", (TInt(IInt, []), [TInt(IUInt, [])], false);
      "__builtin_k1_ctzd", (TInt(ILongLong, []), [TInt(IULongLong, [])], false);
      (* "__builtin_k1_ctzdl", (TInt(ILongLong, []), [TInt(IULongLong, [])], false); *)
      (* "__builtin_k1_extfz", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_k1_landhp", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_k1_sat", (TInt(IInt, []), [TInt(IInt, []); TInt(IUChar, [])], false); *)
      "__builtin_k1_satd", (TInt(ILongLong, []), [TInt(ILongLong, []); TInt(IUChar, [])], false);
      (* "__builtin_k1_sbfhp", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false); *)
      "__builtin_k1_sbmm8", (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);
      "__builtin_k1_sbmmt8", (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);
      (* "__builtin_k1_sllhps", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_k1_srahps", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_k1_stsu", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false); *)
      "__builtin_k1_stsud", (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);


    (* Synchronization *)
(*  "__builtin_fence",
      (TVoid [], [], false); *)
(*  (* Float arithmetic *)
    "__builtin_fmadd",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmsub",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fnmadd",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fnmsub",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])], false); *)
    "__builtin_fabsf",
      (TFloat(FFloat, []),
       [TFloat(FFloat, [])], false);
    "__builtin_fmax",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmin",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmaxf",
      (TFloat(FFloat, []),
       [TFloat(FFloat, []); TFloat(FFloat, [])], false);
    "__builtin_fminf",
      (TFloat(FFloat, []),
       [TFloat(FFloat, []); TFloat(FFloat, [])], false);
    "__builtin_fma",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmaf",
      (TFloat(FFloat, []),
       [TFloat(FFloat, []); TFloat(FFloat, []); TFloat(FFloat, [])], false);
]
}

let va_list_type = TPtr(TVoid [], [])  (* to check! *)
let size_va_list = if Archi.ptr64 then 8 else 4
let va_list_scalar = true

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "0(%s)" arg
