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
  (* The builtin list is inspired from the GCC file builtin_kvx.h *)
  builtin_functions = [ (* Some builtins are commented out because their opcode is not present (yet?) *)
      (* BCU Instructions *)
      "__builtin_kvx_await", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_barrier", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_doze", (TVoid [], [], false); (* opcode not supported in assembly, not in documentation *)
      "__builtin_kvx_wfxl", (TVoid [], [TInt(IUChar, []); TInt(ILongLong, [])], false); (* DONE *)
      "__builtin_kvx_wfxm", (TVoid [], [TInt(IUChar, []); TInt(ILongLong, [])], false); (* DONE *)
      "__builtin_kvx_sleep", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_stop", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_syncgroup", (TVoid [], [TInt(IULongLong, [])], false);
      "__builtin_kvx_tlbread", (TVoid [], [], false);
      "__builtin_kvx_tlbwrite", (TVoid [], [], false);
      "__builtin_kvx_tlbprobe", (TVoid [], [], false);
      "__builtin_kvx_tlbdinval", (TVoid [], [], false);
      "__builtin_kvx_tlbiinval", (TVoid [], [], false);
      
      "__builtin_kvx_get", (TInt(IULongLong, []), [TInt(IInt, [])], false); (* DONE *)
      "__builtin_kvx_set", (TVoid [], [TInt(IInt, []); TInt(IULongLong, [])], false); (* DONE *)
      
      (* LSU Instructions *)
      (* acswapd and acswapw done using headers and assembly *)
(*     "__builtin_kvx_afaddd", (TInt(IULongLong, []), [TPtr(TVoid [], []); TInt(ILongLong, [])], false);
       "__builtin_kvx_afaddw", (TInt(IUInt, []), [TPtr(TVoid [], []); TInt(IInt, [])], false); *) (* see #157 *)
      "__builtin_kvx_alclrd", (TInt(IULongLong, []), [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_alclrw", (TInt(IUInt, []), [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_dinval", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_dinvall", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_dtouchl", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_dzerol", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_fence", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_iinval", (TVoid [], [], false); (* DONE *)
      "__builtin_kvx_iinvals", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_itouchl", (TVoid [], [TPtr(TVoid [], [])], false); (* DONE [not supported by assembler but in documentation] *)
      "__builtin_kvx_lbsu", (TInt(IChar, []), [TPtr(TVoid [], [])], false);
      "__builtin_kvx_lbzu", (TInt(IUChar, []), [TPtr(TVoid [], [])], false);
      "__builtin_kvx_ldu", (TInt(IULongLong, []), [TPtr(TVoid [], [])], false); (* DONE *)
      "__builtin_kvx_lhsu", (TInt(IShort, []), [TPtr(TVoid [], [])], false);
      "__builtin_kvx_lhzu", (TInt(IUShort, []), [TPtr(TVoid [], [])], false);
      "__builtin_kvx_lwzu", (TInt(IUInt, []), [TPtr(TVoid [], [])], false);

      (* ALU Instructions *)
      (* "__builtin_kvx_addhp", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_kvx_adds", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_kvx_bwlu", (TInt(IUInt, []), 
        [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, []); TInt(IUShort, [])], false); *)
      (* "__builtin_kvx_bwluhp", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_kvx_bwluwp", (TInt(IULongLong, []), 
        [TInt(IULongLong, []); TInt(IULongLong, []); TInt(IUInt, [])], false); *)
      (* "__builtin_kvx_cbs", (TInt(IInt, []), [TInt(IUInt, [])], false); *)
      (* "__builtin_kvx_cbsdl", (TInt(ILongLong, []), [TInt(IULongLong, [])], false); *)
      (* "__builtin_kvx_clz", (TInt(IInt, []), [TInt(IUInt, [])], false); *)
      "__builtin_clzw", (TInt(IInt, []), [TInt(IUInt, [])], false);
      "__builtin_clzll", (TInt(ILongLong, []), [TInt(IULongLong, [])], false);
      (* "__builtin_kvx_clzdl", (TInt(ILongLong, []), [TInt(IULongLong, [])], false); *)
      (* "__builtin_kvx_cmove", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_kvx_ctz", (TInt(IInt, []), [TInt(IUInt, [])], false); *)
      "__builtin_kvx_ctzw", (TInt(IInt, []), [TInt(IUInt, [])], false);
      "__builtin_kvx_ctzd", (TInt(ILongLong, []), [TInt(IULongLong, [])], false);
      (* "__builtin_kvx_ctzdl", (TInt(ILongLong, []), [TInt(IULongLong, [])], false); *)
      (* "__builtin_kvx_extfz", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_kvx_landhp", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, []); TInt(IInt, [])], false); *)
      (* "__builtin_kvx_sat", (TInt(IInt, []), [TInt(IInt, []); TInt(IUChar, [])], false); *)
      "__builtin_kvx_satd", (TInt(ILongLong, []), [TInt(ILongLong, []); TInt(IUChar, [])], false);
      (* "__builtin_kvx_sbfhp", (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false); *)
      "__builtin_kvx_sbmm8", (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);
      "__builtin_kvx_sbmmt8", (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);
      (* "__builtin_kvx_sllhps", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_kvx_srahps", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false); *)
      (* "__builtin_kvx_stsu", (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false); *)
      "__builtin_kvx_stsud", (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);


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
