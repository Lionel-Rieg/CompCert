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

(* Additional extraction directives specific to the RISC-V port *)

Require Archi Asm.

(* Archi *)

Extract Constant Archi.ptr64 => " Configuration.model = ""64"" ".
Extract Constant Archi.pic_code => "fun () -> false".  (* for the time being *)

Extract Constant Peephole.print_found_store =>
"fun offset x -> Printf.printf ""found offset = %ld\n"" (Camlcoq.camlint_of_coqint offset); x".

(* Asm *)
(*
Extract Constant Asm.low_half => "fun _ _ _ -> assert false".
Extract Constant Asm.high_half => "fun _ _ _ -> assert false".
*)
