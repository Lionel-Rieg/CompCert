(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

open Asmvliw
open Asmblock
open Printf
open Camlcoq
open InstructionScheduler
open TargetPrinter.Target

let debug = false

(**
 * Extracting infos from Asmvliw instructions
 *)

type immediate = I32 of Integers.Int.int | I64 of Integers.Int64.int | Off of offset

type location = Reg of preg | Mem

type real_instruction =
  (* ALU *)
  | Addw | Andw | Compw | Mulw | Orw | Sbfw | Sbfxw | Sraw | Srlw | Sllw | Srsw | Rorw | Xorw
  | Addd | Andd | Compd | Muld | Ord | Sbfd | Sbfxd | Srad | Srld | Slld | Srsd | Xord
  | Nandw | Norw | Nxorw | Nandd | Nord | Nxord | Andnw | Ornw | Andnd | Ornd
  | Maddw | Maddd | Msbfw | Msbfd | Cmoved
  | Make | Nop | Extfz | Extfs | Insf
  | Addxw | Addxd
  (* LSU *)
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld | Lq | Lo
  | Sb | Sh | Sw | Sd | Sq | So
  (* BCU *)
  | Icall | Call | Cb | Igoto | Goto | Ret | Get | Set
  (* FPU *)
  | Fabsd | Fabsw | Fnegw | Fnegd
  | Faddd | Faddw | Fsbfd | Fsbfw | Fmuld | Fmulw
  | Fmind | Fminw | Fmaxd | Fmaxw | Finvw
  | Ffmaw | Ffmad | Ffmsw | Ffmsd
  | Fnarrowdw | Fwidenlwd | Floatwz | Floatuwz | Floatdz | Floatudz | Fixedwz | Fixeduwz | Fixeddz | Fixedudz
  | Fcompw | Fcompd

type ab_inst_rec = {
  inst: real_instruction;
  write_locs : location list;
  read_locs : location list;
  read_at_id : location list; (* Must be contained in read_locs *)
  read_at_e1 : location list; (* idem *)
  imm : immediate option;
  is_control : bool;
}

(** Asmvliw constructor to real instructions *)

exception OpaqueInstruction

let arith_rr_real = function
  | Pcvtl2w ->          Addw
  | Pmv ->              Addd
  | Pnegw ->            Sbfw
  | Pnegl ->            Sbfd
  | Psxwd ->            Extfs
  | Pzxwd ->            Extfz
  | Pextfz(_,_) ->      Extfz
  | Pextfs(_,_) ->      Extfs
  | Pextfzl(_,_) ->     Extfz
  | Pextfsl(_,_) ->     Extfs
  | Pfabsw ->           Fabsw
  | Pfabsd ->           Fabsd
  | Pfnegw ->           Fnegw
  | Pfnegd ->           Fnegd
  | Pfinvw ->           Finvw
  | Pfnarrowdw ->       Fnarrowdw
  | Pfwidenlwd ->       Fwidenlwd
  | Pfloatwrnsz ->      Floatwz
  | Pfloatuwrnsz ->     Floatuwz
  | Pfloatudrnsz ->     Floatudz
  | Pfloatdrnsz ->      Floatdz
  | Pfixedwrzz ->       Fixedwz
  | Pfixeduwrzz ->      Fixeduwz
  | Pfixeddrzz ->       Fixeddz
  | Pfixedudrzz ->      Fixedudz
  | Pfixeddrzz_i32 ->   Fixeddz
  | Pfixedudrzz_i32 ->  Fixedudz

let arith_rrr_real = function
  | Pcompw it ->      Compw
  | Pcompl it ->      Compd
  | Pfcompw ft ->     Fcompw
  | Pfcompl ft ->     Fcompd
  | Paddw ->          Addw
  | Paddxw _ ->       Addxw
  | Psubw ->          Sbfw
  | Prevsubxw _ ->    Sbfxw
  | Pmulw ->          Mulw
  | Pandw ->          Andw
  | Pnandw ->         Nandw
  | Porw ->           Orw
  | Pnorw ->          Norw
  | Pxorw ->          Xorw
  | Pnxorw ->         Nxorw
  | Pandnw ->         Andnw
  | Pornw ->          Ornw
  | Psraw ->          Sraw
  | Psrlw ->          Srlw
  | Psrxw ->          Srsw
  | Psllw ->          Sllw
  | Paddl ->          Addd
  | Paddxl _ ->       Addxd
  | Psubl ->          Sbfd
  | Prevsubxl _ ->    Sbfxd
  | Pandl ->          Andd
  | Pnandl ->         Nandd
  | Porl ->           Ord
  | Pnorl ->          Nord
  | Pxorl ->          Xord
  | Pnxorl ->         Nxord
  | Pandnl ->         Andnd
  | Pornl ->          Ornd
  | Pmull ->          Muld
  | Pslll ->          Slld
  | Psrll ->          Srld
  | Psrxl ->          Srsd
  | Psral ->          Srad
  | Pfaddd ->         Faddd
  | Pfaddw ->         Faddw
  | Pfsbfd ->         Fsbfd
  | Pfsbfw ->         Fsbfw
  | Pfmuld ->         Fmuld
  | Pfmulw ->         Fmulw
  | Pfmind ->         Fmind
  | Pfminw ->         Fminw
  | Pfmaxd ->         Fmaxd
  | Pfmaxw ->         Fmaxw

let arith_rri32_real = function
  | Pcompiw it ->   Compw
  | Paddiw ->       Addw
  | Paddxiw _ ->    Addxw
  | Prevsubiw ->    Sbfw
  | Prevsubxiw _ -> Sbfxw
  | Pmuliw ->       Mulw
  | Pandiw ->       Andw
  | Pnandiw ->      Nandw
  | Poriw ->        Orw
  | Pnoriw ->       Norw
  | Pxoriw ->       Xorw
  | Pnxoriw ->      Nxorw
  | Pandniw ->      Andnw
  | Porniw ->       Ornw
  | Psraiw ->       Sraw
  | Psrxiw ->       Srsw
  | Psrliw ->       Srlw
  | Pslliw ->       Sllw
  | Proriw ->       Rorw
  | Psllil ->       Slld
  | Psrlil ->       Srld
  | Psrail ->       Srad
  | Psrxil ->       Srsd

let arith_rri64_real = function
  | Pcompil it ->   Compd
  | Paddil ->       Addd
  | Prevsubil ->    Sbfd
  | Paddxil _ ->    Addxd
  | Prevsubxil _ -> Sbfxd
  | Pmulil ->       Muld
  | Pandil ->       Andd
  | Pnandil ->      Nandd
  | Poril ->        Ord
  | Pnoril ->       Nord
  | Pxoril ->       Xord
  | Pnxoril ->      Nxord
  | Pandnil ->      Andnd
  | Pornil ->       Ornd


let arith_arr_real = function
  | Pinsf (_, _) ->   Insf
  | Pinsfl (_, _) ->  Insf

let arith_arrr_real = function
  | Pfmaddfw -> Ffmaw
  | Pfmaddfl -> Ffmad
  | Pfmsubfw -> Ffmsw
  | Pfmsubfl -> Ffmsd
  | Pmaddw ->     Maddw
  | Pmaddl ->     Maddd
  | Pmsubw ->     Msbfw
  | Pmsubl ->     Msbfd
  | Pcmove _ ->   Cmoved
  | Pcmoveu _ ->  Cmoved

let arith_arri32_real = function
  | Pmaddiw ->      Maddw
  | Pcmoveiw _ ->   Cmoved
  | Pcmoveuiw _ ->  Cmoved

let arith_arri64_real = function
  | Pmaddil ->      Maddd
  | Pcmoveil _ ->   Cmoved
  | Pcmoveuil _ ->  Cmoved

let arith_ri32_real = Make

let arith_ri64_real = Make

let arith_rf32_real = Make

let arith_rf64_real = Make

let store_real = function
  | Psb ->    Sb
  | Psh ->    Sh
  | Psw ->    Sw
  | Psw_a ->  Sw
  | Psd ->    Sd
  | Psd_a ->  Sd
  | Pfss ->   Sw
  | Pfsd ->   Sd

let load_real = function
  | Plb ->    Lbs
  | Plbu ->   Lbz
  | Plh ->    Lhs
  | Plhu ->   Lhz
  | Plw ->    Lws
  | Plw_a ->  Lws
  | Pld ->    Ld
  | Pld_a ->  Ld
  | Pfls ->   Lws
  | Pfld ->   Ld

let set_real = Set
let get_real = Get
let nop_real = Nop
let loadsymbol_real = Make
let loadqrro_real = Lq
let loadorro_real = Lo
let storeqrro_real = Sq
let storeorro_real = So

let ret_real = Ret
let call_real = Call
let icall_real = Icall
let goto_real = Goto
let igoto_real = Igoto
let jl_real = Goto
let cb_real = Cb
let cbu_real = Cb

let arith_rri32_rec i rd rs imm32 = { inst = arith_rri32_real i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = imm32; is_control = false;
                                      read_at_id = []; read_at_e1 = [] }

let arith_rri64_rec i rd rs imm64 = { inst = arith_rri64_real i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = imm64; is_control = false;
                                      read_at_id = []; read_at_e1 = [] }

let arith_rrr_rec i rd rs1 rs2 = { inst = arith_rrr_real i; write_locs = [Reg rd]; read_locs = [Reg rs1; Reg rs2]; imm = None; is_control = false;
                                      read_at_id = []; read_at_e1 = [] }

let arith_arri32_rec i rd rs imm32 = 
  let rae1 = match i with Pmaddiw -> [Reg rd] | _ -> []
  in {  inst = arith_arri32_real i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs]; imm = imm32; is_control = false;
        read_at_id = [] ; read_at_e1 = rae1 }

let arith_arri64_rec i rd rs imm64 = 
  let rae1 = match i with Pmaddil -> [Reg rd] | _ -> []
  in {  inst = arith_arri64_real i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs]; imm = imm64; is_control = false;
        read_at_id = []; read_at_e1 = rae1 }

let arith_arr_rec i rd rs = { inst = arith_arr_real i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs]; imm = None; is_control = false;
                              read_at_id = []; read_at_e1 = [] }

let arith_arrr_rec i rd rs1 rs2 = 
  let rae1 = match i with Pmaddl | Pmaddw | Pmsubl | Pmsubw -> [Reg rd] | _ -> []
  in {  inst = arith_arrr_real i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs1; Reg rs2]; imm = None; is_control = false;
        read_at_id = []; read_at_e1 = rae1 }

let arith_rr_rec i rd rs = {  inst = arith_rr_real i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = None; is_control = false;
                              read_at_id = []; read_at_e1 = [] }

let arith_r_rec i rd = match i with
    (* For Ploadsymbol, writing the highest integer since we do not know how many bits does a symbol have *)
  | Ploadsymbol (id, ofs) -> {  inst = loadsymbol_real; write_locs = [Reg rd]; read_locs = []; imm = Some (I64 Integers.Int64.max_signed);
                                is_control = false; read_at_id = []; read_at_e1 = [] }

let arith_rec i =
  match i with
  | PArithRRI32 (i, rd, rs, imm32) -> arith_rri32_rec i (IR rd) (IR rs) (Some (I32 imm32))
  | PArithRRI64 (i, rd, rs, imm64) -> arith_rri64_rec i (IR rd) (IR rs) (Some (I64 imm64))
  | PArithRRR (i, rd, rs1, rs2) -> arith_rrr_rec i (IR rd) (IR rs1) (IR rs2)
  | PArithARR (i, rd, rs) -> arith_arr_rec i (IR rd) (IR rs)
  (* Seems like single constant constructor types are elided *)
  | PArithARRI32 (i, rd, rs, imm32) -> arith_arri32_rec i (IR rd) (IR rs) (Some (I32 imm32))
  | PArithARRI64 (i, rd, rs, imm64) -> arith_arri64_rec i (IR rd) (IR rs) (Some (I64 imm64))
  | PArithARRR (i, rd, rs1, rs2) -> arith_arrr_rec i (IR rd) (IR rs1) (IR rs2)
  | PArithRI32 (rd, imm32) -> { inst = arith_ri32_real; write_locs = [Reg (IR rd)]; read_locs = []; imm = (Some (I32 imm32)) ; is_control = false;
                                read_at_id = []; read_at_e1 = [] }
  | PArithRI64 (rd, imm64) -> { inst = arith_ri64_real; write_locs = [Reg (IR rd)]; read_locs = []; imm = (Some (I64 imm64)) ; is_control = false;
                                read_at_id = []; read_at_e1 = [] }
  | PArithRF32 (rd, f) -> { inst = arith_rf32_real; write_locs = [Reg (IR rd)]; read_locs = [];
                            imm = (Some (I32 (Floats.Float32.to_bits f))); is_control = false; read_at_id = []; read_at_e1 = []}
  | PArithRF64 (rd, f) -> { inst = arith_rf64_real; write_locs = [Reg (IR rd)]; read_locs = [];
                            imm = (Some (I64 (Floats.Float.to_bits f))); is_control = false; read_at_id = []; read_at_e1 = []}
  | PArithRR (i, rd, rs) -> arith_rr_rec i (IR rd) (IR rs)
  | PArithR (i, rd) -> arith_r_rec i (IR rd)

let load_rec i = match i with
  | PLoadRRO (trap, i, rs1, rs2, imm) ->
      { inst = load_real i; write_locs = [Reg (IR rs1)]; read_locs = [Mem; Reg (IR rs2)]; imm = (Some (Off imm)) ; is_control = false;
        read_at_id = []; read_at_e1 = [] }
  | PLoadQRRO(rs, ra, imm) ->
     let (rs0, rs1) = gpreg_q_expand rs in
     { inst = loadqrro_real; write_locs = [Reg (IR rs0); Reg (IR rs1)]; read_locs = [Mem; Reg (IR ra)]; imm = (Some (Off imm)) ; is_control = false;
       read_at_id = []; read_at_e1 = [] }
  | PLoadORRO(rs, ra, imm) ->
     let (((rs0, rs1), rs2), rs3) = gpreg_o_expand rs in
     {  inst = loadorro_real; write_locs = [Reg (IR rs0); Reg (IR rs1); Reg (IR rs2); Reg (IR rs3)]; read_locs = [Mem; Reg (IR ra)];
        imm = (Some (Off imm)) ; is_control = false; read_at_id = []; read_at_e1 = []}
  | PLoadRRR (trap, i, rs1, rs2, rs3) | PLoadRRRXS (trap, i, rs1, rs2, rs3) ->
      { inst = load_real i; write_locs = [Reg (IR rs1)]; read_locs = [Mem; Reg (IR rs2); Reg (IR rs3)]; imm = None ; is_control = false;
        read_at_id = []; read_at_e1 = [] }

let store_rec i = match i with
  | PStoreRRO (i, rs, ra, imm) ->
      {  inst = store_real i; write_locs = [Mem]; read_locs = [Reg (IR rs); Reg (IR ra)]; imm = (Some (Off imm));
        read_at_id = []; read_at_e1 = [Reg (IR rs)] ; is_control = false}
  | PStoreQRRO (rs, ra, imm) ->
     let (rs0, rs1) = gpreg_q_expand rs in
     {  inst = storeqrro_real; write_locs = [Mem]; read_locs = [Reg (IR rs0); Reg (IR rs1); Reg (IR ra)]; imm = (Some (Off imm));
        read_at_id = []; read_at_e1 = [Reg (IR rs0); Reg (IR rs1)] ; is_control = false}
  | PStoreORRO (rs, ra, imm) ->
     let (((rs0, rs1), rs2), rs3) = gpreg_o_expand rs in
     {  inst = storeorro_real; write_locs = [Mem]; read_locs = [Reg (IR rs0); Reg (IR rs1); Reg (IR rs2); Reg (IR rs3); Reg (IR ra)];
        imm = (Some (Off imm)); read_at_id = []; read_at_e1 = [Reg (IR rs0); Reg (IR rs1); Reg (IR rs2); Reg (IR rs3)]; is_control = false}
  | PStoreRRR (i, rs, ra1, ra2)  | PStoreRRRXS (i, rs, ra1, ra2) ->
     {  inst = store_real i; write_locs = [Mem]; read_locs = [Reg (IR rs); Reg (IR ra1); Reg (IR ra2)]; imm = None;
        read_at_id = []; read_at_e1 = [Reg (IR rs)]; is_control = false}

let get_rec (rd:gpreg) rs = { inst = get_real; write_locs = [Reg (IR rd)]; read_locs = [Reg rs]; imm = None; is_control = false;
                              read_at_id = []; read_at_e1 = [] }

let set_rec rd (rs:gpreg) = { inst = set_real; write_locs = [Reg rd]; read_locs = [Reg (IR rs)]; imm = None; is_control = false;
                              read_at_id = [Reg (IR rs)]; read_at_e1 = [] }

let basic_rec i =
  match i with
  | PArith i -> arith_rec i
  | PLoad i -> load_rec i
  | PStore i -> store_rec i
  | Pallocframe (_, _) -> raise OpaqueInstruction
  | Pfreeframe (_, _) -> raise OpaqueInstruction
  | Pget (rd, rs) -> get_rec rd rs
  | Pset (rd, rs) -> set_rec rd rs
  | Pnop -> { inst = nop_real; write_locs = []; read_locs = []; imm = None ; is_control = false; read_at_id = []; read_at_e1 = []}

let expand_rec = function
  | Pbuiltin _ -> raise OpaqueInstruction

let ctl_flow_rec = function
  | Pret -> { inst = ret_real; write_locs = []; read_locs = [Reg RA]; imm = None ; is_control = true; read_at_id = [Reg RA]; read_at_e1 = []}
  | Pcall lbl -> { inst = call_real; write_locs = [Reg RA]; read_locs = []; imm = None ; is_control = true; read_at_id = []; read_at_e1 = []}
  | Picall r -> { inst = icall_real; write_locs = [Reg RA]; read_locs = [Reg (IR r)]; imm = None; is_control = true;
                  read_at_id = [Reg (IR r)]; read_at_e1 = [] }
  | Pgoto lbl -> { inst = goto_real; write_locs = []; read_locs = []; imm = None ; is_control = true; read_at_id = []; read_at_e1 = []}
  | Pigoto r -> { inst = igoto_real; write_locs = []; read_locs = [Reg (IR r)]; imm = None ; is_control = true;
                  read_at_id = [Reg (IR r)]; read_at_e1 = [] }
  | Pj_l lbl -> { inst = goto_real; write_locs = []; read_locs = []; imm = None ; is_control = true; read_at_id = []; read_at_e1 = []}
  | Pcb (bt, rs, lbl) -> { inst = cb_real; write_locs = []; read_locs = [Reg (IR rs)]; imm = None ; is_control = true;
                           read_at_id = [Reg (IR rs)]; read_at_e1 = [] }
  | Pcbu (bt, rs, lbl) -> { inst = cbu_real; write_locs = []; read_locs = [Reg (IR rs)]; imm = None ; is_control = true;
                           read_at_id = [Reg (IR rs)]; read_at_e1 = [] }
  | Pjumptable (r, _) -> raise OpaqueInstruction (* { inst = "Pjumptable"; write_locs = [Reg (IR GPR62); Reg (IR GPR63)]; read_locs = [Reg (IR r)]; imm = None ; is_control = true} *)

let control_rec i =
  match i with
  | PExpand i -> expand_rec i
  | PCtlFlow i -> ctl_flow_rec i

let rec basic_recs body = match body with
  | [] -> []
  | bi :: body -> (basic_rec bi) :: (basic_recs body)

let exit_rec exit = match exit with
  | None -> []
  | Some ex -> [control_rec ex]

let instruction_recs bb = (basic_recs bb.body) @ (exit_rec bb.exit)

(**
 * Providing informations relative to the real instructions
 *)

(** Abstraction providing all the necessary informations for solving the scheduling problem *)
type inst_info = {
  write_locs : location list;
  read_locs : location list;
  reads_at_id : bool;
  reads_at_e1 : bool;
  is_control : bool;
  usage: int array; (* resources consumed by the instruction *)
  latency: int;
}

(** Figuring out whether an immediate is s10, u27l10 or e27u27l10 *)
type imm_encoding = U6 | S10 | U27L5 | U27L10 | E27U27L10

let rec pow a = function
  | 0 -> Int64.one
  | 1 -> Int64.of_int a
  | n -> let b = pow a (n/2) in
         Int64.mul b (Int64.mul b (if n mod 2 = 0 then Int64.one else Int64.of_int a))

let signed_interval n : (int64 * int64) = begin 
  assert (n > 0);
  let min = Int64.neg @@ pow 2 (n-1)
  and max = Int64.sub (pow 2 (n-1)) Int64.one
  in (min, max)
end

let within i interv = match interv with (min, max) -> (i >= min && i <= max)

let signed_length (i:int64) =
  let rec f (i:int64) n = 
    let interv = signed_interval n
    in if (within i interv) then n else f i (n+1)
  in f i 1

let unsigned_length (i:int64) = (signed_length i) - 1

let encode_imm (imm:int64) =
  if (Int64.compare imm Int64.zero < 0) then
    let length = signed_length imm
    in if length <= 10 then S10
    else if length <= 32 then U27L5
    else if length <= 37 then U27L10
    else if length <= 64 then E27U27L10
    else failwith @@ sprintf "encode_imm: integer too big! (%Ld)" imm
  else
    let length = unsigned_length imm
    in if length <= 6 then U6
    else if length <= 9 then S10 (* Special case for S10 - stay signed no matter what *)
    else if length <= 32 then U27L5
    else if length <= 37 then U27L10
    else if length <= 64 then E27U27L10
    else failwith @@ sprintf "encode_imm: integer too big! (%Ld)" imm

(** Resources *)
type rname = Rissue | Rtiny | Rlite | Rfull | Rlsu | Rmau | Rbcu | Rtca | Rauxr | Rauxw | Rcrrp | Rcrwl | Rcrwh | Rnop

let resource_names = [Rissue; Rtiny; Rlite; Rfull; Rlsu; Rmau; Rbcu; Rtca; Rauxr; Rauxw; Rcrrp; Rcrwl; Rcrwh; Rnop]

let rec find_index elt l =
  match l with
  | [] -> raise Not_found
  | e::l -> if (e == elt) then 0
            else 1 + find_index elt l

let resource_id resource : int = find_index resource resource_names

let resource_bound resource : int =
  match resource with
  | Rissue -> 8
  | Rtiny -> 4
  | Rlite -> 2
  | Rfull -> 1
  | Rlsu -> 1
  | Rmau -> 1
  | Rbcu -> 1
  | Rtca -> 1
  | Rauxr -> 1
  | Rauxw -> 1
  | Rcrrp -> 1
  | Rcrwl -> 1
  | Rcrwh -> 1
  | Rnop -> 4

let resource_bounds : int array = Array.of_list (List.map resource_bound resource_names)

(** Reservation tables *)
let alu_full : int array = let resmap = fun r -> match r with
  | Rissue -> 1 | Rtiny -> 1 | Rlite -> 1 | Rfull -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_lite : int array = let resmap = fun r -> match r with 
  | Rissue -> 1 | Rtiny -> 1 | Rlite -> 1 |  _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_lite_x : int array = let resmap = fun r -> match r with 
  | Rissue -> 2 | Rtiny -> 1 | Rlite -> 1 |  _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_lite_y : int array = let resmap = fun r -> match r with 
  | Rissue -> 3 | Rtiny -> 1 | Rlite -> 1 |  _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_nop : int array = let resmap = fun r -> match r with 
  | Rissue -> 1 | Rnop -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_tiny : int array = let resmap = fun r -> match r with
  | Rissue -> 1 | Rtiny -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_tiny_x : int array = let resmap = fun r -> match r with
  | Rissue -> 2 | Rtiny -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_tiny_y : int array = let resmap = fun r -> match r with
  | Rissue -> 3 | Rtiny -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let bcu : int array = let resmap = fun r -> match r with 
  | Rissue -> 1 | Rbcu -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let bcu_tiny_tiny_mau_xnop : int array = let resmap = fun r -> match r with 
  | Rissue -> 1 | Rtiny -> 2 | Rmau -> 1 | Rbcu -> 1 | Rnop -> 4 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_auxr : int array = let resmap = fun r -> match r with
  | Rissue -> 1 | Rtiny -> 1 | Rlsu -> 1 | Rauxr -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_auxr_x : int array = let resmap = fun r -> match r with
  | Rissue -> 2 | Rtiny -> 1 | Rlsu -> 1 | Rauxr -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_auxr_y : int array = let resmap = fun r -> match r with
  | Rissue -> 3 | Rtiny -> 1 | Rlsu -> 1 | Rauxr -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_auxw : int array = let resmap = fun r -> match r with
  | Rissue -> 1 | Rtiny -> 1 | Rlsu -> 1 | Rauxw -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_auxw_x : int array = let resmap = fun r -> match r with
  | Rissue -> 2 | Rtiny -> 1 | Rlsu -> 1 | Rauxw -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_auxw_y : int array = let resmap = fun r -> match r with
  | Rissue -> 3 | Rtiny -> 1 | Rlsu -> 1 | Rauxw -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let mau : int array = let resmap = fun r -> match r with
  | Rissue -> 1 | Rtiny -> 1 | Rmau -> 1 |  _ -> 0
  in Array.of_list (List.map resmap resource_names)

let mau_x : int array = let resmap = fun r -> match r with
  | Rissue -> 2 | Rtiny -> 1 | Rmau -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let mau_y : int array = let resmap = fun r -> match r with
  | Rissue -> 3 | Rtiny -> 1 | Rmau -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let mau_auxr : int array = let resmap = fun r -> match r with
  | Rissue -> 1 | Rtiny -> 1 | Rmau -> 1 | Rauxr -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let mau_auxr_x : int array = let resmap = fun r -> match r with
  | Rissue -> 2 | Rtiny -> 1 | Rmau -> 1 | Rauxr -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let mau_auxr_y : int array = let resmap = fun r -> match r with
  | Rissue -> 3 | Rtiny -> 1 | Rmau -> 1 | Rauxr -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

(** Real instructions *)

exception InvalidEncoding

let rec_to_usage r =
  let encoding = match r.imm with None -> None | Some (I32 i) | Some (I64 i) -> Some (encode_imm @@ Z.to_int64 i)
                                  | Some (Off ptr) -> Some (encode_imm @@ camlint64_of_ptrofs ptr)

  in match r.inst with
  | Addw | Andw | Nandw | Orw | Norw | Sbfw | Xorw
  | Nxorw | Andnw | Ornw -> 
      (match encoding with None | Some U6 | Some S10 -> alu_tiny 
                          | Some U27L5 | Some U27L10 -> alu_tiny_x
                          | _ -> raise InvalidEncoding)
  | Sbfxw | Sbfxd ->
      (match encoding with None -> alu_lite
                          | Some U6 | Some S10 | Some U27L5 -> alu_lite_x
                          | _ -> raise InvalidEncoding)
  | Addd | Andd | Nandd | Ord | Nord | Sbfd | Xord
  | Nxord | Andnd | Ornd ->
      (match encoding with None | Some U6 | Some S10 -> alu_tiny 
                          | Some U27L5 | Some U27L10 -> alu_tiny_x
                          | Some E27U27L10 -> alu_tiny_y)
  |Cmoved ->
      (match encoding with None | Some U6 | Some S10 -> alu_lite
                          | Some U27L5 | Some U27L10 -> alu_lite_x
                          | Some E27U27L10 -> alu_lite_y)
  | Addxw -> 
      (match encoding with None | Some U6 | Some S10 -> alu_lite 
                          | Some U27L5 | Some U27L10 -> alu_lite_x
                          | _ -> raise InvalidEncoding)
  | Addxd -> 
      (match encoding with None | Some U6 | Some S10 -> alu_lite 
                          | Some U27L5 | Some U27L10 -> alu_lite_x
                          | Some E27U27L10 -> alu_lite_y)
  | Compw -> (match encoding with None -> alu_tiny
                                | Some U6 | Some S10 | Some U27L5 -> alu_tiny_x
                                | _ -> raise InvalidEncoding)
  | Compd -> (match encoding with None | Some U6 | Some S10 -> alu_tiny
                                | Some U27L5 | Some U27L10 -> alu_tiny_x
                                | Some E27U27L10 -> alu_tiny_y)
  | Fcompw -> (match encoding with None -> alu_lite
                                | Some U6 | Some S10 | Some U27L5 -> alu_lite_x
                                | _ -> raise InvalidEncoding)
  | Fcompd -> (match encoding with None -> alu_lite
                                | Some U6 | Some S10 | Some U27L5 -> alu_lite_x
                                | _ -> raise InvalidEncoding)
  | Make -> (match encoding with Some U6 | Some S10 -> alu_tiny 
                          | Some U27L5 | Some U27L10 -> alu_tiny_x 
                          | Some E27U27L10 -> alu_tiny_y 
                          | _ -> raise InvalidEncoding)
  | Maddw -> (match encoding with None -> mau_auxr
                | Some U6 | Some S10 | Some U27L5 -> mau_auxr_x
                | _ -> raise InvalidEncoding)
  | Maddd -> (match encoding with None | Some U6 | Some S10 -> mau_auxr
                | Some U27L5 | Some U27L10 -> mau_auxr_x
                | Some E27U27L10 -> mau_auxr_y)
  | Mulw| Msbfw -> (match encoding with None -> mau
                                | Some U6 | Some S10 | Some U27L5 -> mau_x
                                | _ -> raise InvalidEncoding)
  | Muld | Msbfd -> (match encoding with None | Some U6 | Some S10 -> mau
                                | Some U27L5 | Some U27L10 -> mau_x
                                | Some E27U27L10 -> mau_y)
  | Nop -> alu_nop
  | Sraw | Srlw | Sllw | Srad | Srld | Slld -> (match encoding with None | Some U6 -> alu_tiny | _ -> raise InvalidEncoding)
  (* TODO: check *)
  | Srsw | Srsd | Rorw -> (match encoding with None | Some U6 -> alu_lite | _ -> raise InvalidEncoding)
  | Extfz | Extfs | Insf -> (match encoding with None -> alu_lite | _ -> raise InvalidEncoding)
  | Fixeduwz | Fixedwz | Floatwz | Floatuwz | Fixeddz | Fixedudz | Floatdz | Floatudz -> mau
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld | Lq | Lo -> 
      (match encoding with None | Some U6 | Some S10 -> lsu_auxw
                          | Some U27L5 | Some U27L10 -> lsu_auxw_x
                          | Some E27U27L10 -> lsu_auxw_y)
  | Sb | Sh | Sw | Sd | Sq | So ->
      (match encoding with None | Some U6 | Some S10 -> lsu_auxr
                          | Some U27L5 | Some U27L10 -> lsu_auxr_x
                          | Some E27U27L10 -> lsu_auxr_y)
  | Icall | Call | Cb | Igoto | Goto | Ret | Set -> bcu
  | Get -> bcu_tiny_tiny_mau_xnop
  | Fnegd | Fnegw | Fabsd | Fabsw | Fwidenlwd
  | Fmind | Fmaxd | Fminw | Fmaxw -> alu_lite
  | Fnarrowdw -> alu_full
  | Faddd | Faddw | Fsbfd | Fsbfw | Fmuld | Fmulw | Finvw
  | Ffmad | Ffmaw | Ffmsd | Ffmsw -> mau


let inst_info_to_dlatency i = 
  begin
  assert (not (i.reads_at_id && i.reads_at_e1));
  match i.reads_at_id with
  | true -> +1
  | false -> (match i.reads_at_e1 with
              | true -> -1
              | false -> 0)
  end

let real_inst_to_latency = function
  | Nop -> 0 (* Only goes through ID *)
  | Addw | Andw | Compw | Orw | Sbfw | Sbfxw | Sraw | Srsw | Srlw | Sllw | Xorw
    (* TODO check rorw *)
  | Rorw | Nandw | Norw | Nxorw | Ornw | Andnw
  | Nandd | Nord | Nxord | Ornd | Andnd
  | Addd | Andd | Compd | Ord | Sbfd | Sbfxd | Srad | Srsd | Srld | Slld | Xord | Make
  | Extfs | Extfz | Insf | Fcompw | Fcompd | Cmoved | Addxw | Addxd
  | Fmind | Fmaxd | Fminw | Fmaxw
        -> 1
  | Floatwz | Floatuwz | Fixeduwz | Fixedwz | Floatdz | Floatudz | Fixeddz | Fixedudz -> 4
  | Mulw | Muld | Maddw | Maddd | Msbfw | Msbfd -> 2 (* FIXME - WORST CASE. If it's S10 then it's only 1 *)
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld | Lq | Lo -> 3
  | Sb | Sh | Sw | Sd | Sq | So -> 1 (* See kvx-Optimization.pdf page 19 *)
  | Get -> 1
  | Set -> 4 (* According to the manual should be 3, but I measured 4 *)
  | Icall | Call | Cb | Igoto | Goto | Ret -> 42 (* Should not matter since it's the final instruction of the basic block *)
  | Fnegd | Fnegw | Fabsd | Fabsw | Fwidenlwd | Fnarrowdw -> 1
  | Faddd | Faddw | Fsbfd | Fsbfw | Fmuld | Fmulw | Finvw
  | Ffmaw | Ffmad | Ffmsw | Ffmsd -> 4

let rec empty_inter la = function
  | [] -> true
  | b::lb -> if (List.mem b la) then false else empty_inter la lb

let rec_to_info r : inst_info =
  let usage = rec_to_usage r
  and latency = real_inst_to_latency r.inst
  and reads_at_id = not (empty_inter r.read_locs r.read_at_id)
  and reads_at_e1 = not (empty_inter r.read_locs r.read_at_e1)
  in {  write_locs = r.write_locs; read_locs = r.read_locs; usage=usage; latency=latency; is_control=r.is_control;
        reads_at_id = reads_at_id; reads_at_e1 = reads_at_e1 }

let instruction_infos bb = List.map rec_to_info (instruction_recs bb)

let instruction_usages bb =
  let usages = List.map (fun info -> info.usage) (instruction_infos bb)
  in Array.of_list usages

(**
 * Latency constraints building
 *)

(* type access = { inst: int; loc: location } *)

let preg2int pr = Camlcoq.P.to_int @@ Asmblockdeps.ppos pr

let loc2int = function
  | Mem -> 1
  | Reg pr -> preg2int pr

(* module HashedLoc = struct
  type t = { loc: location; key: int }
  let equal l1 l2 = (l1.key = l2.key)
  let hash l = l.key
  let create (l:location) : t = { loc=l; key = loc2int l }
end *)

(* module LocHash = Hashtbl.Make(HashedLoc) *)
module LocHash = Hashtbl

(* Hash table : location => list of instruction ids *)

let rec intlist n =
  if n < 0 then failwith "intlist: n < 0"
  else if n = 0 then []
  else (n-1) :: (intlist (n-1))

let find_in_hash hashloc loc =
  match LocHash.find_opt hashloc loc with
  | Some idl -> idl
  | None -> []

(* Returns a list of instruction ids *)
let rec get_accesses hashloc (ll: location list) = match ll with
  | [] -> []
  | loc :: llocs -> (find_in_hash hashloc loc) @ (get_accesses hashloc llocs)

let compute_latency (ifrom: inst_info) (ito: inst_info) =
  let dlat = inst_info_to_dlatency ito
  in let lat = ifrom.latency + dlat
  in assert (lat >= 0); if (lat == 0) then 1 else lat

let latency_constraints bb =
  let written = LocHash.create 70
  and read = LocHash.create 70
  and count = ref 0
  and constraints = ref []
  and instr_infos = instruction_infos bb
  in let step (i: inst_info) =
    let raw = get_accesses written i.read_locs
    and waw = get_accesses written i.write_locs
    and war = get_accesses read i.write_locs
    in begin
      List.iter (fun i -> constraints := {instr_from = i; instr_to = !count;
                                          latency = compute_latency (List.nth instr_infos i) (List.nth instr_infos !count)} :: !constraints) raw;
      List.iter (fun i -> constraints := {instr_from = i; instr_to = !count;
                                          latency = compute_latency (List.nth instr_infos i) (List.nth instr_infos !count)} :: !constraints) waw;
      List.iter (fun i -> constraints := {instr_from = i; instr_to = !count; latency = 0} :: !constraints) war;
      if i.is_control then List.iter (fun n -> constraints := {instr_from = n; instr_to = !count; latency = 0} :: !constraints) (intlist !count);
      (* Updating "read" and "written" hashmaps *)
      List.iter (fun loc ->
                  begin 
                    LocHash.replace written loc [!count];
                    LocHash.replace read loc []; (* Clearing all the entries of "read" hashmap when a register is written *)
                  end) i.write_locs;
      List.iter (fun loc -> LocHash.replace read loc ((!count) :: (find_in_hash read loc))) i.read_locs;
      count := !count + 1
    end
  in (List.iter step instr_infos; !constraints)

(**
 * Using the InstructionScheduler
 *)

let build_problem bb = 
  { max_latency = -1; resource_bounds = resource_bounds;
    instruction_usages = instruction_usages bb; latency_constraints = latency_constraints bb }

let rec find_min_opt (l: int option list) =
  match l with
  | [] -> None 
  | e :: l ->
    begin match find_min_opt l with
    | None -> e
    | Some m ->
      begin match e with
      | None -> Some m
      | Some n -> if n < m then Some n else Some m
      end
    end

let rec filter_indexes predicate = function
  | [] -> []
  | e :: l -> if (predicate e) then e :: (filter_indexes predicate l) else filter_indexes predicate l

let get_from_indexes indexes l = List.map (List.nth l) indexes

let is_basic = function PBasic _ -> true | _ -> false
let is_control = function PControl _ -> true | _ -> false
let to_basic = function PBasic i -> i | _ -> failwith "to_basic: control instruction found"
let to_control = function PControl i -> i | _ -> failwith "to_control: basic instruction found"

let bundlize li hd =
  let last = List.nth li (List.length li - 1)
  in if is_control last then
      let cut_li = Array.to_list @@ Array.sub (Array.of_list li) 0 (List.length li - 1)
      in let bli = List.map to_basic cut_li
      in { header = hd; body = bli; exit = Some (to_control last) }
    else 
      let bli = List.map to_basic li
      in { header = hd; body = bli; exit = None }

let apply_pbasic b = PBasic b
let extract_some o = match o with Some e -> e | None -> failwith "extract_some: None found"

let rec find_min = function
  | [] -> None
  | e :: l ->
    match find_min l with
    | None -> Some e
    | Some m -> if (e < m) then Some e else Some m

let rec remove_all m = function
  | [] -> []
  | e :: l -> if m=e then remove_all m l
                     else e :: (remove_all m l)

let rec find_mins l = match find_min l with
  | None -> []
  | Some m -> m :: find_mins (remove_all m l)

let find_all_indices m l = 
  let rec find m off = function
    | [] -> []
    | e :: l -> if m=e then off :: find m (off+1) l
                       else find m (off+1) l
  in find m 0 l

module TimeHash = Hashtbl

(* Hash table : time => list of instruction ids *)

let hashtbl2list h maxint = 
  let rec f i = match TimeHash.find_opt h i with
  | None -> if (i > maxint) then [] else (f (i+1))
  | Some bund -> bund :: (f (i+1))
  in f 0 

let find_max l =
  let rec f = function
    | [] -> None
    | e :: l -> match f l with
        | None -> Some e
        | Some m -> if (e > m) then Some e else Some m
  in match (f l) with
  | None -> raise Not_found
  | Some m -> m 

(* [0, 2, 3, 1, 1, 2, 4, 5] -> [[0], [3, 4], [1, 5], [2], [6], [7]] *)
let minpack_list (l: int list) =
  let timehash = TimeHash.create (List.length l)
  in let rec f i = function
  | [] -> ()
  | t::l -> begin
      (match TimeHash.find_opt timehash t with
      | None -> TimeHash.add timehash t [i] 
      | Some bund -> TimeHash.replace timehash t (bund @ [i]));
      f (i+1) l
    end 
  in begin
    f 0 l;
    hashtbl2list timehash (find_max l)
  end;;

(* let minpack_list l =
  let mins = find_mins l
  in List.map (fun m -> find_all_indices m l) mins
  *)

let bb_to_instrs bb = (List.map apply_pbasic bb.body) @ (match bb.exit with None -> [] | Some e -> [PControl e])

let bundlize_solution bb sol =
  let tmp = (Array.to_list @@ Array.sub sol 0 (Array.length sol - 1))
  in let packs = minpack_list tmp
  and instrs = bb_to_instrs bb
  in let rec bund hd = function
    | [] -> []
    | pack :: packs -> bundlize (get_from_indexes pack instrs) hd :: (bund [] packs)
  in bund bb.header packs

let print_inst oc = function
  | Asm.Pallocframe(sz, ofs) -> fprintf oc "	Pallocframe\n"
  | Asm.Pfreeframe(sz, ofs) -> fprintf oc "	Pfreeframe\n"
  | Asm.Pbuiltin(ef, args, res) -> fprintf oc "	Pbuiltin\n"
  | Asm.Pcvtl2w(rd, rs) -> fprintf oc "	Pcvtl2w	%a = %a\n" ireg rd ireg rs
  | i -> print_instruction oc i

let print_bb oc bb =
  let asm_instructions = Asm.unfold_bblock bb
  in List.iter (print_inst oc) asm_instructions

let do_schedule bb =
  let problem = build_problem bb
  in let solution = (if !Clflags.option_fpostpass_sched = "ilp" then
                      validated_scheduler cascaded_scheduler
                    else if !Clflags.option_fpostpass_sched = "list" then
                      validated_scheduler list_scheduler
                    else if !Clflags.option_fpostpass_sched = "revlist" then
                      validated_scheduler reverse_list_scheduler
                    else if !Clflags.option_fpostpass_sched = "greedy" then
                      greedy_scheduler else failwith ("Invalid scheduler:" ^ !Clflags.option_fpostpass_sched)) problem
  in match solution with
  | None -> failwith "Could not find a valid schedule"
  | Some sol -> let bundles = bundlize_solution bb sol in 
      (if debug then
      begin
        Printf.eprintf "Scheduling the following group of instructions:\n";
        print_bb stderr bb;
        Printf.eprintf "Gave the following solution:\n";
        List.iter (print_bb stderr) bundles;
        Printf.eprintf "--------------------------------\n"
      end;
      bundles)

(**
 * Dumb schedule if the above doesn't work
 *)

let bundlize_label l =
  match l with
  | [] -> []
  | l -> [{ header = l; body = []; exit = None }]

let rec bundlize_basic l =
  match l with
  | [] -> []
  | b :: l -> { header = []; body = [b]; exit = None } :: bundlize_basic l

let bundlize_exit e =
  match e with
  | Some e -> [{ header = []; body = []; exit = Some e }]
  | None -> []

let dumb_schedule (bb : bblock) : bblock list = bundlize_label bb.header @ bundlize_basic bb.body @ bundlize_exit bb.exit

(**
 * Separates the opaque instructions such as Pfreeframe and Pallocframe
 *)

let is_opaque = function
  | PBasic (Pallocframe _) | PBasic (Pfreeframe _) | PControl (PExpand (Pbuiltin _)) -> true
  | _ -> false

(* Returns : (accumulated instructions, remaining instructions, opaque instruction if found) *)
let rec biggest_wo_opaque = function
  | [] -> ([], [], None)
  | i :: li -> if is_opaque i then ([], li, Some i)
               else let big, rem, opaque = biggest_wo_opaque li in (i :: big, rem, opaque);;

let separate_opaque bb =
  let instrs = bb_to_instrs bb
  in let rec f hd li =
    match li with
    | [] -> []
    | li -> let big, rem, opaque = biggest_wo_opaque li in
            match opaque with
            | Some i ->
                (match big with
                | [] -> (bundlize [i] hd) :: (f [] rem)
                | big -> (bundlize big hd) :: (bundlize [i] []) :: (f [] rem)
                )
            | None -> (bundlize big hd) :: (f [] rem)
  in f bb.header instrs

let smart_schedule bb =
  let lbb = separate_opaque bb
  in let rec f = function
  | [] -> []
  | bb :: lbb -> 
      let bundles =
        try do_schedule bb
        with OpaqueInstruction -> dumb_schedule bb
        | e -> 
          let msg = Printexc.to_string e
          and stack = Printexc.get_backtrace ()
          in begin
            Printf.eprintf "In regards to this group of instructions:\n";
            print_bb stderr bb;
            Printf.eprintf "Postpass scheduling could not complete: %s\n%s" msg stack;
            failwith "Invalid schedule"
            (*
            Printf.eprintf "Issuing one instruction per bundle instead\n\n";
            dumb_schedule bb
            *)
          end
      in bundles @ (f lbb)
  in f lbb

let bblock_to_bundles bb =
  if debug then (eprintf "###############################\n"; Printf.eprintf "SCHEDULING\n"; print_bb stderr bb);
  (* print_problem (build_problem bb); *)
  if Compopts.optim_postpass () then smart_schedule bb else dumb_schedule bb

(** To deal with the Coq Axiom schedule : bblock -> (list (list basic)) * option control *)

let rec bundles_to_coq_schedule = function
  | [] -> ([], None)
  | bb :: [] -> ([bb.body], bb.exit)
  | bb :: lbb -> let (llb, oc) = bundles_to_coq_schedule lbb in (bb.body :: llb, oc)

(** Called schedule function from Coq *)

let schedule_notime bb = let toto = bundles_to_coq_schedule @@ bblock_to_bundles bb in toto
let schedule bb = Timing.time_coq ('P'::('o'::('s'::('t'::('p'::('a'::('s'::('s'::('S'::('c'::('h'::('e'::('d'::('u'::('l'::('i'::('n'::('g'::(' '::('o'::('r'::('a'::('c'::('l'::('e'::([])))))))))))))))))))))))))) schedule_notime bb
