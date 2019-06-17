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

type ab_inst_rec = {
  inst: string; (* name of the pseudo instruction *)
  write_locs : location list;
  read_locs : location list;
  imm : immediate option;
  is_control : bool;
}

(** Asmvliw constructor to string functions *)

exception OpaqueInstruction

let arith_rr_str = function
  | Pcvtl2w -> "Pcvtl2w"
  | Pmv -> "Pmv"
  | Pnegw -> "Pnegw"
  | Pnegl -> "Pnegl"
  | Psxwd -> "Psxwd"
  | Pzxwd -> "Pzxwd"
  | Pextfz(_,_) -> "Pextfz"
  | Pextfs(_,_) -> "Pextfs"
  | Pextfzl(_,_) -> "Pextfzl"
  | Pextfsl(_,_) -> "Pextfsl"
  | Pfabsw -> "Pfabsw"
  | Pfabsd -> "Pfabsd"
  | Pfnegw -> "Pfnegw"
  | Pfnegd -> "Pfnegd"
  | Pfnarrowdw -> "Pfnarrowdw"
  | Pfwidenlwd -> "Pfwidenlwd"
  | Pfloatwrnsz -> "Pfloatwrnsz"
  | Pfloatuwrnsz -> "Pfloatuwrnsz"
  | Pfloatudrnsz -> "Pfloatudrnsz"
  | Pfloatdrnsz -> "Pfloatdrnsz"
  | Pfixedwrzz -> "Pfixedwrzz"
  | Pfixeduwrzz -> "Pfixeduwrzz"
  | Pfixeddrzz -> "Pfixeddrzz"
  | Pfixedudrzz -> "Pfixedudrzz"
  | Pfixeddrzz_i32 -> "Pfixeddrzz_i32"
  | Pfixedudrzz_i32 -> "Pfixedudrzz_i32"

let arith_rrr_str = function
  | Pcompw it -> "Pcompw"
  | Pcompl it -> "Pcompl"
  | Pfcompw ft -> "Pfcompw"
  | Pfcompl ft -> "Pfcompl"
  | Paddw -> "Paddw"
  | Paddxw _ -> "Paddxw"
  | Psubw -> "Psubw"
  | Prevsubxw _ -> "Psubxw"
  | Pmulw -> "Pmulw"
  | Pandw -> "Pandw"
  | Pnandw -> "Pnandw"
  | Porw -> "Porw"
  | Pnorw -> "Pnorw"
  | Pxorw -> "Pxorw"
  | Pnxorw -> "Pnxorw"
  | Pandnw -> "Pandnw"
  | Pornw -> "Pornw"
  | Psraw -> "Psraw"
  | Psrlw -> "Psrlw"
  | Psrxw -> "Psrxw"
  | Psllw -> "Psllw"
  | Paddl -> "Paddl"
  | Paddxl _ -> "Paddxl"
  | Psubl -> "Psubl"
  | Prevsubxl _ -> "Psubxl"
  | Pandl -> "Pandl"
  | Pnandl -> "Pnandl"
  | Porl -> "Porl"
  | Pnorl -> "Pnorl"
  | Pxorl -> "Pxorl"
  | Pnxorl -> "Pnxorl"
  | Pandnl -> "Pandnl"
  | Pornl -> "Pornl"
  | Pmull -> "Pmull"
  | Pslll -> "Pslll"
  | Psrll -> "Psrll"
  | Psrxl -> "Psrxl"
  | Psral -> "Psral"
  | Pfaddd -> "Pfaddd"
  | Pfaddw -> "Pfaddw"
  | Pfsbfd -> "Pfsbfd"
  | Pfsbfw -> "Pfsbfw"
  | Pfmuld -> "Pfmuld"
  | Pfmulw -> "Pfmulw"

let arith_rri32_str = function
  | Pcompiw it -> "Pcompiw"
  | Paddiw -> "Paddiw"
  | Paddxiw _ -> "Paddxiw"
  | Prevsubiw -> "Psubiw"
  | Prevsubxiw _ -> "Psubxiw"
  | Pmuliw -> "Pmuliw"
  | Pandiw -> "Pandiw"
  | Pnandiw -> "Pnandiw"
  | Poriw -> "Poriw"
  | Pnoriw -> "Pnoriw"
  | Pxoriw -> "Pxoriw"
  | Pnxoriw -> "Pnxoriw"
  | Pandniw -> "Pandniw"
  | Porniw -> "Porniw"
  | Psraiw -> "Psraiw"
  | Psrxiw -> "Psrxiw"
  | Psrliw -> "Psrliw"
  | Pslliw -> "Pslliw"
  | Proriw -> "Proriw"
  | Psllil -> "Psllil"
  | Psrlil -> "Psrlil"
  | Psrail -> "Psrail"
  | Psrxil -> "Psrxil"

let arith_rri64_str = function
  | Pcompil it -> "Pcompil"
  | Paddil -> "Paddil"
  | Prevsubil -> "Psubil"
  | Paddxil _ -> "Paddxil"
  | Prevsubxil _ -> "Psubxil"
  | Pmulil -> "Pmulil"
  | Pandil -> "Pandil"
  | Pnandil -> "Pnandil"
  | Poril -> "Poril"
  | Pnoril -> "Pnoril"
  | Pxoril -> "Pxoril"
  | Pnxoril -> "Pnxoril"
  | Pandnil -> "Pandnil"
  | Pornil -> "Pornil"


let arith_arr_str = function
  | Pinsf (_, _) -> "Pinsf"
  | Pinsfl (_, _) -> "Pinsfl"

let arith_arrr_str = function
  | Pmaddw -> "Pmaddw"
  | Pmaddl -> "Pmaddl"
  | Pmsubw -> "Pmsubw"
  | Pmsubl -> "Pmsubl"
  | Pcmove _ -> "Pcmove"
  | Pcmoveu _ -> "Pcmoveu"

let arith_arri32_str = function
  | Pmaddiw -> "Pmaddiw"
  | Pcmoveiw _ -> "Pcmoveiw"
  | Pcmoveuiw _ -> "Pcmoveuiw"

let arith_arri64_str = function
  | Pmaddil -> "Pmaddil"
  | Pcmoveil _ -> "Pcmoveil"
  | Pcmoveuil _ -> "Pcmoveuil"

let arith_ri32_str = "Pmake"

let arith_ri64_str = "Pmakel"

let arith_rf32_str = "Pmakefs"

let arith_rf64_str = "Pmakef"

let store_str = function
  | Psb -> "Psb"
  | Psh -> "Psh"
  | Psw -> "Psw"
  | Psw_a -> "Psw_a"
  | Psd -> "Psd"
  | Psd_a -> "Psd_a"
  | Pfss -> "Pfss"
  | Pfsd -> "Pfsd"

let load_str = function
  | Plb -> "Plb"
  | Plbu -> "Plbu"
  | Plh -> "Plh"
  | Plhu -> "Plhu"
  | Plw -> "Plw"
  | Plw_a -> "Plw_a"
  | Pld -> "Pld"
  | Pld_a -> "Pld_a"
  | Pfls -> "Pfls"
  | Pfld -> "Pfld"

let set_str = "Pset"
let get_str = "Pget"

let arith_rri32_rec i rd rs imm32 = { inst = arith_rri32_str i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = imm32; is_control = false }

let arith_rri64_rec i rd rs imm64 = { inst = arith_rri64_str i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = imm64; is_control = false }

let arith_rrr_rec i rd rs1 rs2 = { inst = arith_rrr_str i; write_locs = [Reg rd]; read_locs = [Reg rs1; Reg rs2]; imm = None; is_control = false}

let arith_arri32_rec i rd rs imm32 = { inst = arith_arri32_str i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs]; imm = imm32; is_control = false }

let arith_arri64_rec i rd rs imm64 = { inst = arith_arri64_str i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs]; imm = imm64; is_control = false }

let arith_arr_rec i rd rs = { inst = arith_arr_str i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs]; imm = None; is_control = false}

let arith_arrr_rec i rd rs1 rs2 = { inst = arith_arrr_str i; write_locs = [Reg rd]; read_locs = [Reg rd; Reg rs1; Reg rs2]; imm = None; is_control = false}

let arith_rr_rec i rd rs = { inst = arith_rr_str i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = None; is_control = false}

let arith_r_rec i rd = match i with
    (* For Ploadsymbol, writing the highest integer since we do not know how many bits does a symbol have *)
  | Ploadsymbol (id, ofs) -> { inst = "Ploadsymbol"; write_locs = [Reg rd]; read_locs = []; imm = Some (I64 Integers.Int64.max_signed); is_control = false}

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
  | PArithRI32 (rd, imm32) -> { inst = arith_ri32_str; write_locs = [Reg (IR rd)]; read_locs = []; imm = (Some (I32 imm32)) ; is_control = false}
  | PArithRI64 (rd, imm64) -> { inst = arith_ri64_str; write_locs = [Reg (IR rd)]; read_locs = []; imm = (Some (I64 imm64)) ; is_control = false}
  | PArithRF32 (rd, f) -> { inst = arith_rf32_str; write_locs = [Reg (IR rd)]; read_locs = [];
                            imm = (Some (I32 (Floats.Float32.to_bits f))); is_control = false}
  | PArithRF64 (rd, f) -> { inst = arith_rf64_str; write_locs = [Reg (IR rd)]; read_locs = [];
                            imm = (Some (I64 (Floats.Float.to_bits f))); is_control = false}
  | PArithRR (i, rd, rs) -> arith_rr_rec i (IR rd) (IR rs)
  | PArithR (i, rd) -> arith_r_rec i (IR rd)

let load_rec i = match i with
  | PLoadRRO (i, rs1, rs2, imm) ->
     { inst = load_str i; write_locs = [Reg (IR rs1)]; read_locs = [Mem; Reg (IR rs2)]; imm = (Some (Off imm)) ; is_control = false}
  | PLoadQRRO(rs, ra, imm) ->
     let (rs0, rs1) = gpreg_q_expand rs in
     { inst = "Plq"; write_locs = [Reg (IR rs0); Reg (IR rs1)]; read_locs = [Mem; Reg (IR ra)]; imm = (Some (Off imm)) ; is_control = false}
  | PLoadORRO(rs, ra, imm) ->
     let (((rs0, rs1), rs2), rs3) = gpreg_o_expand rs in
     { inst = "Plo"; write_locs = [Reg (IR rs0); Reg (IR rs1); Reg (IR rs2); Reg (IR rs3)]; read_locs = [Mem; Reg (IR ra)]; imm = (Some (Off imm)) ; is_control = false}
  | PLoadRRR (i, rs1, rs2, rs3) | PLoadRRRXS (i, rs1, rs2, rs3) ->
     { inst = load_str i; write_locs = [Reg (IR rs1)]; read_locs = [Mem; Reg (IR rs2); Reg (IR rs3)]; imm = None ; is_control = false}

let store_rec i = match i with
  | PStoreRRO (i, rs1, rs2, imm) ->
     { inst = store_str i; write_locs = [Mem]; read_locs = [Reg (IR rs1); Reg (IR rs2)]; imm = (Some (Off imm))
                                      ; is_control = false}
  | PStoreQRRO (rs, ra, imm) ->
     let (rs0, rs1) = gpreg_q_expand rs in
     { inst = "Psq"; write_locs = [Mem]; read_locs = [Reg (IR rs0); Reg (IR rs1); Reg (IR ra)]; imm = (Some (Off imm))
                                      ; is_control = false}
  | PStoreORRO (rs, ra, imm) ->
     let (((rs0, rs1), rs2), rs3) = gpreg_o_expand rs in
     { inst = "Pso"; write_locs = [Mem]; read_locs = [Reg (IR rs0); Reg (IR rs1); Reg (IR rs2); Reg (IR rs3); Reg (IR ra)]; imm = (Some (Off imm))
                                      ; is_control = false}
  | PStoreRRR (i, rs1, rs2, rs3)  | PStoreRRRXS (i, rs1, rs2, rs3) -> { inst = store_str i; write_locs = [Mem]; read_locs = [Reg (IR rs1); Reg (IR rs2); Reg (IR rs3)]; imm = None
                                      ; is_control = false}

let get_rec (rd:gpreg) rs = { inst = get_str; write_locs = [Reg (IR rd)]; read_locs = [Reg rs]; imm = None; is_control = false }

let set_rec rd (rs:gpreg) = { inst = set_str; write_locs = [Reg rd]; read_locs = [Reg (IR rs)]; imm = None; is_control = false }

let basic_rec i =
  match i with
  | PArith i -> arith_rec i
  | PLoad i -> load_rec i
  | PStore i -> store_rec i
  | Pallocframe (_, _) -> raise OpaqueInstruction
  | Pfreeframe (_, _) -> raise OpaqueInstruction
  | Pget (rd, rs) -> get_rec rd rs
  | Pset (rd, rs) -> set_rec rd rs
  | Pnop -> { inst = "nop"; write_locs = []; read_locs = []; imm = None ; is_control = false}

let expand_rec = function
  | Pbuiltin _ -> raise OpaqueInstruction

let ctl_flow_rec = function
  | Pret -> { inst = "Pret"; write_locs = []; read_locs = [Reg RA]; imm = None ; is_control = true}
  | Pcall lbl -> { inst = "Pcall"; write_locs = [Reg RA]; read_locs = []; imm = None ; is_control = true}
  | Picall r -> { inst = "Picall"; write_locs = [Reg RA]; read_locs = [Reg (IR r)]; imm = None; is_control = true}
  | Pgoto lbl -> { inst = "Pcall"; write_locs = []; read_locs = []; imm = None ; is_control = true}
  | Pigoto r -> { inst = "Pigoto"; write_locs = []; read_locs = [Reg (IR r)]; imm = None ; is_control = true}
  | Pj_l lbl -> { inst = "Pj_l"; write_locs = []; read_locs = []; imm = None ; is_control = true}
  | Pcb (bt, rs, lbl) -> { inst = "Pcb"; write_locs = []; read_locs = [Reg (IR rs)]; imm = None ; is_control = true}
  | Pcbu (bt, rs, lbl) -> { inst = "Pcbu"; write_locs = []; read_locs = [Reg (IR rs)]; imm = None ; is_control = true}
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
let resource_names = ["ISSUE"; "TINY"; "LITE"; "ALU"; "LSU"; "MAU"; "BCU"; "ACC"; "DATA"; "TCA"; "BRE"; "BRO"; "NOP"]

let rec find_index elt l =
  match l with
  | [] -> raise Not_found
  | e::l -> if (e == elt) then 0
            else 1 + find_index elt l

let resource_id resource : int = find_index resource resource_names

let resource_bound resource : int =
  match resource with
  | "ISSUE" -> 8
  | "TINY" -> 4
  | "LITE" -> 2
  | "ALU" -> 1
  | "LSU" -> 1
  | "MAU" -> 1
  | "BCU" -> 1
  | "ACC" -> 1
  | "DATA" -> 1
  | "TCA" -> 1
  | "BRE" -> 1
  | "BRO" -> 1
  | "NOP" -> 4
  | _ -> raise Not_found

let resource_bounds : int array = Array.of_list (List.map resource_bound resource_names)

(** Reservation tables *)
let alu_tiny : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 1 | "TINY" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let alu_tiny_x : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 2 | "TINY" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let alu_tiny_y : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 3 | "TINY" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let alu_lite : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 1 | "TINY" -> 1 | "LITE" -> 1 |  _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let alu_lite_x : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 2 | "TINY" -> 1 | "LITE" -> 1 |  _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let alu_lite_y : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 3 | "TINY" -> 1 | "LITE" -> 1 |  _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let alu_full : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 1 | "TINY" -> 1 | "LITE" -> 1 | "ALU" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let alu_nop : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 1 | "NOP" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let mau : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 1 | "TINY" -> 1 | "MAU" -> 1 |  _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let mau_x : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 2 | "TINY" -> 1 | "MAU" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let mau_y : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 3 | "TINY" -> 1 | "MAU" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let bcu : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 1 | "BCU" -> 1 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let bcu_tiny_tiny_mau_xnop : int array = let resmap = fun r -> match r with 
  | "ISSUE" -> 1 | "TINY" -> 2 | "MAU" -> 1 | "BCU" -> 1 | "NOP" -> 4 | _ -> 0 
  in Array.of_list (List.map resmap resource_names)

let lsu_acc : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 1 | "TINY" -> 1 | "LSU" -> 1 | "ACC" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_acc_x : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 2 | "TINY" -> 1 | "LSU" -> 1 | "ACC" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_acc_y : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 3 | "TINY" -> 1 | "LSU" -> 1 | "ACC" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_data : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 1 | "TINY" -> 1 | "LSU" -> 1 | "DATA" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_data_x : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 2 | "TINY" -> 1 | "LSU" -> 1 | "DATA" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_data_y : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 3 | "TINY" -> 1 | "LSU" -> 1 | "DATA" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

(** Real instructions *)

type real_instruction = 
  (* ALU *) 
  | Addw | Andw | Compw | Mulw | Orw | Sbfw | Sraw | Srlw | Sllw | Srsw | Rorw | Xorw
  | Addd | Andd | Compd | Muld | Ord | Sbfd | Srad | Srld | Slld | Srsd | Xord
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
  | Fnarrowdw | Fwidenlwd | Floatwz | Floatuwz | Floatdz | Floatudz | Fixedwz | Fixeduwz | Fixeddz | Fixedudz
  | Fcompw | Fcompd

let ab_inst_to_real = function
  | "Paddw" | "Paddiw" | "Pcvtl2w" -> Addw
  | "Paddxw" | "Paddxiw" -> Addxw
  | "Paddxl" | "Paddxil" -> Addxd
  | "Paddl" | "Paddil" | "Pmv" | "Pmvw2l" -> Addd
  | "Pandw" | "Pandiw" -> Andw
  | "Pnandw" | "Pnandiw" -> Nandw
  | "Pandl" | "Pandil" -> Andd
  | "Pnandl" | "Pnandil" -> Nandd
  | "Pcompw" | "Pcompiw" -> Compw
  | "Pcompl" | "Pcompil" -> Compd
  | "Pfcompw" -> Fcompw
  | "Pfcompl" -> Fcompd
  | "Pmulw" | "Pmuliw" -> Mulw
  | "Pmull" | "Pmulil" -> Muld
  | "Porw" | "Poriw" -> Orw
  | "Pnorw" | "Pnoriw" -> Norw
  | "Porl" | "Poril" -> Ord
  | "Pnorl" | "Pnoril" -> Nord
  | "Psubw" | "Pnegw" -> Sbfw
  | "Psubl" | "Pnegl" -> Sbfd
  | "Psraw" | "Psraiw" -> Sraw
  | "Psral" | "Psrail" -> Srad
  | "Psrxw" | "Psrxiw" -> Srsw
  | "Psrxl" | "Psrxil" -> Srsd
  | "Psrlw" | "Psrliw" -> Srlw
  | "Psrll" | "Psrlil" -> Srld
  | "Psllw" | "Pslliw" -> Sllw
  | "Proriw" -> Rorw
  | "Pmaddw" | "Pmaddiw" -> Maddw
  | "Pmsubw" | "Pmsubiw" -> Msbfw
  | "Pslll" | "Psllil" -> Slld
  | "Pxorw" | "Pxoriw" -> Xorw
  | "Pnxorw" | "Pnxoriw" -> Nxorw
  | "Pandnw" | "Pandniw" -> Andnw
  | "Pornw" | "Porniw" -> Ornw
  | "Pxorl" | "Pxoril" -> Xord
  | "Pnxorl" | "Pnxoril" -> Nxord
  | "Pandnl" | "Pandnil" -> Andnd
  | "Pornl" | "Pornil" -> Ornd
  | "Pmaddl" | "Pmaddil" -> Maddd
  | "Pmsubl" | "Pmsubil" -> Msbfd
  | "Pmake" | "Pmakel" | "Pmakefs" | "Pmakef" | "Ploadsymbol" -> Make
  | "Pnop" | "Pcvtw2l" -> Nop
  | "Pextfz" | "Pextfzl" | "Pzxwd" -> Extfz
  | "Pextfs" | "Pextfsl" | "Psxwd" -> Extfs
  | "Pinsf" | "Pinsfl" -> Insf
  | "Pfnarrowdw" -> Fnarrowdw
  | "Pfwidenlwd" -> Fwidenlwd
  | "Pfloatwrnsz" -> Floatwz
  | "Pfloatuwrnsz" -> Floatuwz
  | "Pfloatdrnsz" -> Floatdz
  | "Pfloatudrnsz" -> Floatudz
  | "Pfixedwrzz" -> Fixedwz
  | "Pfixeduwrzz" -> Fixeduwz
  | "Pfixeddrzz" -> Fixeddz
  | "Pfixedudrzz" -> Fixedudz
  | "Pfixeddrzz_i32" -> Fixeddz
  | "Pfixedudrzz_i32" -> Fixedudz
  | "Pcmove" | "Pcmoveu"   | "Pcmoveiw" | "Pcmoveuiw" | "Pcmoveil" | "Pcmoveuil" -> Cmoved
  
  | "Plb" -> Lbs
  | "Plbu" -> Lbz
  | "Plh" -> Lhs
  | "Plhu" -> Lhz 
  | "Plw" | "Plw_a" | "Pfls" -> Lws 
  | "Pld" | "Pfld" | "Pld_a" -> Ld
  | "Plq" -> Lq
  | "Plo" -> Lo

  | "Psb" -> Sb
  | "Psh" -> Sh 
  | "Psw" | "Psw_a" | "Pfss" -> Sw
  | "Psd" | "Psd_a" | "Pfsd" -> Sd
  | "Psq" -> Sq
  | "Pso" -> So

  | "Pcb" | "Pcbu" -> Cb
  | "Pcall" | "Pdiv" | "Pdivu" -> Call
  | "Picall" -> Icall
  | "Pgoto" | "Pj_l" -> Goto
  | "Pigoto" -> Igoto
  | "Pget" -> Get
  | "Pret" -> Ret
  | "Pset" -> Set

  | "Pfabsd" -> Fabsd
  | "Pfabsw" -> Fabsw
  | "Pfnegw" -> Fnegw
  | "Pfnegd" -> Fnegd
  | "Pfaddd" -> Faddd
  | "Pfaddw" -> Faddw
  | "Pfsbfd" -> Fsbfd
  | "Pfsbfw" -> Fsbfw
  | "Pfmuld" -> Fmuld
  | "Pfmulw" -> Fmulw

  | "nop" -> Nop
           
  | s -> failwith @@ sprintf "ab_inst_to_real: unrecognized instruction: %s" s
              
exception InvalidEncoding

let rec_to_usage r =
  let encoding = match r.imm with None -> None | Some (I32 i) | Some (I64 i) -> Some (encode_imm @@ Z.to_int64 i)
                                  | Some (Off ptr) -> Some (encode_imm @@ camlint64_of_ptrofs ptr)

  and real_inst = ab_inst_to_real r.inst
  in match real_inst with
  | Addw | Andw | Nandw | Orw | Norw | Sbfw | Xorw
  | Nxorw | Andnw | Ornw -> 
      (match encoding with None | Some U6 | Some S10 -> alu_tiny 
                          | Some U27L5 | Some U27L10 -> alu_tiny_x
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
  | Mulw| Maddw | Msbfw -> (match encoding with None -> mau
                                | Some U6 | Some S10 | Some U27L5 -> mau_x
                                | _ -> raise InvalidEncoding)
  | Muld | Maddd | Msbfd -> (match encoding with None | Some U6 | Some S10 -> mau
                                | Some U27L5 | Some U27L10 -> mau_x
                                | Some E27U27L10 -> mau_y)
  | Nop -> alu_nop
  | Sraw | Srlw | Sllw | Srad | Srld | Slld -> (match encoding with None | Some U6 -> alu_tiny | _ -> raise InvalidEncoding)
  (* TODO: check *)
  | Srsw | Srsd | Rorw -> (match encoding with None | Some U6 -> alu_lite | _ -> raise InvalidEncoding)
  | Extfz | Extfs | Insf -> (match encoding with None -> alu_lite | _ -> raise InvalidEncoding)
  | Fixeduwz | Fixedwz | Floatwz | Floatuwz | Fixeddz | Fixedudz | Floatdz | Floatudz -> mau
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld | Lq | Lo -> 
      (match encoding with None | Some U6 | Some S10 -> lsu_data 
                          | Some U27L5 | Some U27L10 -> lsu_data_x 
                          | Some E27U27L10 -> lsu_data_y)
  | Sb | Sh | Sw | Sd | Sq | So ->
      (match encoding with None | Some U6 | Some S10 -> lsu_acc 
                          | Some U27L5 | Some U27L10 -> lsu_acc_x 
                          | Some E27U27L10 -> lsu_acc_y)
  | Icall | Call | Cb | Igoto | Goto | Ret | Set -> bcu
  | Get -> bcu_tiny_tiny_mau_xnop
  | Fnegd | Fnegw | Fabsd | Fabsw | Fwidenlwd -> alu_lite
  | Fnarrowdw -> alu_full
  | Faddd | Faddw | Fsbfd | Fsbfw | Fmuld | Fmulw -> mau

let real_inst_to_latency = function
  | Nop -> 0 (* Only goes through ID *)
  | Addw | Andw | Compw | Orw | Sbfw | Sraw | Srsw | Srlw | Sllw | Xorw
    (* TODO check rorw *)
  | Rorw | Nandw | Norw | Nxorw | Ornw | Andnw
  | Nandd | Nord | Nxord | Ornd | Andnd
  | Addd | Andd | Compd | Ord | Sbfd | Srad | Srsd | Srld | Slld | Xord | Make
  | Extfs | Extfz | Insf | Fcompw | Fcompd | Cmoved | Addxw | Addxd
        -> 1
  | Floatwz | Floatuwz | Fixeduwz | Fixedwz | Floatdz | Floatudz | Fixeddz | Fixedudz -> 4
  | Mulw | Muld | Maddw | Maddd | Msbfw | Msbfd -> 2 (* FIXME - WORST CASE. If it's S10 then it's only 1 *)
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld | Lq | Lo -> 3
  | Sb | Sh | Sw | Sd | Sq | So -> 1 (* See k1c-Optimization.pdf page 19 *)
  | Get -> 1
  | Set -> 4 (* According to the manual should be 3, but I measured 4 *)
  | Icall | Call | Cb | Igoto | Goto | Ret -> 42 (* Should not matter since it's the final instruction of the basic block *)
  | Fnegd | Fnegw | Fabsd | Fabsw | Fwidenlwd | Fnarrowdw -> 1
  | Faddd | Faddw | Fsbfd | Fsbfw | Fmuld | Fmulw -> 4

let rec_to_info r : inst_info =
  let usage = rec_to_usage r
  and latency = real_inst_to_latency @@ ab_inst_to_real r.inst
  in { write_locs = r.write_locs; read_locs = r.read_locs; usage=usage; latency=latency; is_control=r.is_control }

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

module HashedLoc = struct
  type t = { loc: location; key: int }
  let equal l1 l2 = (l1.key = l2.key)
  let hash l = l.key
  let create (l:location) : t = { loc=l; key = loc2int l }
end

module LocHash = Hashtbl.Make(HashedLoc)

(* Hash table : location => list of instruction ids *)

let rec intlist n =
  if n < 0 then failwith "intlist: n < 0"
  else if n = 0 then []
  else (n-1) :: (intlist (n-1))

(* Returns a list of instruction ids *)
let rec get_accesses hashloc = function
  | [] -> []
  | loc :: llocs -> (LocHash.find hashloc loc) @ (get_accesses hashloc llocs)

let latency_constraints bb =
  let written = LocHash.create 0
  and read = LocHash.create 0
  and count = ref 0
  and constraints = ref []
  and instr_infos = instruction_infos bb
  in let step (i: inst_info) =
    let raw = get_accesses i.read_locs written
    and waw = get_accesses i.write_locs written
    and war = get_accesses i.write_locs read
    in begin
      List.iter (fun i -> constraints := {instr_from = i; instr_to = !count; latency = (List.nth instr_infos i).latency} :: !constraints) raw;
      List.iter (fun i -> constraints := {instr_from = i; instr_to = !count; latency = (List.nth instr_infos i).latency} :: !constraints) waw;
      List.iter (fun i -> constraints := {instr_from = i; instr_to = !count; latency = 0} :: !constraints) war;
      if i.is_control then List.iter (fun n -> constraints := {instr_from = n; instr_to = !count; latency = 0} :: !constraints) (intlist !count);
      (* Updating "read" and "written" hashmaps *)
      List.iter (fun loc ->
                  begin 
                    LocHash.replace written loc [!count];
                    LocHash.replace read loc []; (* Clearing all the entries of "read" hashmap when a register is written *)
                  end) i.write_locs;
      List.iter (fun loc -> LocHash.replace read loc (LocHash.find read loc)) i.read_locs;
      count := !count + 1
    end
  in (List.iter step instr_infos; !constraints)

(*
let rec list2locmap v = function
  | [] -> LocMap.empty
  | loc :: l -> LocMap.add loc v (list2locmap v l)

  let written = ref (LocHash.create 0)
  and read = ref LocMap.empty
  and count = ref 0
  and constraints = ref []
  and instr_infos = instruction_infos bb
  in let step (i: inst_info) =
    let write_accesses = list2locmap !count i.write_locs
    and read_accesses = list2locmap !count i.read_locs
    in let raw = get_accesses i.read_locs !written
    and waw = get_accesses i.write_locs !written
    and war = get_accesses i.write_locs !read
    in begin
      LocMap.iter (fun l i -> constraints := {instr_from = i; instr_to = !count; latency = (List.nth instr_infos i).latency} :: !constraints) raw;
      LocMap.iter (fun l i -> constraints := {instr_from = i; instr_to = !count; latency = (List.nth instr_infos i).latency} :: !constraints) waw;
      LocMap.iter (fun l i -> constraints := {instr_from = i; instr_to = !count; latency = 0} :: !constraints) war;
      if i.is_control then List.iter (fun n -> constraints := {instr_from = n; instr_to = !count; latency = 0} :: !constraints) (intlist !count);
      written := LocMap.union (fun _ i1 i2 -> if i1 < i2 then Some i2 else Some i1) !written write_accesses;
      read := LocMap.union (fun _ i1 i2 -> if i1 < i2 then Some i2 else Some i1) !read read_accesses;
      count := !count + 1
    end
  in (List.iter step instr_infos; !constraints)
  *)

(* let latency_constraints bb = (* failwith "latency_constraints: not implemented" *)
  let written = ref []
  and read = ref []
  and count = ref 0
  and constraints = ref []
  and instr_infos = instruction_infos bb
  in let step (i: inst_info) = 
    let write_accesses = List.map (fun loc -> { inst= !count; loc=loc }) i.write_locs
    and read_accesses = List.map (fun loc -> { inst= !count; loc=loc }) i.read_locs
    in let raw = get_accesses i.read_locs !written
    and waw = get_accesses i.write_locs !written
    and war = get_accesses i.write_locs !read
    in begin
      List.iter (fun (acc: access) -> constraints := {instr_from = acc.inst; instr_to = !count; latency = (List.nth instr_infos acc.inst).latency} :: !constraints) (raw @ waw);
      List.iter (fun (acc: access) -> constraints := {instr_from = acc.inst; instr_to = !count; latency = 0} :: !constraints) war;
      (* If it's a control instruction, add an extra 0-lat dependency between this instruction and all the previous ones *)
      if i.is_control then List.iter (fun n -> constraints := {instr_from = n; instr_to = !count; latency = 0} :: !constraints) (intlist !count);
      written := write_accesses @ !written;
      read := read_accesses @ !read;
      count := !count + 1
    end
  in (List.iter step instr_infos; !constraints)
*)

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

(* [0, 2, 3, 1, 1, 2, 4, 5] -> [[0], [3, 4], [1, 5], [2], [6], [7]] *)
let minpack_list l =
  let mins = find_mins l
  in List.map (fun m -> find_all_indices m l) mins

let bb_to_instrs bb = (List.map apply_pbasic bb.body) @ (match bb.exit with None -> [] | Some e -> [PControl e])

let bundlize_solution bb sol =
  let packs = minpack_list (Array.to_list @@ Array.sub sol 0 (Array.length sol - 1))
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

let real_do_schedule bb =
  let problem = build_problem bb
  in let solution = (if !Clflags.option_fpostpass_sched = "ilp" then
                      validated_scheduler cascaded_scheduler
                    else if !Clflags.option_fpostpass_sched = "list" then
                      validated_scheduler list_scheduler
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

let do_schedule bb =
  let nb_instructions = Camlcoq.Z.to_int64 @@ Asmvliw.size bb
  in let start_time = (Gc.major(); (Unix.times ()).Unix.tms_utime)
  in let sched = real_do_schedule bb
  in let refer = ref sched
  in begin
    for i = 1 to 100-1 do
      refer := (if i > 0 then real_do_schedule bb else real_do_schedule bb);
    done;
    Printf.printf "%Ld: %f\n" nb_instructions ((Unix.times ()).Unix.tms_utime -. start_time);
    sched
  end

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

(** Called schedule function from Coq *)

let schedule bb = 
  if debug then (eprintf "###############################\n"; Printf.eprintf "SCHEDULING\n"; print_bb stderr bb);
  (* print_problem (build_problem bb); *)
  if Compopts.optim_postpass () then smart_schedule bb else dumb_schedule bb

(** FIXME - Fix for PostpassScheduling WIP *)

type bblock' = int

let trans_block bb = 1

let bblock_equivb' bb1 bb2 = true
