open Asmblock
open Printf
open Camlcoq
open InstructionScheduler
open TargetPrinter.Target

let debug = false

(**
 * Extracting infos from Asmblock instructions
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

(** Asmblock constructor to string functions *)

exception OpaqueInstruction

let arith_rr_str = function
  | Pcvtl2w -> "Pcvtl2w"
  | Pmv -> "Pmv"
  | Pnegw -> "Pnegw"
  | Pnegl -> "Pnegl"
  | Psxwd -> "Psxwd"
  | Pzxwd -> "Pzxwd"
  | Pfabsw -> "Pfabsw"
  | Pfabsd -> "Pfabsd"
  | Pfnegw -> "Pfnegw"
  | Pfnegd -> "Pfnegd"
  | Pfnarrowdw -> "Pfnarrowdw"
  | Pfwidenlwd -> "Pfwidenlwd"
  | Pfloatwrnsz -> "Pfloatwrnsz"
  | Pfloatuwrnsz -> "Pfloatuwrnsz"
  | Pfloatudrnsz_i32 -> "Pfloatudrnsz_i32"
  | Pfloatudrnsz -> "Pfloatudrnsz"
  | Pfloatdrnsz -> "Pfloatdrnsz"
  | Pfloatdrnsz_i32 -> "Pfloatdrnsz_i32"
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
  | Psubw -> "Psubw"
  | Pmulw -> "Pmulw"
  | Pandw -> "Pandw"
  | Porw -> "Porw"
  | Pxorw -> "Pxorw"
  | Psraw -> "Psraw"
  | Psrlw -> "Psrlw"
  | Psllw -> "Psllw"
  | Paddl -> "Paddl"
  | Psubl -> "Psubl"
  | Pandl -> "Pandl"
  | Porl -> "Porl"
  | Pxorl -> "Pxorl"
  | Pmull -> "Pmull"
  | Pslll -> "Pslll"
  | Psrll -> "Psrll"
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
  | Pandiw -> "Pandiw"
  | Poriw -> "Poriw"
  | Pxoriw -> "Pxoriw"
  | Psraiw -> "Psraiw"
  | Psrliw -> "Psrliw"
  | Pslliw -> "Pslliw"
  | Psllil -> "Psllil"
  | Psrlil -> "Psrlil"
  | Psrail -> "Psrail"

let arith_rri64_str = function
  | Pcompil it -> "Pcompil"
  | Paddil -> "Paddil"
  | Pandil -> "Pandil"
  | Poril -> "Poril"
  | Pxoril -> "Pxoril"

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

let arith_rr_rec i rd rs = { inst = arith_rr_str i; write_locs = [Reg rd]; read_locs = [Reg rs]; imm = None; is_control = false}

let arith_r_rec i rd = match i with
    (* For Ploadsymbol, writing the highest integer since we do not know how many bits does a symbol have *)
  | Ploadsymbol (id, ofs) -> { inst = "Ploadsymbol"; write_locs = [Reg rd]; read_locs = []; imm = Some (I64 Integers.Int64.max_signed); is_control = false}

let arith_rec i =
  match i with
  | PArithRRI32 (i, rd, rs, imm32) -> arith_rri32_rec i (IR rd) (IR rs) (Some (I32 imm32))
  | PArithRRI64 (i, rd, rs, imm64) -> arith_rri64_rec i (IR rd) (IR rs) (Some (I64 imm64))
  | PArithRRR (i, rd, rs1, rs2) -> arith_rrr_rec i (IR rd) (IR rs1) (IR rs2)
  | PArithRI32 (rd, imm32) -> { inst = arith_ri32_str; write_locs = [Reg (IR rd)]; read_locs = []; imm = (Some (I32 imm32)) ; is_control = false}
  | PArithRI64 (rd, imm64) -> { inst = arith_ri64_str; write_locs = [Reg (IR rd)]; read_locs = []; imm = (Some (I64 imm64)) ; is_control = false}
  | PArithRF32 (rd, f) -> { inst = arith_rf32_str; write_locs = [Reg (IR rd)]; read_locs = [];
                            imm = (Some (I32 (Floats.Float32.to_bits f))); is_control = false}
  | PArithRF64 (rd, f) -> { inst = arith_rf64_str; write_locs = [Reg (IR rd)]; read_locs = [];
                            imm = (Some (I64 (Floats.Float.to_bits f))); is_control = false}
  | PArithRR (i, rd, rs) -> arith_rr_rec i (IR rd) (IR rs)
  | PArithR (i, rd) -> arith_r_rec i (IR rd)

let load_rec i = match i with
  | PLoadRRO (i, rs1, rs2, imm) -> { inst = load_str i; write_locs = [Reg (IR rs1)]; read_locs = [Mem; Reg (IR rs2)]; imm = (Some (Off imm))
                                      ; is_control = false}

let store_rec i = match i with
  | PStoreRRO (i, rs1, rs2, imm) -> { inst = store_str i; write_locs = [Mem]; read_locs = [Reg (IR rs1); Reg (IR rs2)]; imm = (Some (Off imm))
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
    else if length <= 10 then S10
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
  | Addw | Andw | Compw | Mulw | Orw | Sbfw | Sraw | Srlw | Sllw | Xorw
  | Addd | Andd | Compd | Muld | Ord | Sbfd | Srad | Srld | Slld | Xord
  | Make | Nop  | Sxwd  | Zxwd
  (* LSU *)
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld
  | Sb | Sh | Sw | Sd 
  (* BCU *)
  | Icall | Call | Cb | Igoto | Goto | Ret | Get | Set
  (* FPU *)
  | Fabsd | Fabsw | Fnegw | Fnegd
  | Faddd | Faddw | Fsbfd | Fsbfw | Fmuld | Fmulw
  | Fnarrowdw | Fwidenlwd | Floatwz | Floatuwz | Floatdz | Floatudz | Fixedwz | Fixeduwz | Fixeddz | Fixedudz
  | Fcompw | Fcompd

let ab_inst_to_real = function
  | "Paddw" | "Paddiw" | "Pcvtl2w" -> Addw
  | "Paddl" | "Paddil" | "Pmv" | "Pmvw2l" -> Addd
  | "Pandw" | "Pandiw" -> Andw
  | "Pandl" | "Pandil" -> Andd
  | "Pcompw" | "Pcompiw" -> Compw
  | "Pcompl" | "Pcompil" -> Compd
  | "Pfcompw" -> Fcompw
  | "Pfcompl" -> Fcompd
  | "Pmulw" -> Mulw
  | "Pmull" -> Muld
  | "Porw" | "Poriw" -> Orw
  | "Porl" | "Poril" -> Ord
  | "Psubw" | "Pnegw" -> Sbfw
  | "Psubl" | "Pnegl" -> Sbfd
  | "Psraw" | "Psraiw" -> Sraw
  | "Psral" | "Psrail" -> Srad
  | "Psrlw" | "Psrliw" -> Srlw
  | "Psrll" | "Psrlil" -> Srld
  | "Psllw" | "Pslliw" -> Sllw
  | "Pslll" | "Psllil" -> Slld
  | "Pxorw" | "Pxoriw" -> Xorw
  | "Pxorl" | "Pxoril" -> Xord
  | "Pmake" | "Pmakel" | "Pmakefs" | "Pmakef" | "Ploadsymbol" -> Make
  | "Pnop" | "Pcvtw2l" -> Nop
  | "Psxwd" -> Sxwd
  | "Pzxwd" -> Zxwd
  | "Pfnarrowdw" -> Fnarrowdw
  | "Pfwidenlwd" -> Fwidenlwd
  | "Pfloatwrnsz" -> Floatwz
  | "Pfloatuwrnsz" -> Floatuwz
  | "Pfloatdrnsz" -> Floatdz
  | "Pfloatdrnsz_i32" -> Floatdz
  | "Pfloatudrnsz" -> Floatudz
  | "Pfloatudrnsz_i32" -> Floatudz
  | "Pfixedwrzz" -> Fixedwz
  | "Pfixeduwrzz" -> Fixeduwz
  | "Pfixeddrzz" -> Fixeddz
  | "Pfixedudrzz" -> Fixedudz
  | "Pfixeddrzz_i32" -> Fixeddz
  | "Pfixedudrzz_i32" -> Fixedudz

  | "Plb" -> Lbs
  | "Plbu" -> Lbz
  | "Plh" -> Lhs
  | "Plhu" -> Lhz 
  | "Plw" | "Plw_a" | "Pfls" -> Lws 
  | "Pld" | "Pfld" | "Pld_a" -> Ld

  | "Psb" -> Sb
  | "Psh" -> Sh 
  | "Psw" | "Psw_a" | "Pfss" -> Sw
  | "Psd" | "Psd_a" | "Pfsd" -> Sd

  | "Pcb" | "Pcbu" -> Cb
  | "Pcall" -> Call
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
  | s -> failwith @@ sprintf "ab_inst_to_real: unrecognized instruction: %s" s

exception InvalidEncoding

let rec_to_usage r =
  let encoding = match r.imm with None -> None | Some (I32 i) | Some (I64 i) -> Some (encode_imm @@ Z.to_int64 i)
                                  | Some (Off (Ofsimm ptr)) -> Some (encode_imm @@ camlint64_of_ptrofs ptr)
                                  | Some (Off (Ofslow (_, _))) -> Some E27U27L10 (* FIXME *) 
                                  (* I do not know yet in which context Ofslow can be used by CompCert *)
  and real_inst = ab_inst_to_real r.inst
  in match real_inst with
  | Addw | Andw | Orw | Sbfw | Xorw -> 
      (match encoding with None | Some U6 | Some S10 -> alu_tiny 
                          | Some U27L5 | Some U27L10 -> alu_tiny_x
                          | _ -> raise InvalidEncoding)
  | Addd | Andd | Ord | Sbfd | Xord -> 
      (match encoding with None | Some U6 | Some S10 -> alu_tiny 
                          | Some U27L5 | Some U27L10 -> alu_tiny_x
                          | Some E27U27L10 -> alu_tiny_y)
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
  | Mulw -> (match encoding with None -> mau
                                | Some U6 | Some S10 | Some U27L5 -> mau_x
                                | _ -> raise InvalidEncoding)
  | Muld -> (match encoding with None | Some U6 | Some S10 -> mau
                                | Some U27L5 | Some U27L10 -> mau_x
                                | Some E27U27L10 -> mau_y)
  | Nop -> alu_nop
  | Sraw | Srlw | Sllw | Srad | Srld | Slld -> (match encoding with None | Some U6 -> alu_tiny | _ -> raise InvalidEncoding)
  | Sxwd | Zxwd -> (match encoding with None -> alu_lite | _ -> raise InvalidEncoding)
  | Fixeduwz | Fixedwz | Floatwz | Floatuwz | Fixeddz | Fixedudz | Floatdz | Floatudz -> mau
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld -> 
      (match encoding with None | Some U6 | Some S10 -> lsu_data 
                          | Some U27L5 | Some U27L10 -> lsu_data_x 
                          | Some E27U27L10 -> lsu_data_y)
  | Sb | Sh | Sw | Sd ->
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
  | Addw | Andw | Compw | Orw | Sbfw | Sraw | Srlw | Sllw | Xorw
  | Addd | Andd | Compd | Ord | Sbfd | Srad | Srld | Slld | Xord | Make
  | Sxwd | Zxwd | Fcompw | Fcompd
        -> 1
  | Floatwz | Floatuwz | Fixeduwz | Fixedwz | Floatdz | Floatudz | Fixeddz | Fixedudz -> 4
  | Mulw | Muld -> 2 (* FIXME - WORST CASE. If it's S10 then it's only 1 *)
  | Lbs | Lbz | Lhs | Lhz | Lws | Ld
  | Sb | Sh | Sw | Sd 
        -> 3 (* FIXME - random value *)
  | Get -> 1
  | Set -> 3
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

type access = { inst: int; loc: location }

let rec get_accesses llocs laccs =
  let accesses loc laccs = List.filter (fun acc -> acc.loc = loc) laccs
  in match llocs with
  | [] -> []
  | loc :: llocs -> (accesses loc laccs) @ (get_accesses llocs laccs)

let rec intlist n =
  if n < 0 then failwith "intlist: n < 0"
  else if n = 0 then []
  else (n-1) :: (intlist (n-1))

let latency_constraints bb = (* failwith "latency_constraints: not implemented" *)
  let written = ref []
  and read = ref []
  and count = ref 0
  and constraints = ref []
  in let step (i: inst_info) = 
    let write_accesses = List.map (fun loc -> { inst= !count; loc=loc }) i.write_locs
    and read_accesses = List.map (fun loc -> { inst= !count; loc=loc }) i.read_locs
    in let raw = get_accesses i.read_locs !written
    and waw = get_accesses i.write_locs !written
    and war = get_accesses i.write_locs !read
    in begin
      List.iter (fun (acc: access) -> constraints := {instr_from = acc.inst; instr_to = !count; latency = i.latency} :: !constraints) (raw @ waw);
      List.iter (fun (acc: access) -> constraints := {instr_from = acc.inst; instr_to = !count; latency = 0} :: !constraints) war;
      (* If it's a control instruction, add an extra 0-lat dependency between this instruction and all the previous ones *)
      if i.is_control then List.iter (fun n -> constraints := {instr_from = n; instr_to = !count; latency = 0} :: !constraints) (intlist !count);
      written := write_accesses @ !written;
      read := read_accesses @ !read;
      count := !count + 1
    end
  and instr_infos = instruction_infos bb
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

let do_schedule bb =
  let scheduler = match Compopts.optim_pp_optimizer () with 1 -> list_scheduler | _ -> failwith "No scheduler provided"
  in let problem = build_problem bb
  in let solution = validated_scheduler scheduler problem
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

let rec biggest_wo_opaque = function
  | [] -> ([], [])
  | [i] -> ([i], [])
  | i1 :: i2 :: li -> if is_opaque i2 || is_opaque i1 then ([i1], i2::li) 
                     else let big, rem = biggest_wo_opaque li in (i1 :: i2 :: big, rem)

let separate_opaque bb =
  let instrs = bb_to_instrs bb
  in let rec f hd = function
  | [] -> []
  | li ->
    let sub_li, li = biggest_wo_opaque li
    in (bundlize sub_li hd) :: (f [] li)
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
            Printf.eprintf "Issuing one instruction per bundle instead\n\n";
            dumb_schedule bb
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
