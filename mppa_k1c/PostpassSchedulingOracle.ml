open Asmblock
open Printf
open Camlcoq
open InstructionScheduler

(**
 * Extracting infos from Asmblock instructions
 *)

type immediate = I32 of Integers.Int.int | I64 of Integers.Int64.int

type ab_inst_rec = {
  inst: string; (* name of the pseudo instruction *)
  write_regs : gpreg list;
  read_regs : gpreg list;
  imm : immediate option;
}

let arith_rrr_rec i rd rs1 rs2 = match i with
  | Paddl -> { inst="Paddl" ; write_regs = [rd]; read_regs = [rs1; rs2]; imm = None}
  | _ -> failwith "arith_rrr_rec: unrecognized constructor"

let arith_rri32_rec i rd rs imm32 = match i with
  | Paddiw -> 
      { inst = "Paddiw"; write_regs = [rd]; read_regs = [rs]; imm=imm32 }
  | _ -> failwith "arith_rri32_rec: unrecognized constructor"

let arith_rri64_rec i rd rs imm64 = match i with
  | Paddil ->
      { inst = "Paddil"; write_regs = [rd]; read_regs = [rs]; imm=imm64 }
  | _ -> failwith "arith_rri64_rec: unrecognized constructor"

let arith_rec i =
  match i with
  | PArithRRI32 (i, rd, rs, imm32) -> arith_rri32_rec i rd rs (Some (I32 imm32))
  | PArithRRI64 (i, rd, rs, imm64) -> arith_rri64_rec i rd rs (Some (I64 imm64))
  | PArithRRR (i, rd, rs1, rs2) -> arith_rrr_rec i rd rs1 rs2
  | _ -> failwith "arith_rec: unrecognized constructor"

let basic_rec i =
  match i with
  | PArith i -> arith_rec i
  | _ -> failwith "basic_rec: unrecognized constructor"

let control_rec i = failwith "control_rec: not implemented"

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
  write_regs : gpreg list;
  read_regs : gpreg list;
  usage: int array; (* resources consumed by the instruction *)
  latency: int;
}

(** Figuring out whether an immediate is s10, u27l10 or e27u27l10 *)
type imm_encoding = S10 | U27l10 | E27u27l10

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> let b = pow a (n/2) in
         b * b * (if n mod 2 = 0 then 1 else a)

let signed_interval n = begin 
  assert (n > 0);
  let min = - pow 2 (n-1)
  and max = pow 2 (n-1) - 1
  in (min, max)
end

let within i interv = match interv with (min, max) -> (i >= min && i <= max)

let signed_length i =
  let rec f i n = 
    let interv = signed_interval n
    in if (within i interv) then n else f i (n+1)
  in f i 0

let encode_imm imm =
  let i = Z.to_int imm
  in let length = signed_length i
  in if length <= 10 then S10
  else if length <= 37 then U27l10
  else if length <= 64 then E27u27l10
  else failwith @@ sprintf "encode_imm: integer too big! (%d)" i

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

(** Real instructions *)

type real_instruction = Addw | Addd

let real_inst_to_str = function
  | Addw -> "addw"
  | Addd -> "addd"

let ab_inst_to_real = function
  | "Paddl" | "Paddil" -> Addd
  | "Paddw" | "Paddiw" -> Addw
  | s -> failwith @@ sprintf "ab_inst_to_real: unrecognized instruction: %s" s

let rec_to_usage r =
  let encoding = match r.imm with None -> None | Some (I32 i) | Some (I64 i) -> Some (encode_imm i)
  and real_inst = ab_inst_to_real r.inst
  and fail i = failwith @@ sprintf "rec_to_usage: failed with instruction %s" (real_inst_to_str i)
  in match real_inst with
  | Addw -> (match encoding with None | Some S10 -> alu_tiny | Some U27l10 -> alu_tiny_x | Some E27u27l10 -> fail real_inst)
  | Addd -> (match encoding with None | Some S10 -> alu_tiny | Some U27l10 -> alu_tiny_x | Some E27u27l10 -> alu_tiny_y)

let real_inst_to_latency = function
  | Addw | Addd -> 1

let rec_to_info r : inst_info =
  let usage = rec_to_usage r
  and latency = real_inst_to_latency @@ ab_inst_to_real r.inst
  in { write_regs = r.write_regs; read_regs = r.read_regs; usage=usage; latency=latency }

let instruction_infos bb = List.map rec_to_info (instruction_recs bb)

let instruction_usages bb =
  let usages = List.map (fun info -> info.usage) (instruction_infos bb)
  in Array.of_list usages

(** Latency constraints building *)
type access = { inst: int; reg: ireg }

let rec get_accesses lregs laccs =
  let accesses reg laccs = List.filter (fun acc -> acc.reg = reg) laccs
  in match lregs with
  | [] -> []
  | reg :: lregs -> (accesses reg laccs) @ (get_accesses lregs laccs)

let latency_constraints bb = (* failwith "latency_constraints: not implemented" *)
  let written = ref []
  and read = ref []
  and count = ref 0
  and constraints = ref []
  in let step (i: inst_info) = 
    let write_accesses = List.map (fun reg -> { inst= !count; reg=reg }) i.write_regs
    and read_accesses = List.map (fun reg -> { inst= !count; reg=reg }) i.read_regs
    and written_regs = List.map (fun acc -> acc.reg) !written
    and read_regs = List.map (fun acc -> acc.reg) !read
    in let raw = get_accesses written_regs read_accesses
    and waw = get_accesses written_regs write_accesses
    and war = get_accesses read_regs write_accesses
    in begin
      List.iter (fun (acc: access) -> constraints := {instr_from = acc.inst; instr_to = !count; latency = i.latency} :: !constraints) (raw @ waw);
      List.iter (fun (acc: access) -> constraints := {instr_from = acc.inst; instr_to = !count; latency = 0} :: !constraints) war;
      written := write_accesses @ !written;
      read := read_accesses @ !read;
      count := !count + 1
    end
  and instr_infos = instruction_infos bb
  in List.iter step instr_infos

(** Dumb schedule if the above doesn't work *)

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

(** Called schedule function from Coq *)

let schedule bb = dumb_schedule bb (* TODO - raccorder le scheduler de David ici *)
