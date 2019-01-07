open Asmblock
open Printf
open Camlcoq

(** Resource functions *)
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

(** Mapping instruction -> instruction info *)

type inst_info = {
  reservation : int array;
  write_regs : gpreg list;
  read_regs : gpreg list;
}

(* Figuring out whether an immediate is s10, u27l10 or e27u27l10 *)
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

(** Instruction usages building *)

let arith_rrr_info i rd rs1 rs2 = match i with
  | Paddl -> { reservation=alu_tiny; write_regs = [rd]; read_regs = [rs1; rs2] }
  | _ -> failwith "arith_rrr_info: unrecognized constructor"

let arith_rri32_info i rd rs imm32 = match i with
  | Paddiw -> let restbl = match encode_imm imm32 with S10 -> alu_tiny | U27l10 -> alu_tiny_x | E27u27l10 -> alu_tiny_y in
      { reservation = restbl; write_regs = [rd]; read_regs = [rs] }
  | _ -> failwith "arith_rri32_info: unrecognized constructor"

let arith_rri64_info i rd rs imm64 = match i with
  | Paddil -> let restbl = match encode_imm imm64 with S10 -> alu_tiny | U27l10 -> alu_tiny_x | E27u27l10 -> alu_tiny_y in
      { reservation = restbl; write_regs = [rd]; read_regs = [rs]}
  | _ -> failwith "arith_rri64_info: unrecognized constructor"

let arith_info i =
  match i with
  | PArithRRI32 (i, rd, rs, imm32) -> arith_rri32_info i rd rs imm32
  | PArithRRI64 (i, rd, rs, imm64) -> arith_rri64_info i rd rs imm64
  | PArithRRR (i, rd, rs1, rs2) -> arith_rrr_info i rd rs1 rs2
  | _ -> failwith "arith_info: unrecognized constructor"

let basic_info i =
  match i with
  | PArith i -> arith_info i
  | _ -> failwith "basic_info: unrecognized constructor"

let control_info i = failwith "control_info: not implemented"

let rec basic_infos body = match body with
  | [] -> []
  | bi :: body -> (basic_info bi) :: (basic_infos body)

let exit_info exit = match exit with
  | None -> []
  | Some ex -> [control_info ex]

let instruction_infos bb = (basic_infos bb.body) @ (exit_info bb.exit)

let instruction_usages bb =
  let usages = List.map (fun info -> info.reservation) (instruction_infos bb)
  in Array.of_list usages

(** Latency constraints building *)
type access = { inst: int; reg: ireg }

let rec get_accesses lregs laccs =
  let accesses reg laccs = List.filter (fun acc -> acc.reg = reg) laccs
  in match lregs with
  | [] -> []
  | reg :: lregs -> (accesses reg laccs) @ (get_accesses lregs laccs)

let latency_constraints bb = failwith "latency_constraints: not implemented"
(* TODO
  let written = ref []
  and read = ref []
  and count = ref 0
  and constraints = ref []
  in let step i = 
    let write_accesses = List.map (fun reg -> { inst= !count; reg=reg }) i.write_regs
    and read_accesses = List.map (fun reg -> { inst= !count; reg=reg }) i.read_regs
    in let raw = get_accesses !written read_accesses
    and waw = get_accesses !written write_accesses
    and war = get_accesses !read write_accesses
    in begin
      (* TODO *) failwith "latency_constraints: not implemented"
    end
  and instr_infos = instruction_infos bb
  in List.iter step instr_infos
*)

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
