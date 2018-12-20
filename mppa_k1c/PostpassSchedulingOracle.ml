open Asmblock

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

let encode_imm : imm_encoding = raise Not_found (* TODO *)

let arith_rrr_info i rd rs1 rs2 = match i with
  | Paddl -> { reservation=alu_tiny; write_regs = [rd]; read_regs = [rs1; rs2] }
  | _ -> raise Not_found

let arith_rri32_info i rd rs imm32 = match i with
  | Paddiw -> let restbl = match encode_imm imm with S10 -> alu_tiny | U27l10 -> alu_tiny_x | E27u27l10 -> alu_tiny_y in
      { reservation = restbl; write_regs = [rd]; read_regs = [rs] }
  | _ -> raise Not_found

let arith_rri64_info i rd rs imm64 = match i with
  | Paddil -> let restbl = match encode_imm imm with S10 -> alu_tiny | U27l10 -> alu_tiny_x | E27u27l10 -> alu_tiny_y in
      { reservation = restbl; write_regs = [rd]; read_regs = [rs]}
  | _ -> raise Not_found

let arith_info i =
  match i with
  | PArithRRI32 i rd rs imm -> arith_rri32_info i rd rs imm32
  | PArithRRI64 i rd rs imm64 -> arith_rri64_info i rd rs imm64
  | PArithRRR i rd rs1 rs2 -> arith_rrr_info i r0 r1 r2
  | _ -> raise Not_found

let basic_info i =
  match i with
  | PArith i -> arith_info i
  | _ -> raise Not_found

let exit_info i = raise Not_found

(** Instruction usages building *)
let rec basic_usages body = match body with
  | [] -> []
  | bi :: body -> (basic_info bi).reservation :: (basic_usages body)

let exit_usage exit = match exit with
  | None -> []
  | Some ex -> [(control_info ex).reservation]

let instruction_usages bb = Array.of_list ((basic_usages bb.body) @ (exit_usage bb.exit))

(** Latency constraints building *)
let latency_constraints bb = (* TODO *)

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
