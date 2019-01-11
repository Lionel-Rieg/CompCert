open Asmblock
open Printf
open Camlcoq
open InstructionScheduler
open TargetPrinter.Target

let debug = true

(**
 * Extracting infos from Asmblock instructions
 *)

type immediate = I32 of Integers.Int.int | I64 of Integers.Int64.int | Off of offset

type ab_inst_rec = {
  inst: string; (* name of the pseudo instruction *)
  write_regs : gpreg list;
  read_regs : gpreg list;
  imm : immediate option;
}

(** Asmblock constructor to string functions *)

let arith_rrr_str = function
  | Pcompw it -> "Pcompw" ^ (icond_name it)
  | Pcompl it -> "Pcompl" ^ (icond_name it)
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

let arith_rri32_str = function
  | Pcompiw it -> "Pcompiw" ^ (icond_name it)
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
  | Pcompil it -> "Pcompil" ^ (icond_name it)
  | Paddil -> "Paddil"
  | Pandil -> "Pandil"
  | Poril -> "Poril"
  | Pxoril -> "Pxoril"

let store_str = function
  | Psb -> "Psb"
  | Psh -> "Psh"
  | Psw -> "Psw"
  | Psw_a -> "Psw_a"
  | Psd -> "Psd"
  | Psd_a -> "Psd_a"
  | Pfss -> "Pfss"
  | Pfsd -> "Pfsd"

let arith_rrr_rec i rd rs1 rs2 = { inst = arith_rrr_str i; write_regs = [rd]; read_regs = [rs1; rs2]; imm = None}

let arith_rri32_rec i rd rs imm32 = { inst = arith_rri32_str i; write_regs = [rd]; read_regs = [rs]; imm = imm32 }

let arith_rri64_rec i rd rs imm64 = { inst = arith_rri64_str i; write_regs = [rd]; read_regs = [rs]; imm = imm64 }

let arith_rec i =
  match i with
  | PArithRRI32 (i, rd, rs, imm32) -> arith_rri32_rec i rd rs (Some (I32 imm32))
  | PArithRRI64 (i, rd, rs, imm64) -> arith_rri64_rec i rd rs (Some (I64 imm64))
  | PArithRRR (i, rd, rs1, rs2) -> arith_rrr_rec i rd rs1 rs2
  | _ -> failwith "arith_rec: unrecognized constructor"

let load_rec i = failwith "load_rec: not implemented"

let store_rec i = match i with
  | PStoreRRO (i, rs1, rs2, imm) -> { inst = store_str i; write_regs = []; read_regs = [rs1; rs2]; imm = (Some (Off imm)) }

let get_rec rd rs = failwith "get_rec: not implemented"

let set_rec rd rs = failwith "set_rec: not implemented"

let basic_rec i =
  match i with
  | PArith i -> arith_rec i
  | PLoad i -> load_rec i
  | PStore i -> store_rec i
  | Pallocframe (_, _) -> failwith "basic_rec: Pallocframe"
  | Pfreeframe (_, _) -> failwith "basic_rec: Pfreeframe"
  | Pget (rd, rs) -> get_rec rd rs
  | Pset (rd, rs) -> set_rec rd rs
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
  in f i 1

let encode_imm imm =
  let i = Int64.to_int imm
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

let lsu_acc : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 1 | "TINY" -> 1 | "LSU" -> 1 | "ACC" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_acc_x : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 2 | "TINY" -> 1 | "LSU" -> 1 | "ACC" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

let lsu_acc_y : int array = let resmap = fun r -> match r with
  | "ISSUE" -> 3 | "TINY" -> 1 | "LSU" -> 1 | "ACC" -> 1 | _ -> 0
  in Array.of_list (List.map resmap resource_names)

(** Real instructions *)

type real_instruction = Addw | Addd | Sd

let real_inst_to_str = function
  | Addw -> "addw"
  | Addd -> "addd"
  | Sd -> "sd"

let ab_inst_to_real = function
  | "Paddl" | "Paddil" -> Addd
  | "Paddw" | "Paddiw" -> Addw
  | "Psd" -> Sd
  | s -> failwith @@ sprintf "ab_inst_to_real: unrecognized instruction: %s" s

let rec_to_usage r =
  let encoding = match r.imm with None -> None | Some (I32 i) | Some (I64 i) -> Some (encode_imm @@ Z.to_int64 i)
                                  | Some (Off (Ofsimm ptr)) -> Some (encode_imm @@ camlint64_of_ptrofs ptr)
                                  | Some (Off (Ofslow (_, _))) -> Some E27u27l10 (* FIXME *) 
                                  (* I do not know yet in which context Ofslow can be used by CompCert *)
  and real_inst = ab_inst_to_real r.inst
  and fail i = failwith @@ sprintf "rec_to_usage: failed with instruction %s" (real_inst_to_str i)
  in match real_inst with
  | Addw -> (match encoding with None | Some S10 -> alu_tiny | Some U27l10 -> alu_tiny_x | Some E27u27l10 -> fail real_inst)
  | Addd -> (match encoding with None | Some S10 -> alu_tiny | Some U27l10 -> alu_tiny_x | Some E27u27l10 -> alu_tiny_y)
  | Sd ->   (match encoding with None | Some S10 -> lsu_acc | Some U27l10 -> lsu_acc_x | Some E27u27l10 -> lsu_acc_y)

let real_inst_to_latency = function
  | Addw | Addd -> 1
  | Sd -> 5 (* FIXME - random value *)

let rec_to_info r : inst_info =
  let usage = rec_to_usage r
  and latency = real_inst_to_latency @@ ab_inst_to_real r.inst
  in { write_regs = r.write_regs; read_regs = r.read_regs; usage=usage; latency=latency }

let instruction_infos bb = List.map rec_to_info (instruction_recs bb)

let instruction_usages bb =
  let usages = List.map (fun info -> info.usage) (instruction_infos bb)
  in Array.of_list usages

(**
 * Latency constraints building
 *)

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
  in (List.iter step instr_infos; !constraints)

(**
 * Using the InstructionScheduler
 *)

let build_problem bb = 
  { max_latency = 5000; resource_bounds = resource_bounds;
    instruction_usages = instruction_usages bb; latency_constraints = latency_constraints bb }

let rec find_min (l: int option list) =
  match l with
  | [] -> None 
  | e :: l ->
    begin match find_min l with
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

let bundlize_solution bb sol =
  let times = ref (Array.to_list @@ Array.map (fun t -> Some t) (Array.sub sol 0 (Array.length sol - 1)))
  and is_first = ref true
  and lbb = ref []
  and instrs = (List.map apply_pbasic bb.body) @ (match bb.exit with None -> [] | Some e -> [PControl e])
  in let next_instrs = 
    let next_time = find_min !times
    in match next_time with
    | None -> []
    | Some t -> 
        let next_indexes = filter_indexes (fun e -> match e with None -> false | Some tt -> t = tt) !times
        in begin
          times := List.map (fun e -> match e with None -> None | Some tt -> if (t = tt) then None else Some tt) !times;
          get_from_indexes (List.map extract_some next_indexes) instrs
        end
  in let to_bundlize = ref [] 
  in begin 
    while (match next_instrs with [] -> false | li -> (to_bundlize := li; true)) do
      let hd = if !is_first then (is_first := false; bb.header) else []
      in lbb := !lbb @ [bundlize !to_bundlize hd]
    done;
    !lbb
  end

let print_inst oc = function
  | Asm.Pallocframe(sz, ofs) -> fprintf oc "	Pallocframe\n"
  | Asm.Pfreeframe(sz, ofs) -> fprintf oc "	Pfreeframe\n"
  | i -> print_instruction oc i

let print_bb bb =
  let asm_instructions = Asm.unfold_bblock bb
  in List.iter (print_inst stdout) asm_instructions

(* let[@warning "-26"] smart_schedule bb = print_bb bb; failwith "done" *)
let smart_schedule bb =
  ( printf "Attempting to schedule the basicblock:\n"; print_bb bb; printf "-----------------------------------\n";
  let problem = build_problem bb
  in let solution = validated_scheduler list_scheduler problem
  in match solution with
  | None -> failwith "Could not find a valid schedule"
  | Some sol -> bundlize_solution bb sol
  )

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

(** Called schedule function from Coq *)

let schedule bb = 
  ( if debug then print_bb bb;
    try smart_schedule bb
  with e ->
    let msg = Printexc.to_string e
    and stack = Printexc.get_backtrace ()
    in begin
      Printf.eprintf "Postpass scheduling could not complete: %s\n%s" msg stack;
      Printf.eprintf "Issuing one instruction per bundle instead\n\n";
      dumb_schedule bb
    end
  )
