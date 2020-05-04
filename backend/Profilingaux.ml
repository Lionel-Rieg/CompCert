(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*                                                             *)
(*  Copyright VERIMAG. All rights reserved.                    *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

open Camlcoq
open RTL
open Maps
   
type identifier = Digest.t

let pp_id channel (x : identifier) =
  assert(String.length x = 16);
  for i=0 to 15 do
    Printf.fprintf channel "%02x" (Char.code (String.get x i))
  done

let print_anonymous_function pp f =
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.fn_code)) in
  PrintRTL.print_succ pp f.fn_entrypoint
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (PrintRTL.print_instruction pp) instrs;
  Printf.fprintf pp "}\n\n"
  
let function_id (f : coq_function) : identifier =
  let digest = Digest.string (Marshal.to_string f []) in
  (*
  Printf.fprintf stderr "FUNCTION hash = %a\n" pp_id digest;
  print_anonymous_function stderr f;
   *)
  digest

let branch_id (f_id : identifier) (node : P.t) : identifier =
  Digest.string (f_id ^ (Int64.to_string (P.to_int64 node)));;

let profiling_counts : (identifier, (Int64.t*Int64.t)) Hashtbl.t = Hashtbl.create 1000;;

let get_counts id =
  match Hashtbl.find_opt profiling_counts id with
  | Some x -> x
  | None -> (0L, 0L);;
  
let add_profiling_counts id counter0 counter1 =
  let (old0, old1) = get_counts id in
    Hashtbl.replace profiling_counts id (Int64.add old0 counter0,
                                         Int64.add old1 counter1);;

let input_counter (ic : in_channel) : Int64.t =
  let r = ref Int64.zero in
  for i=0 to 7
  do
    r := Int64.add !r (Int64.shift_left (Int64.of_int (input_byte ic)) (8*i))
  done;
  !r;;
  
let load_profiling_info (filename : string) : unit =
  let ic = open_in filename in
  try
    while true do
      let id : identifier = really_input_string ic 16 in
      let counter0 = input_counter ic in
      let counter1 = input_counter ic in
      (* Printf.fprintf stderr "%a : %Ld %Ld\n" pp_id id counter0 counter1 *)
      add_profiling_counts id counter0 counter1
    done
  with End_of_file -> close_in ic;;

let condition_oracle (id : identifier) : bool option =
  let (count0, count1) = get_counts id in
  (* (if count0 <> 0L || count1 <> 0L then
    Printf.fprintf stderr "%a : %Ld %Ld\n" pp_id id count0 count1); *)
  if count0 = count1 then None
  else Some(count1 > count0);;
