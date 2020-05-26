open Printf
open Asmblock
open Integers
open PostpassSchedulingOracle
open BinNums

let test_schedule_sd =
  let sd_inst = PStore (PStoreRRO (Psd, GPR12, GPR16, (Ofsimm (Ptrofs.of_int @@ Int.intval Z0))))
  in let bb = { header = []; body = [sd_inst]; exit = None }
  in List.iter print_bb (smart_schedule bb)

let _ = test_schedule_sd; printf "Done\n"
