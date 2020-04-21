type is_partial = TOTAL | PARTIAL;;
type when_triggered = Always | Option of string;;

let rtl_passes =
[|
TOTAL, (Option "optim_tailcalls"), (Some "Tail calls"), "Tailcall";
PARTIAL, Always, (Some "Inlining"), "Inlining";
TOTAL, (Option "profile_arcs"), (Some "Profiling insertion"), "Profiling";
TOTAL, (Option "branch_probabilities"), (Some "Profiling use"), "ProfilingExploit";
TOTAL, (Option "optim_move_loop_invariants"), (Some "Inserting initial nop"), "FirstNop";
TOTAL, Always, (Some "Renumbering"), "Renumber";
PARTIAL, (Option "optim_duplicate"),  (Some "Tail-duplicating"), "Duplicate";
TOTAL, Always, (Some "Renumbering pre constprop"), "Renumber";
TOTAL, (Option "optim_constprop"), (Some "Constant propagation"), "Constprop";
PARTIAL, (Option "optim_move_loop_invariants"), (Some "LICM"), "LICM";
TOTAL, (Option "optim_move_loop_invariants"), (Some "Renumbering pre CSE"), "Renumber";
PARTIAL, (Option "optim_CSE"), (Some "CSE"), "CSE";
TOTAL, (Option "optim_CSE2"), (Some "CSE2"), "CSE2";
PARTIAL, (Option "optim_CSE3"), (Some "CSE3"), "CSE3";
TOTAL, (Option "optim_forward_moves"), (Some "Forwarding moves"), "ForwardMoves";
PARTIAL, (Option "optim_redundancy"), (Some "Redundancy elimination"), "Deadcode";
TOTAL, (Option "all_loads_nontrap"), None, "Allnontrap";
PARTIAL, Always, (Some "Unused globals"), "Unusedglob"
|];;

let totality = function TOTAL -> "total" | PARTIAL -> "partial";;

let print_rtl_require oc =
  Array.iter (fun (partial, trigger, time_label, pass_name) ->
      Printf.fprintf oc "Require %s.\n" pass_name)
    rtl_passes;;

let print_rtl_require_proof oc =
  Array.iter (fun (partial, trigger, time_label, pass_name) ->
      Printf.fprintf oc "Require %sproof.\n" pass_name)
    rtl_passes;;

let print_rtl_transf oc =
  Array.iteri
    (fun i (partial, trigger, time_label, pass_name) ->
      output_string oc (match partial with
                        | TOTAL -> "   @@ "
                        | PARTIAL -> "  @@@ ");
      (match trigger with
       | Always -> ()
       | Option s ->
          Printf.fprintf oc "%s_if Compopts.%s " (totality partial) s);
      output_char oc '(';
      (match time_label with
       | None -> ()
       | Some s ->
          Printf.fprintf oc "time \"%s\" " s);
      Printf.fprintf oc "%s.transf_program)\n" pass_name;
      Printf.fprintf oc "   @@ print (print_RTL %d)\n" (succ i)
    ) rtl_passes;;
    
if (Array.length Sys.argv)<>3
then exit 1;;

let filename_in = Sys.argv.(1) and filename_out = Sys.argv.(2) in
    let ic = open_in filename_in and oc = open_out filename_out in
    try
      while true
      do
        match input_line ic with
        | "EXPAND_RTL_TRANSF_PROGRAM" ->
           print_rtl_transf oc
        | "EXPAND_RTL_REQUIRE" ->
           print_rtl_require oc
        | "EXPAND_RTL_REQUIRE_PROOF" ->
           print_rtl_require_proof oc
        | line -> (output_string oc line;
                   output_char oc '\n')
      done
    with End_of_file ->
      (close_in ic; close_out oc);;
