(*
The Compcert verified compiler

Compiler.vexpand -> Compiler.v

Expand the list of RTL compiler passes into Compiler.v

David Monniaux, CNRS, VERIMAG
 *)

type is_partial = TOTAL | PARTIAL;;
type print_result = Noprint | Print of string;;
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

let post_rtl_passes =
[|
  PARTIAL, Always, (Some "Register allocation"), "Allocation", (Print "LTL");
  TOTAL, Always, (Some "Branch tunneling"), "Tunneling", Noprint;
  PARTIAL, Always, (Some "CFG linearization"), "Linearize", Noprint;
  TOTAL, Always, (Some "Label cleanup"), "CleanupLabels", Noprint;
  PARTIAL, (Option "debug"), (Some "Debugging info for local variables"), "Debugvar", Noprint;
  PARTIAL, Always, (Some "Mach generation"), "Stacking", (Print "Mach")
|];;

let all_passes =
  Array.concat
    [Array.mapi
       (fun i (a,b,c,d) -> (a,b,c,d, Print (Printf.sprintf "RTL %d" (i+1))))
       rtl_passes;
     post_rtl_passes];;

let totality = function TOTAL -> "total" | PARTIAL -> "partial";;

let print_rtl_require oc =
  Array.iter (fun (partial, trigger, time_label, pass_name, printing) ->
      Printf.fprintf oc "Require %s.\n" pass_name)
    all_passes;;

let print_rtl_require_proof oc =
  Array.iter (fun (partial, trigger, time_label, pass_name, printing) ->
      Printf.fprintf oc "Require %sproof.\n" pass_name)
    all_passes;;

let print_rtl_transf oc =
  Array.iteri
    (fun i (partial, trigger, time_label, pass_name, printing) ->
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
      (match printing with
       | Noprint -> ()
       | Print s ->
           Printf.fprintf oc "   @@ print (print_%s)\n" s)
    ) all_passes;;

let print_rtl_mkpass oc =
  Array.iter (fun (partial, trigger, time_label, pass_name, printing) ->
      output_string oc "  ::: mkpass (";
      (match trigger with
       | Always -> ()
       | Option s ->
          Printf.fprintf oc "match_if Compopts.%s " s);
      Printf.fprintf oc "%sproof.match_prog)\n" pass_name)
    all_passes;;

let print_if kind oc = function
  | Always -> ()
  | Option s -> Printf.fprintf oc "%s_if %s " kind s;;

let numbering_base = 7
                   
let print_rtl_proof oc =
  Array.iteri (fun i (partial, trigger, time_label, pass_name, printing) ->
      let j = i+numbering_base in
      match partial with
      | TOTAL ->
         Printf.fprintf oc "set (p%d := %a%s.transf_program p%d) in *.\n"
           j (print_if "total") trigger pass_name (pred j)
      | PARTIAL ->
         Printf.fprintf oc "destruct (%a%s.transf_program p%d) as [p%d|e] eqn:P%d; cbn in T; try discriminate.\n"
           (print_if "partial") trigger pass_name (pred j) j j)
    all_passes;;

let print_rtl_proof2 oc =
  Array.iteri (fun i (partial, trigger, time_label, pass_name, printing) ->
      let j = i+numbering_base in
      Printf.fprintf oc "  exists p%d; split. " j;
      (match trigger with
       | Always -> ()
       | Option _ ->
          (match partial with
           | TOTAL -> output_string oc "apply total_if_match. "
           | PARTIAL -> output_string oc "eapply partial_if_match; eauto. "));
      Printf.fprintf oc "apply %sproof.transf_program_match; auto.\n" pass_name)
    all_passes;;

let print_rtl_forward_simulations oc =
  Array.iter (fun (partial, trigger, time_label, pass_name) ->
      output_string oc "  eapply compose_forward_simulations.\n    ";
      (match trigger with
       | Always -> ()
       | Option s -> output_string oc "eapply match_if_simulation. eassumption. ");
      Printf.fprintf oc "eapply %sproof.transf_program_correct; eassumption." pass_name
    )
    rtl_passes;;

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
        | "EXPAND_RTL_MKPASS" ->
           print_rtl_mkpass oc
        | "EXPAND_RTL_PROOF" ->
           print_rtl_proof oc
        | "EXPAND_RTL_PROOF2" ->
           print_rtl_proof2 oc
        | "EXPAND_ASM_SEMANTICS" ->
           Printf.fprintf oc "    (Asm.semantics p%d)\n"
             ((Array.length all_passes) + 7)
        | "EXPAND_RTL_FORWARD_SIMULATIONS" ->
           print_rtl_forward_simulations oc
        | line -> (output_string oc line;
                   output_char oc '\n')
      done
    with End_of_file ->
      (close_in ic; close_out oc);;
