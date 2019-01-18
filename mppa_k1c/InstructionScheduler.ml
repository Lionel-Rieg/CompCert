(** Schedule instructions on a synchronized pipeline
@author David Monniaux, CNRS, VERIMAG *)

type latency_constraint = {
    instr_from : int;
    instr_to : int;
    latency : int };;

type problem = {
  max_latency : int;
  resource_bounds : int array;
  instruction_usages : int array array;
  latency_constraints : latency_constraint list;
  }

let get_nr_instructions problem = Array.length problem.instruction_usages;;
let get_nr_resources problem = Array.length problem.resource_bounds;;

type solution = int array
type scheduler = problem -> solution option

(* DISABLED				    
(** Schedule the problem optimally by constraint solving using the Gecode solver. *)
external gecode_scheduler : problem -> solution option =
  "caml_gecode_schedule_instr";;
 *)
				     
let maximum_slot_used times =
  let maxi = ref (-1) in
  for i=0 to (Array.length times)-2
  do
    maxi := max !maxi times.(i)
  done;
  !maxi;;

let check_schedule (problem : problem) (times : solution) =
  let nr_instructions = get_nr_instructions problem in
  (if Array.length times <> nr_instructions+1
   then failwith
          (Printf.sprintf "check_schedule: %d times expected, got %d"
            (nr_instructions+1) (Array.length times)));
  (if problem.max_latency >= 0 && times.(nr_instructions)> problem.max_latency
   then failwith "check_schedule: max_latency exceeded");
  (Array.iteri (fun i time ->
       (if time < 0
        then failwith (Printf.sprintf "time[%d] < 0" i))) times);
  let slot_resources = Array.init ((maximum_slot_used times)+1)
                         (fun _ -> Array.copy problem.resource_bounds) in
  for i=0 to nr_instructions -1
  do
    let remaining_resources = slot_resources.(times.(i))
    and used_resources = problem.instruction_usages.(i) in
    for resource=0 to (Array.length used_resources)-1
    do
      let after = remaining_resources.(resource) - used_resources.(resource) in
      (if after < 0
       then failwith (Printf.sprintf "check_schedule: instruction %d exceeds resource %d at slot %d" i resource times.(i)));
      remaining_resources.(resource) <- after
    done
  done;
  List.iter (fun ctr ->
      if times.(ctr.instr_to) - times.(ctr.instr_from) < ctr.latency
      then failwith (Printf.sprintf "check_schedule: time[%d]=%d - time[%d]=%d < %d"
                       ctr.instr_to times.(ctr.instr_to)
                       ctr.instr_from times.(ctr.instr_from)
                       ctr.latency)
    ) problem.latency_constraints;;

let bound_max_time problem =
  let total = ref(Array.length problem.instruction_usages) in
  List.iter (fun ctr -> total := !total + ctr.latency) problem.latency_constraints;
  !total;;

let vector_less_equal a b =
  try
    Array.iter2 (fun x y ->
        if x>y
        then raise Exit) a b;
    true
  with Exit -> false;;

let vector_subtract a b =
  assert ((Array.length a) = (Array.length b));
  for i=0 to (Array.length a)-1
  do
    b.(i) <- b.(i) - a.(i)
  done;;

(* The version with critical path ordering is much better! *)
type list_scheduler_order =
  (* | INSTRUCTION_ORDER *)
  | CRITICAL_PATH_ORDER;;

let int_max (x : int) (y : int) =
  if x > y then x else y;;

let int_min (x : int) (y : int) =
  if x < y then x else y;;

let get_predecessors problem =
  let nr_instructions = get_nr_instructions problem in
  let predecessors = Array.make (nr_instructions+1) [] in
  List.iter (fun ctr ->
      predecessors.(ctr.instr_to) <-
        (ctr.instr_from, ctr.latency)::predecessors.(ctr.instr_to))
    problem.latency_constraints;
  predecessors;;

let get_successors problem =
  let nr_instructions = get_nr_instructions problem in
  let successors = Array.make nr_instructions [] in
  List.iter (fun ctr ->
      successors.(ctr.instr_from) <-
             (ctr.instr_to, ctr.latency)::successors.(ctr.instr_from))
    problem.latency_constraints;
  successors;;

let critical_paths successors =
  let nr_instructions = Array.length successors in
  let path_lengths =  Array.make nr_instructions (-1) in
  let rec compute i =
    if i=nr_instructions then 0 else
      match path_lengths.(i) with
      | -2 -> failwith "InstructionScheduler: the dependency graph has cycles"
      | -1 -> path_lengths.(i) <- -2;
              let x = List.fold_left
                        (fun cur (j, latency)-> int_max cur (latency+(compute j)))
                        1 successors.(i)
              in path_lengths.(i) <- x; x
      | x -> x
  in for i = nr_instructions-1 downto 0
     do
       ignore (compute i)
     done;
     path_lengths;;

(* let maximum_critical_path problem =
  let paths = critical_paths (get_successors problem) in
  Array.fold_left int_max 0 paths;;
*)

let get_earliest_dates predecessors =
  let nr_instructions = (Array.length predecessors)-1 in
  let path_lengths =  Array.make (nr_instructions+1) (-1) in
  let rec compute i =
    match path_lengths.(i) with
    | -2 -> failwith "InstructionScheduler: the dependency graph has cycles"
    | -1 -> path_lengths.(i) <- -2;
            let x = List.fold_left
                      (fun cur (j, latency)-> int_max cur (latency+(compute j)))
                      0 predecessors.(i)
            in path_lengths.(i) <- x; x
    | x -> x
  in for i = 0 to nr_instructions
     do
       ignore (compute i)
     done;
     for i = 0 to nr_instructions - 1
     do
       path_lengths.(nr_instructions) <- int_max
	 path_lengths.(nr_instructions) (1 + path_lengths.(i))
     done;
     path_lengths;;

exception Unschedulable
        
let get_latest_dates deadline successors =
  let nr_instructions = Array.length successors
  and path_lengths = critical_paths successors in
  Array.init (nr_instructions + 1)
	     (fun i ->
	      if i < nr_instructions then
		let path_length = path_lengths.(i) in
		assert (path_length >= 1);
		(if path_length > deadline
                 then raise Unschedulable);
		deadline - path_length
	      else deadline);;
  
let priority_list_scheduler (order : list_scheduler_order)
      (problem : problem) :
      solution option =
  let nr_instructions = get_nr_instructions problem in
  let successors = get_successors problem
  and predecessors = get_predecessors problem
  and times = Array.make (nr_instructions+1) (-1) in

  let priorities = match order with
    (* | INSTRUCTION_ORDER -> None *)
    | CRITICAL_PATH_ORDER -> Some (critical_paths successors) in
  
  let module InstrSet =
    Set.Make (struct type t=int
                     let compare = match priorities with
                       | None -> (fun x y -> x - y)
                       | Some p -> (fun x y ->
                         (match p.(y)-p.(x) with
                          | 0 -> x - y
                          | z -> z))
              end) in

  let max_time = bound_max_time problem in
  let ready = Array.make max_time InstrSet.empty in
  Array.iteri (fun i preds ->
      if i<nr_instructions && preds=[]
      then ready.(0) <- InstrSet.add i ready.(0)) predecessors;
  
  let current_time = ref 0
  and current_resources = Array.copy problem.resource_bounds
  and earliest_time i =
    try
      let time = ref (-1) in
      List.iter (fun (j, latency) ->
          if times.(j) < 0
          then raise Exit
          else let t = times.(j) + latency in
               if t > !time
               then time := t) predecessors.(i);
      assert(!time >= 0);
      !time
    with Exit -> -1
               
  in
  let advance_time() =
    begin
      (if !current_time < max_time-1
      then
        begin
          Array.blit problem.resource_bounds 0 current_resources 0
            (Array.length current_resources);
          ready.(!current_time + 1) <-
            InstrSet.union (ready.(!current_time)) (ready.(!current_time + 1));
          ready.(!current_time) <- InstrSet.empty;
        end);
      incr current_time
    end in

  let attempt_scheduling ready usages =
    let result = ref (-1) in
    try
      InstrSet.iter (fun i ->
          (* Printf.printf "trying scheduling %d\n" i;
        pr   int_vector usages.(i);
        print           _vector current_resources; *)
          if vector_less_equal usages.(i) current_resources
          then
            begin
              vector_subtract usages.(i) current_resources;
              result := i;
              raise Exit
            end) ready;
      -1
    with Exit -> !result in
  
  while !current_time < max_time
  do
    if (InstrSet.is_empty ready.(!current_time))
     then advance_time()
    else
      match attempt_scheduling ready.(!current_time)
              problem.instruction_usages with
    | -1 -> advance_time()
    | i ->
       begin
         assert(times.(i) < 0);
         times.(i) <- !current_time;
         ready.(!current_time) <- InstrSet.remove i (ready.(!current_time));
         List.iter (fun (instr_to, latency) ->
             if instr_to < nr_instructions then
               match earliest_time instr_to with
               | -1 -> ()
               | to_time ->
                  ready.(to_time) <- InstrSet.add instr_to ready.(to_time))
           successors.(i);
         successors.(i) <- []
       end
  done;
  try
    let final_time = ref (-1) in
    for i=0 to nr_instructions-1
    do
      (if times.(i) < 0 then raise Exit);
      (if !final_time < times.(i)+1 then final_time := times.(i)+1)
    done;
    List.iter (fun (i, latency) ->
        let target_time = latency + times.(i) in
        if target_time > !final_time
        then final_time := target_time
      ) predecessors.(nr_instructions);
    times.(nr_instructions) <- !final_time;
    Some times
  with Exit -> None;;

let list_scheduler = priority_list_scheduler CRITICAL_PATH_ORDER;;

(* alternate implementation
let swap_array_elements a i j =
  let x = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- x;;

let array_reverse_slice a first last =
  let i = ref first and j = ref last in
  while i < j
  do
    swap_array_elements a !i !j;
    incr i;
    decr j
  done;;

let array_reverse a =
  let a' = Array.copy a in
  array_reverse_slice a' 0 ((Array.length a)-1);
  a';;
 *)

let array_reverse a =
  let n=Array.length a in
  Array.init n (fun i -> a.(n-1-i));;

let reverse_constraint nr_instructions ctr =
  if ctr.instr_to < nr_instructions
  then Some
    { instr_to = nr_instructions -1 -ctr.instr_from;
      instr_from =  nr_instructions -1 - ctr.instr_to;
      latency = ctr.latency }
  else None;;

let rec list_map_filter f = function
  | [] ->  []                                      
  | h::t ->
     (match f h with
      | None ->  list_map_filter f t
      | Some x -> x :: (list_map_filter f t));;

let reverse_problem problem =
  let nr_instructions = get_nr_instructions problem in
  {
    max_latency = problem.max_latency;
    resource_bounds = problem.resource_bounds;
    instruction_usages = array_reverse problem.instruction_usages;
    latency_constraints = list_map_filter (reverse_constraint nr_instructions)
                            problem.latency_constraints
  };;

let max_scheduled_time solution =
  let time = ref (-1) in
  for i = 0 to ((Array.length solution) - 2)
  do
    time := max !time solution.(i)
  done;
  !time;;

let schedule_reversed (scheduler : problem -> solution option)
    (problem : problem) =
  match scheduler (reverse_problem problem) with
  | None -> None
  | Some solution ->
     let nr_instructions = get_nr_instructions problem
     and maxi = max_scheduled_time solution in
     Some (Array.init (Array.length solution)
             (fun i ->
               if i < nr_instructions
               then maxi-solution.(nr_instructions-1-i)
               else solution.(i)));;

(** Schedule the problem using a greedy list scheduling algorithm, from the end. *)
let reverse_list_scheduler = schedule_reversed list_scheduler;;

let check_problem problem =
  (if (Array.length problem.instruction_usages) < 1
   then failwith "length(problem.instruction_usages) < 1");;

let validated_scheduler (scheduler : problem -> solution option)
      (problem : problem) =
  check_problem problem;
  match scheduler problem with
  | None -> None
  | (Some solution) as ret -> check_schedule problem solution; ret;;

let get_max_latency solution =
  solution.((Array.length solution)-1);;
  
let show_date_ranges problem =
  let deadline = problem.max_latency in
  assert(deadline >= 0);
  let successors = get_successors problem
  and predecessors = get_predecessors problem in
  let earliest_dates : int array = get_earliest_dates predecessors
  and latest_dates : int array = get_latest_dates deadline successors in
  assert ((Array.length earliest_dates) =
            (Array.length latest_dates));
  Array.iteri (fun i early ->
      let late = latest_dates.(i) in
      Printf.printf "t[%d] in %d..%d\n" i early late)
    earliest_dates;;

type pseudo_boolean_problem_type =
  | SATISFIABILITY
  | OPTIMIZATION;;

type pseudo_boolean_mapper = {
  mapper_pb_type : pseudo_boolean_problem_type;
  mapper_nr_instructions : int;
  mapper_nr_pb_variables : int;
  mapper_earliest_dates : int array;
  mapper_latest_dates : int array;
  mapper_var_offsets : int array;
  mapper_final_predecessors : (int * int) list
};;

(* Latency constraints are:
  presence of instr-to at each t <= sum of presences of instr-from at compatible times
  
  if dual_encoding
  presence of instr-from at each t <= sum of presences of instr-to at compatible times *)

(* Experiments show dual_encoding=true multiplies time by 2
   without making hard instances easier *)
let dual_encoding = false
                  
let pseudo_boolean_print_problem channel problem pb_type =
  let deadline = problem.max_latency in
  assert (deadline > 0);
  let nr_instructions = get_nr_instructions problem
  and nr_resources = get_nr_resources problem
  and successors = get_successors problem
  and predecessors = get_predecessors problem in
  let earliest_dates = get_earliest_dates predecessors
  and latest_dates = get_latest_dates deadline successors in
  let var_offsets = Array.make
                      (match pb_type with
                       | OPTIMIZATION -> nr_instructions+1
                       | SATISFIABILITY -> nr_instructions) 0 in
  let nr_pb_variables =
    (let nr = ref 0 in
     for i=0 to (match pb_type with
                 | OPTIMIZATION -> nr_instructions
                 | SATISFIABILITY -> nr_instructions-1)
     do
        var_offsets.(i) <- !nr;
        nr := !nr + latest_dates.(i) - earliest_dates.(i) + 1
     done;
     !nr)
  and nr_pb_constraints =
    (match pb_type with
     | OPTIMIZATION -> nr_instructions+1
     | SATISFIABILITY -> nr_instructions) +

    (let count = ref 0 in
     for t=0 to deadline-1
     do
       for j=0 to nr_resources-1
       do
         try
           for i=0 to nr_instructions-1
           do
             let usage = problem.instruction_usages.(i).(j) in
             if t >= earliest_dates.(i) && t <= latest_dates.(i)
                && usage > 0 then raise Exit
           done
         with Exit -> incr count
       done
     done;
     !count) +
      
     (let count=ref 0 in
      List.iter
        (fun ctr ->
          if ctr.instr_to < nr_instructions
          then count := !count + 1 + latest_dates.(ctr.instr_to)
                                   - earliest_dates.(ctr.instr_to)
                    + (if dual_encoding
                       then 1 + latest_dates.(ctr.instr_from)
                -      earliest_dates.(ctr.instr_from)
                       else 0)
        )
        problem.latency_constraints;
      !count) +
      
      (match pb_type with
       | OPTIMIZATION -> (1 + deadline - earliest_dates.(nr_instructions)) * nr_instructions
       | SATISFIABILITY -> 0)
  and measured_nr_constraints = ref 0 in

  let pb_var i t =
    assert(t >= earliest_dates.(i));
    assert(t <= latest_dates.(i));
    let v = 1+var_offsets.(i)+t-earliest_dates.(i) in
    assert(v <= nr_pb_variables);
    Printf.sprintf "x%d" v in
  
  let end_constraint () =
    begin
      output_string channel ";\n";
      incr measured_nr_constraints
    end in

  let gen_latency_constraint i_to i_from latency t_to =
    Printf.fprintf channel "* t[%d] - t[%d] >= %d when t[%d]=%d\n"
		   i_to i_from latency i_to t_to;
        for t_from=earliest_dates.(i_from) to
              int_min latest_dates.(i_from) (t_to - latency)
        do
          Printf.fprintf channel "+1 %s " (pb_var i_from t_from)
        done;
        Printf.fprintf channel "-1 %s " (pb_var i_to t_to);
        Printf.fprintf channel ">= 0";
        end_constraint()

  and gen_dual_latency_constraint i_to i_from latency t_from =
    Printf.fprintf channel "* t[%d] - t[%d] >= %d when t[%d]=%d\n"
		   i_to i_from latency i_to t_from;
        for t_to=int_max earliest_dates.(i_to) (t_from + latency)
            to latest_dates.(i_to)
        do
          Printf.fprintf channel "+1 %s " (pb_var i_to t_to)
        done;
        Printf.fprintf channel "-1 %s " (pb_var i_from t_from);
        Printf.fprintf channel ">= 0";
        end_constraint()
  in
  
  Printf.fprintf channel "* #variable= %d #constraint= %d\n" nr_pb_variables nr_pb_constraints;
  Printf.fprintf channel "* nr_instructions=%d deadline=%d\n" nr_instructions deadline;
  begin
    match pb_type with
    | SATISFIABILITY -> ()
    | OPTIMIZATION ->
       output_string channel "min:";
       for t=earliest_dates.(nr_instructions) to deadline
       do
         Printf.fprintf channel " %+d %s" t (pb_var nr_instructions t)
       done;
       output_string channel ";\n";
  end;
  for i=0 to (match pb_type with
              | OPTIMIZATION -> nr_instructions
              | SATISFIABILITY -> nr_instructions-1)
  do
    let early = earliest_dates.(i) and late= latest_dates.(i) in
    Printf.fprintf channel "* t[%d] in %d..%d\n" i early late;
    for t=early to late
    do
      Printf.fprintf channel "+1 %s " (pb_var i t)
    done;
    Printf.fprintf channel "= 1";
    end_constraint()
  done;

  for t=0 to deadline-1
  do
    for j=0 to nr_resources-1
    do
      let bound = problem.resource_bounds.(j)
      and coeffs = ref [] in
      for i=0 to nr_instructions-1
      do
        let usage = problem.instruction_usages.(i).(j) in
        if t >= earliest_dates.(i) && t <= latest_dates.(i)
           && usage > 0
        then coeffs := (i, usage) :: !coeffs 
      done;
      if !coeffs <> [] then
        begin
          Printf.fprintf channel "* resource #%d at t=%d <= %d\n" j t bound;
          List.iter (fun (i, usage) ->
              Printf.fprintf channel "%+d %s " (-usage) (pb_var i t)) !coeffs;
          Printf.fprintf channel ">= %d" (-bound);
          end_constraint();
        end
    done
  done;
  
  List.iter
    (fun ctr ->
      if ctr.instr_to < nr_instructions then
        begin
          for t_to=earliest_dates.(ctr.instr_to) to latest_dates.(ctr.instr_to)
          do
	    gen_latency_constraint ctr.instr_to ctr.instr_from ctr.latency t_to
          done;
          if dual_encoding
          then
            for t_from=earliest_dates.(ctr.instr_from) to latest_dates.(ctr.instr_from)
            do
	      gen_dual_latency_constraint ctr.instr_to ctr.instr_from ctr.latency t_from
            done
        end
    ) problem.latency_constraints;
  
  begin
    match pb_type with
    | SATISFIABILITY -> ()
    | OPTIMIZATION ->
       let final_latencies = Array.make nr_instructions 1 in
       List.iter (fun (i, latency) ->
	   final_latencies.(i) <- int_max final_latencies.(i) latency)
	 predecessors.(nr_instructions);
       for t_to=earliest_dates.(nr_instructions) to deadline
       do
         for i_from = 0 to nr_instructions -1
         do
	   gen_latency_constraint nr_instructions i_from final_latencies.(i_from) t_to
         done
       done
  end;
  assert (!measured_nr_constraints = nr_pb_constraints);
  {
    mapper_pb_type = pb_type;
    mapper_nr_instructions = nr_instructions;
    mapper_nr_pb_variables = nr_pb_variables;
    mapper_earliest_dates = earliest_dates;
    mapper_latest_dates = latest_dates;
    mapper_var_offsets = var_offsets;
    mapper_final_predecessors = predecessors.(nr_instructions)
  };;

type pb_answer =
  | Positive
  | Negative
  | Unknown
      
let line_to_pb_solution sol line nr_pb_variables =
  let assign s v =
    begin
      let i = int_of_string s in
      sol.(i-1) <- v
    end in
  List.iter
    begin
      function "" -> ()
       | item ->
    (match String.get item 0 with
     | '+' ->
        assert ((String.length item) >= 3);
        assert ((String.get item 1) = 'x');
        assign (String.sub item 2 ((String.length item)-2)) Positive
     | '-' ->
        assert ((String.length item) >= 3);
        assert ((String.get item 1) = 'x');
        assign (String.sub item 2 ((String.length item)-2)) Negative
     | 'x' ->
        assert ((String.length item) >= 2);
        assign (String.sub item 1 ((String.length item)-1)) Positive
     |  c -> failwith @@ Printf.sprintf "line_to_pb_solution: unrecognized character: %c" c
    )
    end
    (String.split_on_char ' ' (String.sub line 2 ((String.length line)-2)));;

let pb_solution_to_schedule mapper pb_solution =
  Array.mapi (fun i offset ->
	      let first = mapper.mapper_earliest_dates.(i)
	      and last = mapper.mapper_latest_dates.(i)
	      and time = ref (-1) in
	      for t=first to last
	      do
		match pb_solution.(t - first + offset) with
		| Positive ->
		   (if !time = -1
		    then time:=t
		    else failwith "duplicate time in pseudo boolean solution")
		| Negative -> ()
		| Unknown -> failwith "unknown value in pseudo boolean solution"
	      done;
	      (if !time = -1
	       then failwith "no time in pseudo boolean solution");
	      !time
	    ) mapper.mapper_var_offsets;;
  
let pseudo_boolean_read_solution mapper channel =
  let optimum = ref (-1)
  and optimum_found = ref false
  and solution = Array.make mapper.mapper_nr_pb_variables Unknown in
  try
    while true do
      match input_line channel with
      | "" -> ()
      | line ->
	 begin
	   match String.get line 0 with
	   | 'c' -> ()
	   | 'o' ->
	      assert ((String.length line) >= 2);
	      assert ((String.get line 1) = ' ');
	      optimum := int_of_string (String.sub line 2 ((String.length line)-2))
	   | 's' -> (match line with
		     | "s OPTIMUM FOUND" -> optimum_found := true
		     | "s SATISFIABLE" -> ()
		     | "s UNSATISFIABLE" -> close_in channel;
		                            raise Unschedulable
                     | _ -> failwith line)
	   | 'v' -> line_to_pb_solution solution line mapper.mapper_nr_pb_variables
	   | x -> Printf.printf "unknown: %s\n" line
	 end
    done;
    assert false
  with End_of_file ->
       close_in channel;
       begin
	 let sol = pb_solution_to_schedule mapper solution in
	 sol
       end;;

let recompute_max_latency mapper solution =
  let maxi = ref (-1) in
  for i=0 to (mapper.mapper_nr_instructions-1)
  do
    maxi := int_max !maxi (1+solution.(i))
  done;
  List.iter (fun (i, latency) ->
      maxi := int_max !maxi (solution.(i) + latency)) mapper.mapper_final_predecessors;
  !maxi;;
  
let adjust_check_solution mapper solution =
  match mapper.mapper_pb_type with
  | OPTIMIZATION ->
     let max_latency = recompute_max_latency mapper solution in
     assert (max_latency = solution.(mapper.mapper_nr_instructions));
     solution
  | SATISFIABILITY ->
     let max_latency = recompute_max_latency mapper solution in
     Array.init (mapper.mapper_nr_instructions+1)
       (fun i -> if i < mapper.mapper_nr_instructions
                 then solution.(i)
                 else max_latency);;

(* let pseudo_boolean_solver = ref "/local/monniaux/progs/naps/naps" *)
(* let pseudo_boolean_solver = ref "/local/monniaux/packages/sat4j/org.sat4j.pb.jar CuttingPlanes" *)

(* let pseudo_boolean_solver = ref "java -jar /usr/share/java/org.sat4j.pb.jar CuttingPlanes" *)
(* let pseudo_boolean_solver = ref "java -jar /usr/share/java/org.sat4j.pb.jar" *)
(* let pseudo_boolean_solver = ref "clasp" *)
(* let pseudo_boolean_solver = ref "/home/monniaux/progs/CP/open-wbo/open-wbo_static -formula=1" *)
(* let pseudo_boolean_solver = ref "/home/monniaux/progs/CP/naps/naps" *)
(* let pseudo_boolean_solver = ref "/home/monniaux/progs/CP/minisatp/build/release/bin/minisatp" *)

let pseudo_boolean_solver = ref "java -jar /opt/sat4j/sat4j-pb.jar CuttingPlanesStar"

let pseudo_boolean_scheduler pb_type problem =
  try
    let filename_in = "problem.opb" (* and filename_out = "problem.sol" *) in
    let opb_problem = open_out filename_in in
    let mapper = pseudo_boolean_print_problem opb_problem problem pb_type in
    close_out opb_problem;
    
    let opb_solution = Unix.open_process_in (!pseudo_boolean_solver ^ " " ^ filename_in) in
    let ret = adjust_check_solution mapper (pseudo_boolean_read_solution mapper opb_solution) in
    close_in opb_solution;
    Some ret
  with
  | Unschedulable -> None;;
				 
let rec reoptimizing_scheduler (scheduler : scheduler) (previous_solution : solution) (problem : problem) =
  if (get_max_latency previous_solution) > 1 then
    begin
      Printf.printf "reoptimizing < %d\n" (get_max_latency previous_solution);
      flush stdout;
      match scheduler
              { problem with max_latency = (get_max_latency previous_solution)-1 }
      with
      | None -> previous_solution
      | Some solution -> reoptimizing_scheduler scheduler solution problem
    end
  else previous_solution;;
  
let cascaded_scheduler (problem : problem) =
  match validated_scheduler list_scheduler problem with
  | None -> None
  | Some initial_solution ->
     let solution = reoptimizing_scheduler (validated_scheduler (pseudo_boolean_scheduler SATISFIABILITY)) initial_solution problem in
     begin
       let latency2 = get_max_latency solution
       and latency1 = get_max_latency initial_solution in
       if latency2 < latency1
       then Printf.printf "%d < %d\n" latency2 latency1
       else if latency2 = latency1
       then Printf.printf "%d unchanged\n" latency1
       else failwith "optimizing not optimizing"
     end;
     Some solution;;


(* old
  match validated_scheduler list_scheduler problem with
  | None -> None
  | (Some solution1) as some1 ->
     let latency1 = get_max_latency solution1 in
     begin
       match validated_scheduler pseudo_boolean_scheduler
               { problem with max_latency = latency1-1 } with
       | None ->
          Printf.printf "%d unchanged\n" latency1; 
          some1
       | (Some solution2) as some2 ->
          let latency2 = get_max_latency solution2 in
          Printf.printf "%d < %d\n" latency2 latency1;
          some2
     end;;
 *)

let smt_var i = Printf.sprintf "t%d" i

let is_resource_used problem j =
  try
    Array.iter (fun usages ->
        if usages.(j) > 0
        then raise Exit) problem.instruction_usages;
    false
  with Exit -> true;;

let smt_use_quantifiers = false
                        
let smt_print_problem channel problem =
  let nr_instructions = get_nr_instructions problem in
  let gen_smt_resource_constraint time j =
        output_string channel "(<= (+";
        Array.iteri
          (fun i usages ->
            let usage=usages.(j) in
            if usage > 0
            then Printf.fprintf channel " (ite (= %s %s) %d 0)"
                   time (smt_var i) usage)
          problem.instruction_usages;
        Printf.fprintf channel ") %d)" problem.resource_bounds.(j)
  in
  output_string channel "(set-option :produce-models true)\n"; 
  for i=0 to nr_instructions
  do
    Printf.fprintf channel "(declare-const %s Int)\n" (smt_var i);
    Printf.fprintf channel "(assert (>= %s 0))\n" (smt_var i)
  done;
  for i=0 to nr_instructions-1
  do
    Printf.fprintf channel "(assert (< %s %s))\n"
      (smt_var i) (smt_var nr_instructions)
  done;
  (if problem.max_latency > 0
   then Printf.fprintf channel "(assert (<= %s %d))\n"
          (smt_var nr_instructions) problem.max_latency);
  List.iter (fun ctr ->
      Printf.fprintf channel "(assert (>= (- %s %s) %d))\n"
        (smt_var ctr.instr_to)
        (smt_var ctr.instr_from)
        ctr.latency) problem.latency_constraints;
  for j=0 to (Array.length problem.resource_bounds)-1
  do
    if is_resource_used problem j
    then
      begin
        if smt_use_quantifiers
        then
          begin
            Printf.fprintf channel
              "; resource #%d <= %d\n(assert (forall ((t Int)) "
              j problem.resource_bounds.(j);
            gen_smt_resource_constraint "t" j;
            output_string channel "))\n"
          end
        else
          begin
            (if problem.max_latency < 0
             then failwith "quantifier explosion needs max latency");
            for t=0 to problem.max_latency
            do
              Printf.fprintf channel
                "; resource #%d <= %d at t=%d\n(assert "
                j problem.resource_bounds.(j) t;
              gen_smt_resource_constraint (string_of_int t) j;
              output_string channel ")\n"
            done
          end
      end
  done;
  output_string channel "(check-sat)(get-model)\n";;
      
