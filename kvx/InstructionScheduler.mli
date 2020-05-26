(** Schedule instructions on a synchronized pipeline
by David Monniaux, CNRS, VERIMAG *)

(** A latency constraint: instruction number [instr_to] should be scheduled at least [latency] clock ticks before [instr_from].

It is possible to specify [latency]=0, meaning that [instr_to] can be scheduled at the same clock tick as [instr_from], but not before.

[instr_to] can be the special value equal to the number of instructions, meaning that it refers to the final output latency. *)
type latency_constraint = {
  instr_from : int;
  instr_to : int;
  latency : int;
  }
                        
(** A scheduling problem.

In addition to the latency constraints, the resource constraints should be satisfied: at every clock tick, the sum of vectors of resources used by the instructions scheduled at that tick does not exceed the resource bounds.
*)
type problem = {
    max_latency : int;
    (** An optional maximal total latency of the problem, after which the problem is deemed not schedulable. -1 means there should be no maximum. *)

    resource_bounds : int array;
    (** An array of number of units available indexed by the kind of resources to be allocated. It can be empty, in which case the problem is scheduling without resource constraints. *)

    instruction_usages: int array array;
    (** At index {i i} the vector of resources used by instruction number {i i}. It must be the same length as [resource_bounds] *)

    latency_constraints : latency_constraint list
    (** The latency constraints that must be satisfied *)
  };;

(** Print problem for human readability. *)
val print_problem : out_channel -> problem -> unit;;

(** Scheduling solution. For {i n} instructions to schedule, and 0≤{i i}<{i n}, position {i i} contains the time to which instruction {i i} should be scheduled. Position {i n} contains the final output latency. *)
type solution = int array
              
(** A scheduling algorithm.
The return value [Some x] is a solution [x].
[None] means that scheduling failed. *)
type scheduler = problem -> solution option;;

(* DISABLED
(** Schedule the problem optimally by constraint solving using the Gecode solver. *)
external gecode_scheduler : problem -> solution option
  = "caml_gecode_schedule_instr"
 *)
  
(** Get the number the last scheduling time used for an instruction in a solution.
@return The last clock tick used *)
val maximum_slot_used : solution -> int

(** Validate that a solution is truly a solution of a scheduling problem.
@raise Failure if validation fails *)
val check_schedule : problem -> solution -> unit

(** Schedule the problem using a greedy list scheduling algorithm, from the start.
The first (according to instruction ordering) instruction that is ready (according to the latency constraints) is scheduled at the current clock tick.
Once a clock tick is full go to the next.

@return [Some solution] when a solution is found, [None] if not. *)
val list_scheduler : problem -> solution option

(** Schedule the problem using the order of instructions without any reordering *)
val greedy_scheduler : problem -> solution option

(** Schedule a problem using a scheduler applied in the opposite direction, e.g. for list scheduling from the end instead of the start. BUGGY *)
val schedule_reversed : scheduler -> problem -> int array option

(** Schedule a problem from the end using a list scheduler. BUGGY *)
val reverse_list_scheduler : problem -> int array option

(** Check that a problem is well-formed.
@raise Failure if validation fails *)
val check_problem : problem -> unit
  
(** Apply a scheduler and validate the result against the input problem.
@return The solution found
@raise Failure if validation fails *)
val validated_scheduler : scheduler -> problem -> solution option;;

(** Get max latency from solution
@return Max latency *)
val get_max_latency : solution -> int;;

(** Get the length of a maximal critical path
@return Max length *)
val maximum_critical_path : problem -> int;;

(** Apply line scheduler then advanced solver
@return A solution if found *)
val cascaded_scheduler : problem -> solution option;;

val show_date_ranges : problem -> unit;;

type pseudo_boolean_problem_type =
  | SATISFIABILITY
  | OPTIMIZATION;;

type pseudo_boolean_mapper
val pseudo_boolean_print_problem : out_channel -> problem -> pseudo_boolean_problem_type -> pseudo_boolean_mapper;;
val pseudo_boolean_read_solution : pseudo_boolean_mapper -> in_channel -> solution;;
val pseudo_boolean_scheduler : pseudo_boolean_problem_type -> problem -> solution option;;

val smt_print_problem : out_channel -> problem -> unit;;

val ilp_print_problem : out_channel -> problem -> pseudo_boolean_problem_type -> pseudo_boolean_mapper;;

val ilp_scheduler : pseudo_boolean_problem_type -> problem -> solution option;;
