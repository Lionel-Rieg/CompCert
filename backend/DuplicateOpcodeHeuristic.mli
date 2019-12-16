(** Define opcode heuristics used for the instruction duplication oracle
 * In particular, it is used to figure out which "branch" should be privileged
 * when selecting a trace.
 *)

exception HeuristicSucceeded

(* The bool reference should be updated to [true] if the condition is supposed
 * to hold, [false] if it is supposed to not hold
 * The function should raise HeuristicSucceeded if it succeeded to predict a branch,
 * and do nothing otherwise *)
val opcode_heuristic : RTL.code -> Op.condition -> RTL.node -> RTL.node -> bool ref -> unit
