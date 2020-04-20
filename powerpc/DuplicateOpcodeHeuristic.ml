(* open Camlcoq *)
open Op
open Integers

let opcode_heuristic code cond ifso ifnot is_loop_header =
  match cond with
  | Ccompimm (c, n) | Ccompuimm (c, n) -> if n == Integers.Int.zero then (match c with
      | Clt | Cle -> Some false
      | Cgt | Cge -> Some true
      | _ -> None
      ) else None
  | Ccomplimm (c, n) | Ccompluimm (c, n) -> if n == Integers.Int64.zero then (match c with
      | Clt | Cle -> Some false
      | Cgt | Cge -> Some true
      | _ -> None
      ) else None
  | Ccompf c -> (match c with
      | Ceq -> Some false
      | Cne -> Some true
      | _ -> None
      )
  | Cnotcompf c -> (match c with
      | Ceq -> Some true
      | Cne -> Some false
      | _ -> None
      )
  | _ -> None
