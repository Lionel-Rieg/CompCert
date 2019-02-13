(** Specification of the example illustrating how to use ImpDep. *)

Require Export ZArith.

Require Export ZArith.
Require Export List.
Export ListNotations.

(* Syntax *)

Definition reg := positive.

Inductive operand :=
  | Imm (i:Z)
  | Reg (r:reg)
  .

Inductive arith_op := ADD | SUB | MUL.

Inductive inst :=
  | MOVE (dest: reg) (src: operand)
  | ARITH (dest: reg) (op: arith_op) (src1 src2: operand)
  | LOAD (dest base: reg) (offset: operand)
  | STORE (src base: reg) (offset: operand)
  | MEMSWAP (r base: reg) (offset: operand)
  .

Definition bblock := list inst.

(* Semantics *)

Definition value := Z.

Definition addr := positive.

Definition mem := addr -> value.

Definition assign (m: mem) (x:addr) (v: value) :=
 fun y => if Pos.eq_dec x y then v else (m y).

Definition regmem := reg -> value.

Record state := { sm: mem; rm: regmem }.

Definition operand_eval (x: operand) (rm: regmem): value :=
  match x with
  | Imm i => i
  | Reg r => rm r
  end.

Definition arith_op_eval (o: arith_op): value -> value -> value :=
  match o with
  | ADD => Z.add
  | SUB => Z.sub
  | MUL => Z.mul
  end.

Definition get_addr (base:reg) (offset:operand) (rm: regmem): option addr :=
  let b := rm base in
  let ofs := operand_eval offset rm in
  match Z.add b ofs with
  | Zpos p => Some p
  | _ => None
  end.

(* two-state semantics -- dissociating read from write access.
   - all read access on [sin] state
   - all register write access modifies [sout] state
   - all memory write access modifies [sin] state
   => useful for parallel semantics
   NB: in this parallel semantics -- there is at most one STORE by bundle
   which is non-deterministically chosen...
*)
Definition sem_inst (i: inst) (sin sout: state): option state :=
  match i with
  | MOVE dest src =>
      let v := operand_eval src (rm sin) in
      Some {| sm := sm sout;
              rm := assign (rm sout) dest v |}
  | ARITH dest op src1 src2 =>
      let v1 := operand_eval src1 (rm sin) in
      let v2 := operand_eval src2 (rm sin) in
      let v := arith_op_eval op v1 v2 in
      Some {| sm := sm sout;
              rm := assign (rm sout) dest v |}
  | LOAD dest base offset =>
      match get_addr base offset (rm sin) with
      | Some srce =>
          Some {| sm := sm sout;
                  rm := assign (rm sout) dest (sm sin srce) |}
      | None => None
      end
  | STORE srce base offset =>
      match get_addr base offset (rm sin) with
      | Some dest =>
          Some {| sm := assign (sm sin) dest (rm sin srce);
                  rm := rm sout |}
      | None => None
      end
  | MEMSWAP x base offset =>
      match get_addr base offset (rm sin) with
      | Some ad =>
          Some {| sm := assign (sm sin) ad (rm sin x);
                  rm := assign (rm sout) x (sm sin ad) |}
      | None => None
      end
  end.

Local Open Scope list_scope.

(** usual sequential semantics *)
Fixpoint sem_bblock (p: bblock) (s: state): option state :=
  match p with
  | nil => Some s
  | i::p' =>
    match sem_inst i s s with
    | Some s' => sem_bblock p' s'
    | None => None
    end
  end.

Definition state_equiv (s1 s2: state): Prop :=
  (forall x, sm s1 x = sm s2 x) /\
  (forall x, rm s1 x = rm s2 x). 

(* equalities on bblockram outputs *)
Definition res_equiv (os1 os2: option state): Prop :=
  match os1 with
  | Some s1 => exists s2, os2 = Some s2 /\ state_equiv s1 s2 
  | None => os2 = None
  end.


Definition bblock_equiv (p1 p2: bblock): Prop :=
  forall s, res_equiv (sem_bblock p1 s) (sem_bblock p2 s).

(** parallel semantics with in-order writes *)
Fixpoint sem_bblock_par_iw (p: bblock) (sin sout: state): option state :=
  match p with
  | nil => Some sout
  | i::p' =>
    match sem_inst i sin sout with
    | Some sout' => sem_bblock_par_iw p' sin sout'
    | None => None
    end
  end.

(** parallelism semantics with arbitrary order writes *)
Require Import Sorting.Permutation.

Definition sem_bblock_par (p: bblock) (sin: state) (sout: option state) := exists p', res_equiv sout (sem_bblock_par_iw p' sin sin) /\ Permutation p p'.
