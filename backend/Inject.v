Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.

Local Open Scope positive.

Inductive inj_instr : Type :=
  | INJop: operation -> list reg -> reg -> inj_instr
  | INJload: memory_chunk -> addressing -> list reg -> reg -> inj_instr.

Definition inject_instr (i : inj_instr) (pc' : node) : instruction :=
  match i with
  | INJop op args dst => Iop op args dst pc'
  | INJload chunk addr args dst => Iload NOTRAP chunk addr args dst pc'
  end.

Fixpoint inject_list (prog : code) (pc : node) (dst : node)
         (l : list inj_instr) : node * code :=
  let pc' := Pos.succ pc in
  match l with
  | nil => (pc', PTree.set pc (Inop dst) prog)
  | h::t =>
    inject_list (PTree.set pc (inject_instr h pc') prog)
                pc' dst t
  end.

Definition successor (i : instruction) : node :=
  match i with
  | Inop pc' => pc'
  | Iop _ _ _ pc' => pc'
  | Iload _ _ _ _ _ pc' => pc'
  | Istore _ _ _ _ pc' => pc'
  | Icall _ _ _ _ pc' => pc'
  | Ibuiltin _ _ _ pc' => pc'
  | Icond _ _ pc' _ => pc'
  | Itailcall _ _ _
  | Ijumptable _ _
  | Ireturn _ => 1
  end.

Definition alter_successor (i : instruction) (pc' : node) : instruction :=
  match i with
  | Inop _ => Inop pc'
  | Iop op args dst _ => Iop op args dst pc'
  | Iload trap chunk addr args dst _ => Iload trap chunk addr args dst pc'
  | Istore chunk addr args src _ => Istore chunk addr args src pc'
  | Icall sig ri args dst _ => Icall sig ri args dst pc'
  | Ibuiltin ef args res _ => Ibuiltin ef args res pc'
  | Icond cond args _ pc2 => Icond cond args pc' pc2
  | Itailcall _ _ _
  | Ijumptable _ _
  | Ireturn _ => i
  end.

Definition inject_at (prog : code) (pc extra_pc : node)
           (l : list inj_instr) : node * code :=
  match PTree.get pc prog with
  | Some i =>
    inject_list (PTree.set pc (alter_successor i extra_pc) prog)
                extra_pc (successor i) l
  | None => inject_list prog extra_pc 1 l (* does not happen *)
  end.
