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

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.

Local Open Scope positive.

Inductive inj_instr : Type :=
  | INJnop
  | INJop: operation -> list reg -> reg -> inj_instr
  | INJload: memory_chunk -> addressing -> list reg -> reg -> inj_instr.

Definition inject_instr (i : inj_instr) (pc' : node) : instruction :=
  match i with
  | INJnop => Inop pc'
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
  | Icond _ _ pc' _ _ => pc'
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
  | Ibuiltin ef args res _ => Ibuiltin ef args res pc'
  | Icond cond args _ pc2 expected => Icond cond args pc' pc2 expected
  | Icall sig ros args res _ => Icall sig ros args res pc'
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

Definition inject_at' (already : node * code) pc l :=
  let (extra_pc, prog) := already in
  inject_at prog pc extra_pc l.

Definition inject_l (prog : code) extra_pc injections :=
  List.fold_left (fun already (injection : node * (list inj_instr)) =>
                    inject_at' already (fst injection) (snd injection))
    injections
    (extra_pc, prog).
(*
Definition inject' (prog : code) (extra_pc : node) (injections : PTree.t (list inj_instr)) :=
  PTree.fold inject_at' injections (extra_pc, prog).

Definition inject prog extra_pc injections : code :=
  snd (inject' prog extra_pc injections).
*)

Section INJECTOR.
  Variable gen_injections : function -> node -> reg -> PTree.t (list inj_instr).

  Definition valid_injection_instr (max_reg : reg) (i : inj_instr) :=
    match i with
    | INJnop => true
    | INJop op args res => (max_reg <? res) && (negb (is_trapping_op op)
       && (Datatypes.length args =? args_of_operation op)%nat) 
    | INJload _ _ _ res => max_reg <? res
    end.
  
  Definition valid_injections1 max_pc max_reg :=
    List.forallb
         (fun injection =>
            ((fst injection) <=? max_pc) &&
            (List.forallb (valid_injection_instr max_reg) (snd injection))
         ).

  Definition valid_injections f :=
    valid_injections1 (max_pc_function f) (max_reg_function f).
  
  Definition transf_function (f : function) : res function :=
    let max_pc := max_pc_function f in
    let max_reg := max_reg_function f in
    let injections := PTree.elements (gen_injections f max_pc max_reg) in
    if valid_injections1 max_pc max_reg injections
    then
      OK {| fn_sig := f.(fn_sig);
            fn_params := f.(fn_params);
            fn_stacksize := f.(fn_stacksize);
            fn_code := snd (inject_l (fn_code f) (Pos.succ max_pc) injections);
            fn_entrypoint := f.(fn_entrypoint) |}
    else Error (msg "Inject.transf_function: injections at bad locations").

Definition transf_fundef (fd: fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.
End INJECTOR.
