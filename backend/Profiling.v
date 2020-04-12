Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.

Local Open Scope positive.

Parameter function_id : function -> AST.profiling_id.
Parameter branch_id : AST.profiling_id -> node -> AST.profiling_id.

Section PER_FUNCTION_ID.
  Variable f_id : AST.profiling_id.
  
  Definition inject_profiling_call (prog : code)
             (pc extra_pc ifso ifnot : node) : node * code :=
    let id := branch_id f_id pc in
    let extra_pc' := Pos.succ extra_pc in
    let prog' := PTree.set extra_pc
                           (Ibuiltin (EF_profiling id 0%Z) nil BR_none ifnot) prog in
    let prog'':= PTree.set extra_pc'
                           (Ibuiltin (EF_profiling id 1%Z) nil BR_none ifso) prog' in
    (Pos.succ extra_pc', prog'').
  
  Definition inject_at (prog : code) (pc extra_pc : node) : node * code :=
    match PTree.get pc prog with
    | Some (Icond cond args ifso ifnot expected) =>
      inject_profiling_call
        (PTree.set pc
                   (Icond cond args (Pos.succ extra_pc) extra_pc expected) prog)
        pc extra_pc ifso ifnot
    | _ => inject_profiling_call prog pc extra_pc 1 1 (* does not happen *)
    end.

  Definition inject_at' (already : node * code) pc :=
    let (extra_pc, prog) := already in
    inject_at prog pc extra_pc.

  Definition inject_l (prog : code) extra_pc injections :=
    List.fold_left (fun already (inject_pc : node) =>
                      inject_at' already inject_pc)
                   injections
                   (extra_pc, prog).

  Definition gen_conditions (prog : code) :=
    List.map fst (PTree.elements (PTree.filter1
                                    (fun instr =>
                                       match instr with
                                       | Icond cond args ifso ifnot expected => true
                                       | _ => false
                                       end) prog)).
End PER_FUNCTION_ID.

Definition transf_function (f : function) : function :=
  let max_pc := max_pc_function f in
  let conditions := gen_conditions (fn_code f) in
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := snd (inject_l (function_id f) (fn_code f) (Pos.succ max_pc) conditions);
     fn_entrypoint := f.(fn_entrypoint) |}.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
