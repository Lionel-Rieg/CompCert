Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps CSE2deps.
Require Import CSE3analysis HashedSet.

Axiom preanalysis : RTL.function -> analysis_hints.

Definition run f := preanalysis f.

Section REWRITE.
  Context {ctx : eq_context}.

Definition find_op_in_fmap fmap pc op args :=
  match fmap with
  | None => None
  | Some map =>
    match PMap.get pc map with
    | Some rel => rhs_find (ctx:=ctx) pc (SOp op) args rel
    | None => None
    end
  end.

Definition find_load_in_fmap fmap pc chunk addr args :=
  match fmap with
  | None => None
  | Some map =>
    match PMap.get pc map with
    | Some rel => rhs_find (ctx:=ctx) pc (SLoad chunk addr) args rel
    | None => None
    end
  end.

Definition forward_move_b (rb : RB.t) (x : reg) :=
  match rb with
  | None => x
  | Some rel => forward_move (ctx := ctx) rel x
  end.

Definition subst_arg (fmap : option (PMap.t RB.t)) (pc : node) (x : reg) : reg :=
  match fmap with
  | None => x
  | Some inv => forward_move_b (PMap.get pc inv) x
  end.

Definition subst_args fmap pc := List.map (subst_arg fmap pc).

Definition transf_instr (fmap : option (PMap.t RB.t))
           (pc: node) (instr: instruction) :=
  match instr with
  | Iop op args dst s =>
    let args' := subst_args fmap pc args in
    match find_op_in_fmap fmap pc op args' with
    | None => Iop op args' dst s
    | Some src => Iop Omove (src::nil) dst s
    end
  | Iload trap chunk addr args dst s =>
    let args' := subst_args fmap pc args in
    match find_load_in_fmap fmap pc chunk addr args' with
    | None => Iload trap chunk addr args' dst s
    | Some src => Iop Omove (src::nil) dst s
    end
  | Istore chunk addr args src s =>
    Istore chunk addr (subst_args fmap pc args) src s
  | Icall sig ros args dst s =>
    Icall sig ros (subst_args fmap pc args) dst s
  | Itailcall sig ros args =>
    Itailcall sig ros (subst_args fmap pc args)
  | Icond cond args s1 s2 =>
    Icond cond (subst_args fmap pc args) s1 s2
  | Ijumptable arg tbl =>
    Ijumptable (subst_arg fmap pc arg) tbl
  | Ireturn (Some arg) =>
    Ireturn (Some (subst_arg fmap pc arg))
  | _ => instr
  end.
End REWRITE.

Definition transf_function (f: function) : function :=
  let ctx := context_from_hints (preanalysis f) in
  let invariants := internal_analysis (ctx := ctx) f in
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := PTree.map (transf_instr (ctx := ctx) invariants) f.(fn_code);
     fn_entrypoint := f.(fn_entrypoint) |}.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
