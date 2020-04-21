Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps CSE2deps.
Require Import CSE3analysis HashedSet.
Require Import RTLtyping.

Local Open Scope error_monad_scope.

Axiom preanalysis : typing_env -> RTL.function -> invariants * analysis_hints.

Section REWRITE.
  Context {ctx : eq_context}.

Definition find_op_in_fmap fmap pc op args :=
  match PMap.get pc fmap with
  | Some rel => rhs_find (ctx:=ctx) pc (SOp op) args rel
  | None => None
  end.

Definition find_load_in_fmap fmap pc chunk addr args :=
  match PMap.get pc fmap with
  | Some rel => rhs_find (ctx:=ctx) pc (SLoad chunk addr) args rel
  | None => None
  end.

Definition forward_move_b (rb : RB.t) (x : reg) :=
  match rb with
  | None => x
  | Some rel => forward_move (ctx := ctx) rel x
  end.

Definition subst_arg (fmap : PMap.t RB.t) (pc : node) (x : reg) : reg :=
  forward_move_b (PMap.get pc fmap) x.

Definition forward_move_l_b (rb : RB.t) (xl : list reg) :=
  match rb with
  | None => xl
  | Some rel => forward_move_l (ctx := ctx) rel xl
  end.

Definition subst_args fmap pc xl :=
  forward_move_l_b (PMap.get pc fmap) xl.

Definition transf_instr (fmap : PMap.t RB.t)
           (pc: node) (instr: instruction) :=
  match instr with
  | Iop op args dst s =>
    let args' := subst_args fmap pc args in
    match (if is_trivial_op op then None else find_op_in_fmap fmap pc op args') with
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
    Istore chunk addr (subst_args fmap pc args) (subst_arg fmap pc src) s
  | Icall sig ros args dst s =>
    Icall sig ros (subst_args fmap pc args) dst s
  | Itailcall sig ros args =>
    Itailcall sig ros (subst_args fmap pc args)
  | Icond cond args s1 s2 expected =>
    Icond cond (subst_args fmap pc args) s1 s2 expected
  | Ijumptable arg tbl =>
    Ijumptable (subst_arg fmap pc arg) tbl
  | Ireturn (Some arg) =>
    Ireturn (Some (subst_arg fmap pc arg))
  | _ => instr
  end.
End REWRITE.

Definition transf_function (f: function) : res function :=
  do tenv <- type_function f;
  let (invariants, hints) := preanalysis tenv f in
  let ctx := context_from_hints hints in
  if check_inductiveness (ctx:=ctx) f tenv invariants
  then
    OK {| fn_sig := f.(fn_sig);
          fn_params := f.(fn_params);
          fn_stacksize := f.(fn_stacksize);
          fn_code := PTree.map (transf_instr (ctx := ctx) invariants)
                               f.(fn_code);
          fn_entrypoint := f.(fn_entrypoint) |}
  else Error (msg "cse3: not inductive").

Definition transf_fundef (fd: fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.
