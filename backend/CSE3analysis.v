Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps CSE2deps.
Require Import HashedSet.
Require List.

Module RELATION <: SEMILATTICE_WITHOUT_BOTTOM.
  Definition t := PSet.t.
  Definition eq (x : t) (y : t) := x = y.
  
  Lemma eq_refl: forall x, eq x x.
  Proof.
    unfold eq. trivial.
  Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. congruence.
  Qed.

  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. congruence.
  Qed.
  
  Definition beq (x y : t) := if PSet.eq x y then true else false.
  
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq.
    intros.
    destruct PSet.eq; congruence.
  Qed.
  
  Definition ge (x y : t) := (PSet.is_subset x y) = true.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge.
    intros.
    subst y.
    apply PSet.is_subset_spec.
    trivial.
  Qed.
  
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge.
    intros.
    rewrite PSet.is_subset_spec in *.
    intuition.
  Qed.
  
  Definition lub := PSet.inter.
  
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge, lub.
    intros.
    apply PSet.is_subset_spec.
    intro.
    rewrite PSet.ginter.
    rewrite andb_true_iff.
    intuition.
  Qed.
  
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge, lub.
    intros.
    apply PSet.is_subset_spec.
    intro.
    rewrite PSet.ginter.
    rewrite andb_true_iff.
    intuition.
  Qed.
End RELATION.

Module RB := ADD_BOTTOM(RELATION).
Module DS := Dataflow_Solver(RB)(NodeSetForward).

Inductive sym_op : Type :=
| SOp : operation -> sym_op
| SLoad : memory_chunk -> addressing -> sym_op.

Definition eq_dec_sym_op : forall s s' : sym_op, {s = s'} + {s <> s'}.
Proof.
  generalize eq_operation.
  generalize eq_addressing.
  generalize chunk_eq.
  decide equality.
Defined.

Definition eq_dec_args : forall l l' : list reg, { l = l' } + { l <> l' }.
Proof.
  apply List.list_eq_dec.
  exact peq.
Defined.

Record equation :=
  mkequation
    { eq_lhs : reg;
      eq_op : sym_op;
      eq_args : list reg }.

Definition eq_dec_equation :
  forall eq eq' : equation, {eq = eq'} + {eq <> eq'}.
Proof.
  generalize peq.
  generalize eq_dec_sym_op.
  generalize eq_dec_args.
  decide equality.
Defined.

Definition eq_id := node.

Definition add_i_j (i : reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  Regmap.set i (PSet.add j (Regmap.get i m)) m.

Definition add_ilist_j (ilist : list reg) (j : eq_id) (m : Regmap.t PSet.t) :=
  List.fold_left (fun already i => add_i_j i j already) ilist m.

Definition get_kills (eqs : PTree.t equation) :
  Regmap.t PSet.t :=
  PTree.fold (fun already (eqno : eq_id) (eq : equation) =>
                add_i_j (eq_lhs eq) eqno
                        (add_ilist_j (eq_args eq) eqno already)) eqs
             (PMap.init PSet.empty).

Definition is_move (op : operation) :
  { op = Omove } + { op <> Omove }.
Proof.
  destruct op; try (right ; congruence).
  left; trivial.
Qed.

Definition is_smove (sop : sym_op) :
  { sop = SOp Omove } + { sop <> SOp Omove }.
Proof.
  destruct sop; try (right ; congruence).
  destruct (is_move o).
  - left; congruence.
  - right; congruence.
Qed.

Definition get_moves (eqs : PTree.t equation) :
  Regmap.t PSet.t :=
  PTree.fold (fun already (eqno : eq_id) (eq : equation) =>
                if is_smove (eq_op eq)
                then add_i_j (eq_lhs eq) eqno already
                else already) eqs (PMap.init PSet.empty).
  
Record eq_context := mkeqcontext
                       { eq_catalog : eq_id -> option equation;
                         eq_find_oracle : node -> equation -> option eq_id;
                         eq_rhs_oracle : node -> sym_op -> list reg -> PSet.t;
                         eq_kill_reg : reg -> PSet.t;
                         eq_kill_mem : PSet.t;
                         eq_moves : reg -> PSet.t }.

Section OPERATIONS.
  Context {ctx : eq_context}.
  
  Definition kill_reg (r : reg) (rel : RELATION.t) : RELATION.t :=
    PSet.subtract rel (eq_kill_reg ctx r).
  
  Definition kill_mem (rel : RELATION.t) : RELATION.t :=
    PSet.subtract rel (eq_kill_mem ctx).

  Definition pick_source (l : list reg) := (* todo: take min? *)
    match l with
    | h::t => Some h
    | nil => None
    end.
  
  Definition forward_move (rel : RELATION.t)  (x : reg) : reg :=
    match pick_source (PSet.elements (PSet.inter rel (eq_moves ctx x))) with
    | None => x
    | Some eqno =>
      match eq_catalog ctx eqno with
      | Some eq =>
        if is_smove (eq_op eq) && peq x (eq_lhs eq)
        then
          match eq_args eq with
          | src::nil => src
          | _ => x
          end
        else x
      | _ => x
      end
    end.

  Definition forward_move_l (rel : RELATION.t) : list reg -> list reg :=
    List.map (forward_move rel).

  Section PER_NODE.
    Variable no : node.
    
  Definition eq_find  (eq : equation) :=
    match eq_find_oracle ctx no eq with
    | Some id =>
      match eq_catalog ctx id with
      | Some eq' => if eq_dec_equation eq eq' then Some id else None
      | None => None
      end
    | None => None
    end.


  Definition rhs_find (sop : sym_op) (args : list reg) (rel : RELATION.t) : option reg :=
    match pick_source (PSet.elements (PSet.inter (eq_rhs_oracle ctx no sop args) rel)) with
    | None => None
    | Some src =>
      match eq_catalog ctx src with
      | None => None
      | Some eq =>
        if eq_dec_sym_op sop (eq_op eq) && eq_dec_args args (eq_args eq)
        then Some (eq_lhs eq)
        else None
      end
    end.

  Definition oper2 (dst : reg) (op: sym_op)(args : list reg)
           (rel : RELATION.t) : RELATION.t :=
    let rel' := kill_reg dst rel in
    match eq_find {| eq_lhs := dst;
                     eq_op  := op;
                     eq_args:= args |} with
    | Some id => PSet.add id rel'
    | None => rel'
    end.

  Definition oper1 (dst : reg) (op: sym_op) (args : list reg)
             (rel : RELATION.t) : RELATION.t :=
    if List.in_dec peq dst args
    then kill_reg dst rel
    else oper2 dst op args rel.

  
  Definition move (src dst : reg) (rel : RELATION.t) : RELATION.t :=
    match eq_find {| eq_lhs := dst;
                     eq_op  := SOp Omove;
                     eq_args:= src::nil |} with
    | Some eq_id => PSet.add eq_id (kill_reg dst rel)
    | None => kill_reg dst rel
    end.

  (*
  Definition oper (dst : reg) (op: sym_op) (args : list reg)
             (rel : RELATION.t) : RELATION.t :=
    match find_op rel op (forward_move_l rel args) with
    | Some r => move r dst rel
    | None => oper1 op dst args rel
    end.
*)
  End PER_NODE.
End OPERATIONS.

Definition totoro := RELATION.lub.
