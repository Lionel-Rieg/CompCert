(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           Xavier Leroy       INRIA Paris-Rocquencourt       *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers
  ([Fxx]).

  The type [mreg] does not include reserved machine registers such as
  the zero register (x0), the link register (x1), the stack pointer
  (x2), the global pointer (x3), and the thread pointer (x4).
  Finally, register x31 is reserved for use as a temporary by the
  assembly-code generator [Asmgen].
*)

Inductive mreg: Type :=
  (* Allocatable General Purpose regs. *)
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7  | R8  | R9
  | R10 | R11 (* | R12 | R13 | R14 *) | R15  (* | R16 *) | R17 | R18 | R19
  | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 | R28 | R29
  | R30 | R31 (* | R32 *) | R33 | R34 | R35 | R36 | R37 | R38 | R39
  | R40 | R41 | R42 | R43 | R44 | R45 | R46 | R47 | R48 | R49
  | R50 | R51 | R52 | R53 | R54 | R55 | R56 | R57 | R58 | R59
  | R60 | R61 | R62 | R63.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     R0  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9
  :: R10 :: R11 (* :: R12 :: R13 :: R14 *) :: R15  (* :: R16 *) :: R17 :: R18 :: R19
  :: R20 :: R21 :: R22 :: R23 :: R24 :: R25 :: R26 :: R27 :: R28 :: R29
  :: R30 :: R31 (* :: R32 *) :: R33 :: R34 :: R35 :: R36 :: R37 :: R38 :: R39
  :: R40 :: R41 :: R42 :: R43 :: R44 :: R45 :: R46 :: R47 :: R48 :: R49
  :: R50 :: R51 :: R52 :: R53 :: R54 :: R55 :: R56 :: R57 :: R58 :: R59
  :: R60 :: R61 :: R62 :: R63 :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.
  
Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ := Tany64.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0  => 1  | R1  => 2  | R2  => 3  | R3  => 4  | R4  => 5
    | R5  => 6  | R6  => 7  | R7  => 8  | R8  => 9  | R9  => 10
    | R10 => 11 | R11 => 12 (* | R12 => 13 | R13 => 14 | R14 => 15 *)
    | R15 => 16 (* | R16 => 17 *) | R17 => 18 | R18 => 19 | R19 => 20
    | R20 => 21 | R21 => 22 | R22 => 23 | R23 => 24 | R24 => 25
    | R25 => 26 | R26 => 27 | R27 => 28 | R28 => 29 | R29 => 30
    | R30 => 31 | R31 => 32 (* | R32 => 33 *) | R33 => 34 | R34 => 35
    | R35 => 36 | R36 => 37 | R37 => 38 | R38 => 39 | R39 => 40
    | R40 => 41 | R41 => 42 | R42 => 43 | R43 => 44 | R44 => 45
    | R45 => 46 | R46 => 47 | R47 => 48 | R48 => 49 | R49 => 50
    | R50 => 51 | R51 => 52 | R52 => 53 | R53 => 54 | R54 => 55 
    | R55 => 56 | R56 => 57 | R57 => 58 | R58 => 59 | R59 => 60
    | R60 => 61 | R61 => 62 | R62 => 63 | R63 => 64 
    end.

  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
     ("R0" , R0)  :: ("R1" , R1)  :: ("R2" , R2)  :: ("R3" , R3)  :: ("R4" , R4)
  :: ("R5" , R5)  :: ("R6" , R6)  :: ("R7" , R7)  :: ("R8" , R8)  :: ("R9" , R9)
  :: ("R10", R10) :: ("R11", R11) (* :: ("R12", R12) :: ("R13", R13) :: ("R14", R14) *)
  :: ("R15", R15) (* :: ("R16", R16) *) :: ("R17", R17) :: ("R18", R18) :: ("R19", R19)
  :: ("R20", R20) :: ("R21", R21) :: ("R22", R22) :: ("R23", R23) :: ("R24", R24)
  :: ("R25", R25) :: ("R26", R26) :: ("R27", R27) :: ("R28", R28) :: ("R29", R29)
  :: ("R30", R30) :: ("R31", R31) (* :: ("R32", R32) *) :: ("R33", R33) :: ("R34", R34)
  :: ("R35", R35) :: ("R36", R36) :: ("R37", R37) :: ("R38", R38) :: ("R39", R39)
  :: ("R40", R40) :: ("R41", R41) :: ("R42", R42) :: ("R43", R43) :: ("R44", R44)
  :: ("R45", R45) :: ("R46", R46) :: ("R47", R47) :: ("R48", R48) :: ("R49", R49)
  :: ("R50", R50) :: ("R51", R51) :: ("R52", R52) :: ("R53", R53) :: ("R54", R54)
  :: ("R55", R55) :: ("R56", R56) :: ("R57", R57) :: ("R58", R58) :: ("R59", R59)
  :: ("R60", R60) :: ("R61", R61) :: ("R62", R62) :: ("R63", R63) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg := nil.
(*match op with
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle
  | Olongoffloat | Olonguoffloat | Olongofsingle | Olonguofsingle
      => F6 :: nil
  | _ => nil
  end.
*)

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := R62 :: R63 :: nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy sz al =>
    if Z.leb sz 15
    then R62 :: R63 :: R61 :: nil
    else R62 :: R63 :: R61 :: R60 :: nil
  | EF_profiling _ _ => R62 :: R63 ::nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := R17 :: nil.

Definition temp_for_parent_frame: mreg := R17. (* Temporary used to store the parent frame, where the arguments are *)

Definition destroyed_at_indirect_call: list mreg := nil.
  (* R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17 :: nil. *)

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg := (nil, None).

(* FIXME DMonniaux this seems to be the place for preferred registers for arguments *)
Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) := (nil, nil).

  (* match ef with
  | EF_builtin name sg =>
      if (negb Archi.ptr64) && string_dec name "__builtin_bswap64" then
        (Some R6 :: Some R5 :: nil, Some R5 :: Some R6 :: nil)
      else
        (nil, nil)
  | _ =>
    (nil, nil)
  end. *)

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are two: the pseudo [Ocast32signed],
  because it expands to a no-op owing to the representation of 32-bit
  integers as their 64-bit sign extension; and [Ocast32unsigned],
  because it builds on the same magic no-op. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Ofmaddf | Ofmaddfs
  | Ofmsubf | Ofmsubfs
  | Omadd | Omaddimm _
  | Omaddl | Omaddlimm _
  | Omsub | Omsubl
  | Osel _ _ | Oselimm _ _ | Osellimm _ _
  | Oinsf _ _ | Oinsfl _ _ => true
  | _ => false
  end.

(** Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg =>
    if string_dec id "__builtin_kvx_get" then OK_const :: nil
    else if string_dec id "__builtin_kvx_set"
    then OK_const :: OK_default :: nil
    else if string_dec id "__builtin_kvx_wfxl"
    then OK_const :: OK_default :: nil                 
    else if string_dec id "__builtin_kvx_wfxm"
    then OK_const :: OK_default :: nil
    else nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
