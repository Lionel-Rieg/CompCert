Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Locations.
Require Import Machblock.
Require Import Asmblock.
Require Import Asmblockgen.

Module MB:=Machblock.
Module AB:=Asmblock.

(* inspired from Mach *)

Lemma find_label_tail:
  forall lbl c c', MB.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (MB.is_label lbl a). inv H. auto with coqlib. eauto with coqlib.
Qed.

(* inspired from Asmgenproof0 *)

(* ... skip ... *)

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> bblocks -> bblocks -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos bi c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + (size bi)) (bi :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. omega. generalize (size_positive bi); intros; omega.
Qed.

Lemma find_bblock_tail:
  forall c1 bi c2 pos,
  code_tail pos c1 (bi :: c2) ->
  find_bblock pos c1 = Some bi.
Proof.
  induction c1; simpl; intros.
  inversion H.  
  destruct (zlt pos 0). generalize (code_tail_pos _ _ _ H); intro; omega.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (size_positive a) (code_tail_pos _ _ _ H4). intro; omega.
  inv H. congruence. replace (pos0 + size a - size a) with pos0 by omega.
  eauto.
Qed.


Local Hint Resolve code_tail_0 code_tail_S.

Lemma code_tail_next:
  forall fn ofs c0,
  code_tail ofs fn c0 ->
  forall bi c1, c0 = bi :: c1 -> code_tail (ofs + (size bi)) fn c1.
Proof.
  induction 1; intros.
  - subst; eauto.
  - replace (pos + size bi + size bi0) with ((pos + size bi0) + size bi); eauto.
    omega.
Qed.

Lemma size_blocks_pos c: size_blocks c >= 0.
Proof.
  induction c as [| a l ]; simpl; try omega.
  generalize (size_positive a); omega.
Qed.

Remark code_tail_bounds_1:
  forall fn ofs c,
  code_tail ofs fn c -> 0 <= ofs <= size_blocks fn.
Proof.
  induction 1; intros; simpl.
  generalize (size_blocks_pos c). omega.
  generalize (size_positive bi). omega.
Qed.


Remark code_tail_bounds_2:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < size_blocks fn.
Admitted.
(*
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl.
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.
*)

(* TODO: adapt this lemma -- needs  Ptrofs.one -> size bi
Lemma code_tail_next_int:
  forall fn ofs bi c,
  size_blocks fn <= Ptrofs.max_unsigned ->
  code_tail (Ptrofs.unsigned ofs) fn (bi :: c) ->
  code_tail (Ptrofs.unsigned (Ptrofs.add ofs Ptrofs.one)) fn c.
Proof.
  intros. rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_one.
  rewrite Ptrofs.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds_2 _ _ _ _ H0). omega.
Qed.
*)


(** Predictor for return addresses in generated Asm code.

  The [return_address_offset] predicate defined here is used in the
  semantics for Mach to determine the return addresses that are
  stored in activation records. *)

(** Consider a Mach function [f] and a sequence [c] of Mach instructions
  representing the Mach code that remains to be executed after a
  function call returns.  The predicate [return_address_offset f c ofs]
  holds if [ofs] is the integer offset of the PPC instruction
  following the call in the Asm code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     Asm code           |                    |--------|
     Asm function       |------------- Pcall ---------|

                        <-------- ofs ------->
>>
*)

Definition return_address_offset (f: MB.function) (c: MB.code) (ofs: ptrofs) : Prop :=
  forall tf  tc,
  transf_function f = OK tf ->
  transl_blocks f c = OK tc ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) tc.

(* NB: this lemma should go into [Coqlib.v] *) 
Lemma is_tail_app A (l1: list A): forall l2, is_tail l2 (l1 ++ l2).
Proof.
  induction l1; simpl; auto with coqlib.
Qed.
Hint Resolve is_tail_app: coqlib.

Lemma transl_blocks_tail:
  forall f c1 c2, is_tail c1 c2 ->
  forall tc2, transl_blocks f c2 = OK tc2 ->
  exists tc1, transl_blocks f c1 = OK tc1 /\ is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  exists tc2; split; auto with coqlib.
  monadInv H0. exploit IHis_tail; eauto. intros (tc1 & A & B).
  exists tc1; split. auto.
  eapply is_tail_trans; eauto with coqlib. 
Qed.


Section RETADDR_EXISTS.

Hypothesis transf_function_inv:
  forall f tf, transf_function f = OK tf ->
  exists tc, transl_blocks f (Machblock.fn_code f) = OK tc /\ is_tail tc (fn_blocks tf).

Hypothesis transf_function_len:
  forall f tf, transf_function f = OK tf -> size_blocks (fn_blocks tf) <= Ptrofs.max_unsigned.

Lemma return_address_exists:
  forall b f sg ros c, b.(MB.exit) = Some (MBcall sg ros) -> is_tail (b :: c) f.(MB.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. destruct (transf_function f) as [tf|] eqn:TF.
+ exploit transf_function_inv; eauto. intros (tc1 & TR1 & TL1).
  exploit transl_blocks_tail; eauto. intros (tc2 & TR2 & TL2).
  unfold return_address_offset.
  (* exploit code_tail_next_int; eauto.*)
Admitted.

(*
Opaque transl_instr.
  monadInv TR2.
  assert (TL3: is_tail x (fn_code tf)).
  { apply is_tail_trans with tc1; auto.
    apply is_tail_trans with tc2; auto.
    eapply transl_instr_tail; eauto. }
  exploit is_tail_code_tail. eexact TL3. intros [ofs CT].
  exists (Ptrofs.repr ofs). red; intros.
  rewrite Ptrofs.unsigned_repr. congruence.
  exploit code_tail_bounds_1; eauto.
  apply transf_function_len in TF. omega.
+ exists Ptrofs.zero; red; intros. congruence.
Qed.
*)
End RETADDR_EXISTS.