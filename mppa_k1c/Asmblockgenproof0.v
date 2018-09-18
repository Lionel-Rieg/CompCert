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

(* ... skip ... *)


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
