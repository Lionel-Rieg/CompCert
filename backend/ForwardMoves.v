Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Module RELATION.
  
Definition t := (PTree.t reg).
Definition eq (r1 r2 : t) :=
  forall x, (PTree.get x r1) = (PTree.get x r2).

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq.
  intros; reflexivity.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq.
  intros; eauto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq.
  intros; congruence.
Qed.

Definition reg_beq (x y : reg) :=
  if Pos.eq_dec x y then true else false.

Definition beq (r1 r2 : t) := PTree.beq reg_beq r1 r2.

Lemma beq_correct: forall r1 r2, beq r1 r2 = true -> eq r1 r2.
Proof.
  unfold beq, eq. intros r1 r2 EQ x.
  pose proof (PTree.beq_correct reg_beq r1 r2) as CORRECT.
  destruct CORRECT as [CORRECTF CORRECTB].
  pose proof (CORRECTF EQ x) as EQx.
  clear CORRECTF CORRECTB EQ.
  unfold reg_beq in *.
  destruct (r1 ! x) as [R1x | ] in *;
    destruct (r2 ! x) as [R2x | ] in *;
    trivial; try contradiction.
  destruct (Pos.eq_dec R1x R2x) in *; congruence.
Qed.

(*
  Parameter ge: t -> t -> Prop.
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Parameter bot: t.
  Axiom ge_bot: forall x, ge x bot.
  Parameter lub: t -> t -> t.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.
*)