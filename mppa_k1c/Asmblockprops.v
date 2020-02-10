(** Common definition and proofs on Asmblock required by various modules *)

Require Import Coqlib.
Require Import Integers.
Require Import Memory.
Require Import Globalenvs.
Require Import Values.
Require Import Asmblock.

Definition bblock_simu (ge: Genv.t fundef unit) (f: function) (bb bb': bblock) :=
  forall rs m,
    exec_bblock ge f bb rs m <> Stuck ->
    exec_bblock ge f bb rs m = exec_bblock ge f bb' rs m.
    
Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma preg_of_data:
  forall r, data_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.
Hint Resolve preg_of_data: asmgen.

Lemma data_diff:
  forall r r',
  data_preg r = true -> data_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve data_diff: asmgen.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
Qed.

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence.
Qed.

Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.


Lemma nextblock_pc:
  forall b rs, (nextblock b rs)#PC = Val.offset_ptr rs#PC (Ptrofs.repr (size b)).
Proof.
  intros. apply Pregmap.gss.
Qed.

Lemma nextblock_inv:
  forall b r rs, r <> PC -> (nextblock b rs)#r = rs#r.
Proof.
  intros. unfold nextblock. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextblock_inv1:
  forall b r rs, data_preg r = true -> (nextblock b rs)#r = rs#r.
Proof.
  intros. apply nextblock_inv. red; intro; subst; discriminate.
Qed.

Ltac Simplif :=
  ((rewrite nextblock_inv by eauto with asmgen)
  || (rewrite nextblock_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextblock_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)
  ); auto with asmgen.

Ltac Simpl := repeat Simplif.

Theorem exec_basic_instr_pc:
  forall ge b rs1 m1 rs2 m2,
  exec_basic_instr ge b rs1 m1 = Next rs2 m2 ->
  rs2 PC = rs1 PC.
Proof.
  intros. destruct b; try destruct i; try destruct i.
  all: try (inv H; Simpl).
  1-10: unfold parexec_load_offset in H1; destruct (eval_offset ofs); try discriminate; destruct (Mem.loadv _ _ _); unfold parexec_incorrect_load in *; destruct trap; try discriminate; unfold concrete_default_notrap_load_value in *; inv H1; Simpl; fail.

  1-20: unfold parexec_load_reg, parexec_load_regxs in H1; destruct (Mem.loadv _ _ _); unfold parexec_incorrect_load in *; destruct trap; try discriminate; unfold concrete_default_notrap_load_value in *; inv H1; Simpl; fail.

  { (* PLoadQRRO *)
    unfold  parexec_load_q_offset in H1.
    destruct (gpreg_q_expand _) as [r0 r1] in H1.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    inv H1. Simpl. }
  { (* PLoadORRO *)
    unfold  parexec_load_o_offset in H1.
    destruct (gpreg_o_expand _) as [[[r0 r1] r2] r3] in H1.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    destruct (Mem.loadv _ _ _) in H1; try discriminate.
    inv H1. Simpl. }
  1-8: unfold parexec_store_offset in H1; destruct (eval_offset ofs); try discriminate; destruct (Mem.storev _ _ _); [inv H1; auto | discriminate]; fail.
  1-8: unfold parexec_store_reg in H1; destruct (Mem.storev _ _ _); [inv H1; Simpl | discriminate]; auto; fail.
  1-8: unfold parexec_store_regxs in H1; destruct (Mem.storev _ _ _); [inv H1; Simpl | discriminate]; auto; fail.
  
  { (* PStoreQRRO *)
    unfold  parexec_store_q_offset in H1.
    destruct (gpreg_q_expand _) as [r0 r1] in H1.
    unfold eval_offset in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    inv H1. Simpl. reflexivity. }
  { (* PStoreORRO *)
    unfold  parexec_store_o_offset in H1.
    destruct (gpreg_o_expand _) as [[[r0 r1] r2] r3] in H1.
    unfold eval_offset in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    destruct (Mem.storev _ _ _) in H1; try discriminate.
    inv H1. Simpl. reflexivity. }
  - destruct (Mem.alloc _ _ _). destruct (Mem.store _ _ _ _ _). inv H1. Simpl. discriminate.
  - destruct (Mem.loadv _ _ _); try discriminate. destruct (rs1 _); try discriminate.
    destruct (Mem.free _ _ _ _). inv H1. Simpl. discriminate.
  - destruct rs; try discriminate. inv H1. Simpl.
  - destruct rd; try discriminate. inv H1; Simpl.
  - reflexivity.
Qed.