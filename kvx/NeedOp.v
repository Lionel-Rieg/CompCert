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

Require Import Coqlib.
Require Import AST Integers Floats.
Require Import Values Memory Globalenvs.
Require Import Op RTL.
Require Import NeedDomain.

(** Neededness analysis for RISC-V operators *)

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.
Definition op3 (nv: nval) := nv :: nv :: nv :: nil.

Definition needs_of_condition (cond: condition): list nval := nil.
Definition needs_of_condition0 (cond0: condition0): list nval := nil.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => op1 nv
  | Ointconst n => nil
  | Olongconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oaddrsymbol id ofs => nil
  | Oaddrstack ofs => nil
  | Ocast8signed => op1 (sign_ext 8 nv)
  | Ocast16signed => op1 (sign_ext 16 nv)
  | Oadd => op2 (modarith nv)
  | Oaddimm n => op1 (modarith nv)
  | Oaddx _ => op2 (default nv)
  | Oaddximm _ _ => op1 (default nv)
  | Oneg => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Orevsubimm _ => op1 (default nv)
  | Orevsubx _ => op2 (default nv)
  | Orevsubximm _ _ => op1 (default nv)
  | Omul => op2 (modarith nv)
  | Omulimm _ => op1 (modarith nv)
  | Omulhs | Omulhu | Odiv | Odivu | Omod | Omodu => op2 (default nv)
  | Oand => op2 (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Onand => op2 (bitwise nv)
  | Onandimm n => op1 (andimm nv n)
  | Oor => op2 (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Onor => op2 (bitwise nv)
  | Onorimm n => op1 (orimm nv n)
  | Oxor => op2 (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)
  | Onxor => op2 (bitwise nv)
  | Onxorimm n => op1 (bitwise nv)
  | Onot => op1 (bitwise nv)
  | Oandn => op2 (bitwise nv)
  | Oandnimm n => op1 (andimm nv n)
  | Oorn => op2 (bitwise nv)
  | Oornimm n => op1 (orimm nv n)
  | Oshl | Oshr | Oshru => op2 (default nv)
  | Oshlimm n => op1 (shlimm nv n)
  | Oshrimm n => op1 (shrimm nv n)
  | Ororimm n => op1 (ror nv n)
  | Oshruimm n => op1 (shruimm nv n)
  | Oshrximm n => op1 (default nv)
  | Omadd => op3 (modarith nv)
  | Omaddimm n => op2 (modarith nv)
  | Omsub => op3 (modarith nv)
  | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)
  | Ocast32signed => op1 (default nv)
  | Ocast32unsigned => op1 (default nv)
  | Oaddl => op2 (default nv)
  | Oaddlimm n => op1 (default nv)
  | Oaddxl _ => op2 (default nv)
  | Oaddxlimm _ _ => op1 (default nv)
  | Orevsublimm _ => op1 (default nv)
  | Orevsubxl _ => op2 (default nv)
  | Orevsubxlimm _ _ => op1 (default nv)
  | Onegl => op1 (default nv)
  | Osubl => op2 (default nv)
  | Omull => op2 (default nv)
  | Omullimm _ => op1 (default nv)
  | Omullhs | Omullhu | Odivl | Odivlu | Omodl | Omodlu => op2 (default nv)
  | Oandl => op2 (default nv)
  | Oandlimm n => op1 (default nv)
  | Onandl => op2 (default nv)
  | Onandlimm n => op1 (default nv)
  | Oorl => op2 (default nv)
  | Oorlimm n => op1 (default nv)
  | Onorl => op2 (default nv)
  | Onorlimm n => op1 (default nv)
  | Oxorl => op2 (default nv)
  | Oxorlimm n => op1 (default nv)
  | Onxorl => op2 (default nv)
  | Onxorlimm n => op1 (default nv)
  | Onotl => op1 (default nv)
  | Oandnl => op2 (default nv)
  | Oandnlimm n => op1 (default nv)
  | Oornl => op2 (default nv)
  | Oornlimm n => op1 (default nv)
  | Oshll | Oshrl | Oshrlu => op2 (default nv)
  | Oshllimm n => op1 (default nv)
  | Oshrlimm n => op1 (default nv)
  | Oshrluimm n => op1 (default nv)
  | Oshrxlimm n => op1 (default nv)
  | Omaddl => op3 (default nv)
  | Omaddlimm n => op2 (default nv)
  | Omsubl => op3 (default nv)
  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf | Ominf | Omaxf => op2 (default nv)
  | Ofmaddf | Ofmsubf => op3 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs | Ominfs | Omaxfs => op2 (default nv)
  | Oinvfs => op1 (default nv)
  | Ofmaddfs | Ofmsubfs => op3 (default nv)
  | Ofloatofsingle | Osingleoffloat => op1 (default nv)
  | Ointoffloat | Ointuoffloat => op1 (default nv)
  | Olongoffloat | Olonguoffloat | Ofloatoflong | Ofloatoflongu => op1 (default nv)
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu => op1 (default nv)
  | Olongofsingle | Olonguofsingle | Osingleoflong | Osingleoflongu => op1 (default nv)
  | Ocmp c => needs_of_condition c
  | Oextfz _ _ | Oextfs _ _  | Oextfzl _ _ | Oextfsl _ _ => op1 (default nv)
  | Oinsf _ _ | Oinsfl _ _ => op2 (default nv)
  | Osel c ty => nv :: nv :: needs_of_condition0 c
  | Oselimm c imm
  | Osellimm c imm => nv :: needs_of_condition0 c
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | _ => false
  end.

Ltac InvAgree :=
  match goal with
  | [H: vagree_list nil _ _ |- _ ] => inv H; InvAgree
  | [H: vagree_list (_::_) _ _ |- _ ] => inv H; InvAgree
  | _ => idtac
  end.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Section SOUNDNESS.

Variable ge: genv.
Variable sp: block.
Variables m1 m2: mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.

Lemma needs_of_condition_sound:
  forall cond args b args',
  eval_condition cond args m1 = Some b ->
  vagree_list args args' (needs_of_condition cond) ->
  eval_condition cond args' m2 = Some b.
Proof.
  intros. unfold needs_of_condition in H0.
  eapply default_needs_of_condition_sound; eauto.
Qed.

Let valid_pointer_inj:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  unfold inject_id; intros. inv H. rewrite Ptrofs.add_zero.
  rewrite Mem.valid_pointer_nonempty_perm in *. eauto.
Qed.

Let weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  unfold inject_id; intros. inv H. rewrite Ptrofs.add_zero.
  rewrite Mem.weak_valid_pointer_spec in *.
  rewrite ! Mem.valid_pointer_nonempty_perm in *.
  destruct H0; [left|right]; eauto.
Qed.

Let weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  unfold inject_id; intros. inv H. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
Qed.

Let valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  inject_id b1 = Some (b1', delta1) ->
  inject_id b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  unfold inject_id; intros. left; congruence.
Qed.

Lemma needs_of_condition0_sound:
  forall cond arg1 b arg2,
  eval_condition0 cond arg1 m1 = Some b ->
  vagree arg1 arg2 All ->
  eval_condition0 cond arg2 m2 = Some b.
Proof.
  intros until arg2.
  intros Hcond Hagree.
  apply eval_condition0_inj with (f := inject_id) (m1 := m1) (v1 := arg1); simpl; auto.
  apply val_inject_lessdef. apply lessdef_vagree. assumption.
Qed.

Lemma addl_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (default x) -> vagree v2 w2 (default x) ->
  vagree (Val.addl v1 v2) (Val.addl w1 w2) x.
Proof.
  unfold default; intros.
  destruct x; simpl in *; trivial.
  - unfold Val.addl.
    destruct v1; destruct v2; trivial; destruct Archi.ptr64; trivial.
  - apply Val.addl_lessdef; trivial.
Qed.

Lemma subl_lessdef:
  forall v1 v1' v2 v2',
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Val.lessdef (Val.subl v1 v2) (Val.subl v1' v2').
Proof.
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto.
Qed.

Lemma subl_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (default x) -> vagree v2 w2 (default x) ->
  vagree (Val.subl v1 v2) (Val.subl w1 w2) x.
Proof.
  unfold default; intros.
  destruct x; simpl in *; trivial.
  - unfold Val.subl.
    destruct v1; destruct v2; trivial; destruct Archi.ptr64; simpl; trivial.
    destruct (eq_block _ _) ; simpl; trivial.
  - apply subl_lessdef; trivial.
Qed.


Lemma mull_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (default x) -> vagree v2 w2 (default x) ->
  vagree (Val.mull v1 v2) (Val.mull w1 w2) x.
Proof.
  unfold default; intros.
  destruct x; simpl in *; trivial.
  - unfold Val.mull.
    destruct v1; destruct v2; trivial.
  - unfold Val.mull.
    destruct v1; destruct v2; trivial.
    inv H. inv H0.
    trivial.
Qed.
  

Remark default_idem: forall nv, default (default nv) = default nv.
Proof.
  destruct nv; simpl; trivial.
Qed.

Lemma vagree_triple_op_float :
  forall f a b c x y z nv,
    (vagree a x (default nv)) ->
    (vagree b y (default nv)) ->
    (vagree c z (default nv)) ->
    (vagree (ExtValues.triple_op_float f a b c)
            (ExtValues.triple_op_float f x y z) nv).
Proof.
  induction nv;
  intros Hax Hby Hcz.
  - trivial.
  - simpl in *. destruct a; simpl; trivial.
    destruct b; simpl; trivial.
    destruct c; simpl; trivial.
  - simpl in *. destruct a; simpl; trivial.
    destruct b; simpl; trivial.
    destruct c; simpl; trivial.
    inv Hax. inv Hby. inv Hcz.
    simpl.
    constructor.
Qed.

Lemma vagree_triple_op_single :
  forall f a b c x y z nv,
    (vagree a x (default nv)) ->
    (vagree b y (default nv)) ->
    (vagree c z (default nv)) ->
    (vagree (ExtValues.triple_op_single f a b c)
            (ExtValues.triple_op_single f x y z) nv).
Proof.
  induction nv;
  intros Hax Hby Hcz.
  - trivial.
  - simpl in *. destruct a; simpl; trivial.
    destruct b; simpl; trivial.
    destruct c; simpl; trivial.
  - simpl in *. destruct a; simpl; trivial.
    destruct b; simpl; trivial.
    destruct c; simpl; trivial.
    inv Hax. inv Hby. inv Hcz.
    simpl.
    constructor.
Qed.

Hint Resolve vagree_triple_op_float vagree_triple_op_single : na.

Lemma needs_of_operation_sound:
  forall op args v nv args',
  eval_operation ge (Vptr sp Ptrofs.zero) op args m1 = Some v ->
  vagree_list args args' (needs_of_operation op nv) ->
  nv <> Nothing ->
  exists v',
     eval_operation ge (Vptr sp Ptrofs.zero) op args' m2 = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_operation; intros; destruct op; try (eapply default_needs_of_operation_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree; TrivialExists.
- apply sign_ext_sound; auto. compute; auto. 
- apply sign_ext_sound; auto. compute; auto. 
- apply add_sound; auto.
- apply add_sound; auto with na.
- apply neg_sound; auto.
- apply mul_sound; auto.
- apply mul_sound; auto with na.
- apply and_sound; auto.
- apply andimm_sound; auto.
- apply notint_sound; apply and_sound; auto.
- apply notint_sound; apply andimm_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply notint_sound; apply or_sound; auto.
- apply notint_sound; apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto with na.
- apply notint_sound; apply xor_sound; auto.
- apply notint_sound; apply xor_sound; auto with na.
- apply notint_sound; auto.
- apply and_sound; try apply notint_sound; auto with na.
- apply andimm_sound; try apply notint_sound; auto with na.
- apply or_sound; try apply notint_sound; auto with na.
- apply orimm_sound; try apply notint_sound; auto with na.
- apply shlimm_sound; auto.
- apply shrimm_sound; auto.
- apply shruimm_sound; auto.
- apply ror_sound; auto.
  (* madd *)
- apply add_sound; try apply mul_sound; auto with na; rewrite modarith_idem; assumption.
- apply add_sound; try apply mul_sound; auto with na; rewrite modarith_idem; assumption.
- repeat rewrite ExtValues.sub_add_neg.
  apply add_sound; trivial.
  apply neg_sound; trivial.
  rewrite modarith_idem.
  apply mul_sound;
  rewrite modarith_idem; trivial.
- destruct (eval_condition0 _ _ _) as [b|] eqn:EC.
  erewrite needs_of_condition0_sound by eauto.
  apply select_sound; auto.
  simpl; auto with na.
  (* select imm *)
- destruct (eval_condition0 _ _ _) as [b|] eqn:EC.
  { erewrite needs_of_condition0_sound by eauto.
  apply select_sound; auto with na. }
  simpl; auto with na.
  (* select long imm *)
- destruct (eval_condition0 _ _ _) as [b|] eqn:EC.
  { erewrite needs_of_condition0_sound by eauto.
  apply select_sound; auto with na. }
  simpl; auto with na.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1' args',
  operation_is_redundant op nv = true ->
  eval_operation ge (Vptr sp Ptrofs.zero) op (arg1 :: args) m1 = Some v ->
  vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; inv H1; FuncInv; subst.
- apply sign_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto.
- apply orimm_redundant_sound; auto.
Qed.

End SOUNDNESS.
