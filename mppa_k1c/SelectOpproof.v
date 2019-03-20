(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for operators *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import Events.

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.


(** * Axiomatization of the helper functions *)

Definition external_implements (name: string) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall F V (ge: Genv.t F V) m,
  external_call (EF_runtime name sg) ge vargs m E0 vres m.

Definition builtin_implements (name: string) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall F V (ge: Genv.t F V) m,
  external_call (EF_builtin name sg) ge vargs m E0 vres m.

Axiom i64_helpers_correct :
    (forall x z, Val.longoffloat x = Some z -> external_implements "__compcert_i64_dtos" sig_f_l (x::nil) z)
 /\ (forall x z, Val.longuoffloat x = Some z -> external_implements "__compcert_i64_dtou" sig_f_l (x::nil) z)
 /\ (forall x z, Val.floatoflong x = Some z -> external_implements "__compcert_i64_stod" sig_l_f (x::nil) z)
 /\ (forall x z, Val.floatoflongu x = Some z -> external_implements "__compcert_i64_utod" sig_l_f (x::nil) z)
 /\ (forall x z, Val.singleoflong x = Some z -> external_implements "__compcert_i64_stof" sig_l_s (x::nil) z)
 /\ (forall x z, Val.singleoflongu x = Some z -> external_implements "__compcert_i64_utof" sig_l_s (x::nil) z)
 /\ (forall x, builtin_implements "__builtin_negl" sig_l_l (x::nil) (Val.negl x))
 /\ (forall x y, builtin_implements "__builtin_addl" sig_ll_l (x::y::nil) (Val.addl x y))
 /\ (forall x y, builtin_implements "__builtin_subl" sig_ll_l (x::y::nil) (Val.subl x y))
 /\ (forall x y, builtin_implements "__builtin_mull" sig_ii_l (x::y::nil) (Val.mull' x y))
 /\ (forall x y z, Val.divls x y = Some z -> external_implements "__compcert_i64_sdiv" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.divlu x y = Some z -> external_implements "__compcert_i64_udiv" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.modls x y = Some z -> external_implements "__compcert_i64_smod" sig_ll_l (x::y::nil) z)
 /\ (forall x y z, Val.modlu x y = Some z -> external_implements "__compcert_i64_umod" sig_ll_l (x::y::nil) z)
 /\ (forall x y, external_implements "__compcert_i64_shl" sig_li_l (x::y::nil) (Val.shll x y))
 /\ (forall x y, external_implements "__compcert_i64_shr" sig_li_l (x::y::nil) (Val.shrlu x y))
 /\ (forall x y, external_implements "__compcert_i64_sar" sig_li_l (x::y::nil) (Val.shrl x y))
 /\ (forall x y, external_implements "__compcert_i64_umulh" sig_ll_l (x::y::nil) (Val.mullhu x y))
 /\ (forall x y, external_implements "__compcert_i64_smulh" sig_ll_l (x::y::nil) (Val.mullhs x y))
 /\ (forall x y z, Val.divs x y = Some z -> external_implements "__compcert_i32_sdiv" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.divu x y = Some z -> external_implements "__compcert_i32_udiv" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.mods x y = Some z -> external_implements "__compcert_i32_smod" sig_ii_i (x::y::nil) z)
 /\ (forall x y z, Val.modu x y = Some z -> external_implements "__compcert_i32_umod" sig_ii_i (x::y::nil) z)
.

Definition helper_declared {F V: Type} (p: AST.program (AST.fundef F) V) (id: ident) (name: string) (sg: signature) : Prop :=
  (prog_defmap p)!id = Some (Gfun (External (EF_runtime name sg))).

Definition helper_functions_declared {F V: Type} (p: AST.program (AST.fundef F) V) (hf: helper_functions) : Prop :=
     helper_declared p i64_dtos "__compcert_i64_dtos" sig_f_l
  /\ helper_declared p i64_dtou "__compcert_i64_dtou" sig_f_l
  /\ helper_declared p i64_stod "__compcert_i64_stod" sig_l_f
  /\ helper_declared p i64_utod "__compcert_i64_utod" sig_l_f
  /\ helper_declared p i64_stof "__compcert_i64_stof" sig_l_s
  /\ helper_declared p i64_utof "__compcert_i64_utof" sig_l_s
  /\ helper_declared p i64_sdiv "__compcert_i64_sdiv" sig_ll_l
  /\ helper_declared p i64_udiv "__compcert_i64_udiv" sig_ll_l
  /\ helper_declared p i64_smod "__compcert_i64_smod" sig_ll_l
  /\ helper_declared p i64_umod "__compcert_i64_umod" sig_ll_l
  /\ helper_declared p i64_shl "__compcert_i64_shl" sig_li_l
  /\ helper_declared p i64_shr "__compcert_i64_shr" sig_li_l
  /\ helper_declared p i64_sar "__compcert_i64_sar" sig_li_l
  /\ helper_declared p i64_umulh "__compcert_i64_umulh" sig_ll_l
  /\ helper_declared p i64_smulh "__compcert_i64_smulh" sig_ll_l
  /\ helper_declared p i32_sdiv "__compcert_i32_sdiv" sig_ii_i
  /\ helper_declared p i32_udiv "__compcert_i32_udiv" sig_ii_i
  /\ helper_declared p i32_smod "__compcert_i32_smod" sig_ii_i
  /\ helper_declared p i32_umod "__compcert_i32_umod" sig_ii_i.

(** * Useful lemmas and tactics *)

(** The following are trivial lemmas and custom tactics that help
  perform backward (inversion) and forward reasoning over the evaluation
  of operator applications. *)

Ltac EvalOp := eapply eval_Eop; eauto with evalexpr.

Ltac InvEval1 :=
  match goal with
  | [ H: (eval_expr _ _ _ _ _ (Eop _ Enil) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ _ (Eop _ (_ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ _ (Eop _ (_ ::: _ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ _ Enil _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ _ (_ ::: _) _) |- _ ] =>
      inv H; InvEval1
  | _ =>
      idtac
  end.

Ltac InvEval2 :=
  match goal with
  | [ H: (eval_operation _ _ _ nil _ = Some _) |- _ ] =>
      simpl in H; inv H
  | [ H: (eval_operation _ _ _ (_ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | _ =>
      idtac
  end.

Ltac InvEval := InvEval1; InvEval2; InvEval2.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, _ /\ Val.lessdef ?a v ] => exists a; split; [EvalOp | auto]
  end.

(** * Correctness of the smart constructors *)

Section CMCONSTR.
Variable prog: program.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.
Let ge := Genv.globalenv prog.
Variable sp: val.
Variable e: env.
Variable m: mem.

(* Helper lemmas - from SplitLongproof.v *)

Ltac UseHelper := decompose [Logic.and] i64_helpers_correct; eauto.
Ltac DeclHelper := red in HELPERS; decompose [Logic.and] HELPERS; eauto.

Lemma eval_helper:
  forall le id name sg args vargs vres,
  eval_exprlist ge sp e m le args vargs ->
  helper_declared prog id name sg  ->
  external_implements name sg vargs vres ->
  eval_expr ge sp e m le (Eexternal id sg args) vres.
Proof.
  intros.
  red in H0. apply Genv.find_def_symbol in H0. destruct H0 as (b & P & Q).
  rewrite <- Genv.find_funct_ptr_iff in Q.
  econstructor; eauto.
Qed.

Corollary eval_helper_1:
  forall le id name sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  helper_declared prog id name sg  ->
  external_implements name sg (varg1::nil) vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor.
Qed.

Corollary eval_helper_2:
  forall le id name sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  helper_declared prog id name sg  ->
  external_implements name sg (varg1::varg2::nil) vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor; auto. constructor.
Qed.

(** We now show that the code generated by "smart constructor" functions
  such as [Selection.notint] behaves as expected.  Continuing the
  [notint] example, we show that if the expression [e]
  evaluates to some integer value [Vint n], then [Selection.notint e]
  evaluates to a value [Vint (Int.not n)] which is indeed the integer
  negation of the value of [e].

  All proofs follow a common pattern:
- Reasoning by case over the result of the classification functions
  (such as [add_match] for integer addition), gathering additional
  information on the shape of the argument expressions in the non-default
  cases.
- Inversion of the evaluations of the arguments, exploiting the additional
  information thus gathered.
- Equational reasoning over the arithmetic operations performed,
  using the lemmas from the [Int] and [Float] modules.
- Construction of an evaluation derivation for the expression returned
  by the smart constructor.
*)

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Theorem eval_addrsymbol:
  forall le id ofs,
  exists v, eval_expr ge sp e m le (addrsymbol id ofs) v /\ Val.lessdef (Genv.symbol_address ge id ofs) v.
Proof.
  intros. unfold addrsymbol. econstructor; split.
  EvalOp. simpl; eauto.
  auto.
Qed.

Theorem eval_addrstack:
  forall le ofs,
  exists v, eval_expr ge sp e m le (addrstack ofs) v /\ Val.lessdef (Val.offset_ptr sp ofs) v.
Proof.
  intros. unfold addrstack. econstructor; split.
  EvalOp. simpl; eauto.
  auto.
Qed.

Theorem eval_addimm:
  forall n, unary_constructor_sound (addimm n) (fun x => Val.add x (Vint n)).
Proof.
  red; unfold addimm; intros until x.
  predSpec Int.eq Int.eq_spec n Int.zero.
  - subst n. intros. exists x; split; auto.
    destruct x; simpl; auto.
    rewrite Int.add_zero; auto.
  - case (addimm_match a); intros; InvEval; simpl.
    + TrivialExists; simpl. rewrite Int.add_commut. auto.
    + econstructor; split. EvalOp. simpl; eauto. 
      unfold Genv.symbol_address. destruct (Genv.find_symbol ge s); simpl; auto.
    + econstructor; split. EvalOp. simpl; eauto. 
      destruct sp; simpl; auto.
    + TrivialExists; simpl. subst x. rewrite Val.add_assoc. rewrite Int.add_commut. auto.
    + TrivialExists.
Qed.

Theorem eval_add: binary_constructor_sound add Val.add.
Proof.
  red; intros until y.
  unfold add; case (add_match a b); intros; InvEval.
  - rewrite Val.add_commut. apply eval_addimm; auto.
  - apply eval_addimm; auto.
  - subst.
    replace (Val.add (Val.add v1 (Vint n1)) (Val.add v0 (Vint n2)))
       with (Val.add (Val.add v1 v0) (Val.add (Vint n1) (Vint n2))).
    apply eval_addimm. EvalOp.
    repeat rewrite Val.add_assoc. decEq. apply Val.add_permut.
  - subst. econstructor; split.
    EvalOp. constructor. EvalOp. simpl; eauto. constructor. eauto. constructor. simpl; eauto.
    rewrite Val.add_commut. destruct sp; simpl; auto.
    destruct v1; simpl; auto.
  - subst. econstructor; split.
    EvalOp. constructor. EvalOp. simpl; eauto. constructor. eauto. constructor. simpl; eauto.
    destruct sp; simpl; auto.
    destruct v1; simpl; auto.
  - subst.
    replace (Val.add (Val.add v1 (Vint n1)) y)
       with (Val.add (Val.add v1 y) (Vint n1)).
    apply eval_addimm. EvalOp.
    repeat rewrite Val.add_assoc. decEq. apply Val.add_commut.
  - subst.
    replace (Val.add x (Val.add v1 (Vint n2)))
       with (Val.add (Val.add x v1) (Vint n2)).
    apply eval_addimm. EvalOp.
    repeat rewrite Val.add_assoc. reflexivity.
  - (* Omadd *)
    subst. TrivialExists.
  - (* Omadd rev *)
    subst. rewrite Val.add_commut. TrivialExists.
  - (* Omaddimm *)
    subst. TrivialExists.
  - (* Omaddimm rev *)
    subst. rewrite Val.add_commut. TrivialExists.
  - TrivialExists.
Qed.

Theorem eval_sub: binary_constructor_sound sub Val.sub.
Proof.
  red; intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  - rewrite Val.sub_add_opp. apply eval_addimm; auto.
  - subst. rewrite Val.sub_add_l. rewrite Val.sub_add_r.
    rewrite Val.add_assoc. simpl. rewrite Int.add_commut. rewrite <- Int.sub_add_opp.
    apply eval_addimm; EvalOp.
  - subst. rewrite Val.sub_add_l. apply eval_addimm; EvalOp.
  - subst. rewrite Val.sub_add_r. apply eval_addimm; EvalOp.
  - TrivialExists.
Qed.

Theorem eval_negint: unary_constructor_sound negint (fun v => Val.sub Vzero v).
Proof.
  red; intros until x. unfold negint. case (negint_match a); intros; InvEval.
  TrivialExists.
  TrivialExists.
Qed.

Theorem eval_shlimm:
  forall n, unary_constructor_sound (fun a => shlimm a n)
                                    (fun x => Val.shl x (Vint n)).
Proof.
  red; intros until x.  unfold shlimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shl_zero; auto.

  destruct (Int.ltu n Int.iwordsize) eqn:LT; simpl.
  destruct (shlimm_match a); intros; InvEval.
  - exists (Vint (Int.shl n1 n)); split. EvalOp.
    simpl. rewrite LT. auto.
  - destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?.
    + exists (Val.shl v1 (Vint (Int.add n n1))); split. EvalOp.
      subst. destruct v1; simpl; auto.
      rewrite Heqb.
      destruct (Int.ltu n1 Int.iwordsize) eqn:?; simpl; auto.
      destruct (Int.ltu n Int.iwordsize) eqn:?; simpl; auto.
      rewrite Int.add_commut. rewrite Int.shl_shl; auto. rewrite Int.add_commut; auto.
    + subst. TrivialExists. econstructor. EvalOp. simpl; eauto. constructor.
      simpl. auto.
  - TrivialExists.
  - intros; TrivialExists. constructor. eauto. constructor. EvalOp. simpl; eauto. constructor.
    auto.
Qed.

Theorem eval_shruimm:
  forall n, unary_constructor_sound (fun a => shruimm a n)
                                    (fun x => Val.shru x (Vint n)).
Proof.
  red; intros until x. unfold shruimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shru_zero; auto.

  destruct (Int.ltu n Int.iwordsize) eqn:LT; simpl.
  destruct (shruimm_match a); intros; InvEval.
  - exists (Vint (Int.shru n1 n)); split. EvalOp.
    simpl. rewrite LT; auto.
  - destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?.
    exists (Val.shru v1 (Vint (Int.add n n1))); split. EvalOp.
    subst. destruct v1; simpl; auto.
    rewrite Heqb.
    destruct (Int.ltu n1 Int.iwordsize) eqn:?; simpl; auto.
    rewrite LT. rewrite Int.add_commut. rewrite Int.shru_shru; auto. rewrite Int.add_commut; auto.
    subst. TrivialExists. econstructor. EvalOp. simpl; eauto. constructor.
    simpl. auto.
  - TrivialExists.
  - intros; TrivialExists. constructor. eauto. constructor. EvalOp. simpl; eauto. constructor.
    auto.
Qed.

Theorem eval_shrimm:
  forall n, unary_constructor_sound (fun a => shrimm a n)
                                    (fun x => Val.shr x (Vint n)).
Proof.
  red; intros until x. unfold shrimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shr_zero; auto.

  destruct (Int.ltu n Int.iwordsize) eqn:LT; simpl.
  destruct (shrimm_match a); intros; InvEval.
  - exists (Vint (Int.shr n1 n)); split. EvalOp.
    simpl. rewrite LT; auto.
  - destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?.
    exists (Val.shr v1 (Vint (Int.add n n1))); split. EvalOp.
    subst. destruct v1; simpl; auto.
    rewrite Heqb.
    destruct (Int.ltu n1 Int.iwordsize) eqn:?; simpl; auto.
    rewrite LT.
    rewrite Int.add_commut. rewrite Int.shr_shr; auto. rewrite Int.add_commut; auto.
    subst. TrivialExists. econstructor. EvalOp. simpl; eauto. constructor.
    simpl. auto.
  - TrivialExists.
  - intros; TrivialExists. constructor. eauto. constructor. EvalOp. simpl; eauto. constructor.
    auto.
Qed.

Lemma eval_mulimm_base:
  forall n, unary_constructor_sound (mulimm_base n) (fun x => Val.mul x (Vint n)).
Proof.
  intros; red; intros; unfold mulimm_base.

  assert (DFL: exists v, eval_expr ge sp e m le (Eop Omul (Eop (Ointconst n) Enil ::: a ::: Enil)) v /\ Val.lessdef (Val.mul x (Vint n)) v).
  TrivialExists. econstructor. EvalOp. simpl; eauto. econstructor. eauto. constructor.
  rewrite Val.mul_commut. auto.

  generalize (Int.one_bits_decomp n).
  generalize (Int.one_bits_range n).
  destruct (Int.one_bits n).
  - intros. TrivialExists.
  - destruct l.
    + intros. rewrite H1. simpl.
      rewrite Int.add_zero.
      replace (Vint (Int.shl Int.one i)) with (Val.shl Vone (Vint i)). rewrite Val.shl_mul.
      apply eval_shlimm. auto. simpl. rewrite H0; auto with coqlib.
    + destruct l.
      intros. rewrite H1. simpl.
      exploit (eval_shlimm i (x :: le) (Eletvar 0) x). constructor; auto. intros [v1 [A1 B1]].
      exploit (eval_shlimm i0 (x :: le) (Eletvar 0) x). constructor; auto. intros [v2 [A2 B2]].
      exploit (eval_add (x :: le)). eexact A1. eexact A2. intros [v [A B]].
      exists v; split. econstructor; eauto.
      rewrite Int.add_zero.
      replace (Vint (Int.add (Int.shl Int.one i) (Int.shl Int.one i0)))
         with (Val.add (Val.shl Vone (Vint i)) (Val.shl Vone (Vint i0))).
      rewrite Val.mul_add_distr_r.
      repeat rewrite Val.shl_mul. eapply Val.lessdef_trans. 2: eauto. apply Val.add_lessdef; auto.
      simpl. repeat rewrite H0; auto with coqlib.
      intros. TrivialExists.
Qed.

Theorem eval_mulimm:
  forall n, unary_constructor_sound (mulimm n) (fun x => Val.mul x (Vint n)).
Proof.
  intros; red; intros until x; unfold mulimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. exists (Vint Int.zero); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int.mul_zero. auto.

  predSpec Int.eq Int.eq_spec n Int.one.
  intros. exists x; split; auto.
  destruct x; simpl; auto. subst n. rewrite Int.mul_one. auto.

  case (mulimm_match a); intros; InvEval.
  - TrivialExists. simpl. rewrite Int.mul_commut; auto.
  - subst. rewrite Val.mul_add_distr_l.
    exploit eval_mulimm_base; eauto. instantiate (1 := n). intros [v' [A1 B1]].
    exploit (eval_addimm (Int.mul n n2) le (mulimm_base n t2) v'). auto. intros [v'' [A2 B2]].
    exists v''; split; auto. eapply Val.lessdef_trans. eapply Val.add_lessdef; eauto.
    rewrite Val.mul_commut; auto.
  - apply eval_mulimm_base; auto.
Qed.

Theorem eval_mul: binary_constructor_sound mul Val.mul.
Proof.
  red; intros until y.
  unfold mul; case (mul_match a b); intros; InvEval.
  rewrite Val.mul_commut. apply eval_mulimm. auto.
  apply eval_mulimm. auto.
  TrivialExists.
Qed.

Theorem eval_mulhs: binary_constructor_sound mulhs Val.mulhs.
Proof.
  red; intros. unfold mulhs; destruct Archi.ptr64 eqn:SF.
- econstructor; split.
  EvalOp. constructor. EvalOp. constructor. EvalOp. constructor. EvalOp. simpl; eauto. 
  constructor. EvalOp. simpl; eauto. constructor. 
  simpl; eauto. constructor. simpl; eauto. constructor. simpl; eauto.
  destruct x; simpl; auto. destruct y; simpl; auto.
  change (Int.ltu (Int.repr 32) Int64.iwordsize') with true; simpl.
  apply Val.lessdef_same. f_equal. 
  transitivity (Int.repr (Z.shiftr (Int.signed i * Int.signed i0) 32)).
  unfold Int.mulhs; f_equal. rewrite Int.Zshiftr_div_two_p by omega. reflexivity.
  apply Int.same_bits_eq; intros n N.
  change Int.zwordsize with 32 in *.
  assert (N1: 0 <= n < 64) by omega.
  rewrite Int64.bits_loword by auto.
  rewrite Int64.bits_shr' by auto.
  change (Int.unsigned (Int.repr 32)) with 32. change Int64.zwordsize with 64.
  rewrite zlt_true by omega.
  rewrite Int.testbit_repr by auto. 
  unfold Int64.mul. rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; omega).
  transitivity (Z.testbit (Int.signed i * Int.signed i0) (n + 32)).
  rewrite Z.shiftr_spec by omega. auto.
  apply Int64.same_bits_eqm. apply Int64.eqm_mult; apply Int64.eqm_unsigned_repr. 
  change Int64.zwordsize with 64; omega.
- TrivialExists.
Qed.

Theorem eval_mulhu: binary_constructor_sound mulhu Val.mulhu.
Proof.
  red; intros. unfold mulhu; destruct Archi.ptr64 eqn:SF.
- econstructor; split.
  EvalOp. constructor. EvalOp. constructor. EvalOp. constructor. EvalOp. simpl; eauto. 
  constructor. EvalOp. simpl; eauto. constructor. 
  simpl; eauto. constructor. simpl; eauto. constructor. simpl; eauto.
  destruct x; simpl; auto. destruct y; simpl; auto.
  change (Int.ltu (Int.repr 32) Int64.iwordsize') with true; simpl.
  apply Val.lessdef_same. f_equal. 
  transitivity (Int.repr (Z.shiftr (Int.unsigned i * Int.unsigned i0) 32)).
  unfold Int.mulhu; f_equal. rewrite Int.Zshiftr_div_two_p by omega. reflexivity.
  apply Int.same_bits_eq; intros n N.
  change Int.zwordsize with 32 in *.
  assert (N1: 0 <= n < 64) by omega.
  rewrite Int64.bits_loword by auto.
  rewrite Int64.bits_shru' by auto.
  change (Int.unsigned (Int.repr 32)) with 32. change Int64.zwordsize with 64.
  rewrite zlt_true by omega.
  rewrite Int.testbit_repr by auto. 
  unfold Int64.mul. rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; omega).
  transitivity (Z.testbit (Int.unsigned i * Int.unsigned i0) (n + 32)).
  rewrite Z.shiftr_spec by omega. auto.
  apply Int64.same_bits_eqm. apply Int64.eqm_mult; apply Int64.eqm_unsigned_repr. 
  change Int64.zwordsize with 64; omega.
- TrivialExists.
Qed.

Theorem eval_andimm:
  forall n, unary_constructor_sound (andimm n) (fun x => Val.and x (Vint n)).
Proof.
  intros; red; intros until x. unfold andimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. exists (Vint Int.zero); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int.and_zero. auto.

  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. exists x; split; auto.
  subst. destruct x; simpl; auto. rewrite Int.and_mone; auto.

  case (andimm_match a); intros.
  - InvEval. TrivialExists. simpl. rewrite Int.and_commut; auto.
  - InvEval. subst. rewrite Val.and_assoc. simpl. rewrite Int.and_commut. TrivialExists.
  - InvEval. TrivialExists. simpl; congruence.
  - TrivialExists.
Qed.

Theorem eval_and: binary_constructor_sound and Val.and.
Proof.
  red; intros until y; unfold and; case (and_match a b); intros; InvEval.
  - rewrite Val.and_commut. apply eval_andimm; auto.
  - apply eval_andimm; auto.
  - (*andn*) TrivialExists; simpl; congruence.
  - (*andn reverse*) rewrite Val.and_commut. TrivialExists; simpl; congruence.
  - TrivialExists.
Qed.

Theorem eval_orimm:
  forall n, unary_constructor_sound (orimm n) (fun x => Val.or x (Vint n)).
Proof.
  intros; red; intros until x. unfold orimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. subst. exists x; split; auto.
  destruct x; simpl; auto. rewrite Int.or_zero; auto.

  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. exists (Vint Int.mone); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int.or_mone. auto.

  destruct (orimm_match a); intros; InvEval.
  - TrivialExists. simpl. rewrite Int.or_commut; auto.
  - subst. rewrite Val.or_assoc. simpl. rewrite Int.or_commut. TrivialExists.
  - InvEval. TrivialExists. simpl; congruence.
  - TrivialExists.
Qed.


Remark eval_same_expr:
  forall a1 a2 le v1 v2,
  same_expr_pure a1 a2 = true ->
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  a1 = a2 /\ v1 = v2.
Proof.
  intros until v2.
  destruct a1; simpl; try (intros; discriminate).
  destruct a2; simpl; try (intros; discriminate).
  case (ident_eq i i0); intros.
  subst i0. inversion H0. inversion H1. split. auto. congruence.
  discriminate.
Qed.

Theorem eval_or: binary_constructor_sound or Val.or.
Proof.
  unfold or; red; intros.
  assert (DEFAULT: exists v, eval_expr ge sp e m le (Eop Oor (a:::b:::Enil)) v /\ Val.lessdef (Val.or x y) v) by TrivialExists.
  assert (ROR: forall v n1 n2,
    Int.add n1 n2 = Int.iwordsize ->
    Val.lessdef (Val.or (Val.shl v (Vint n1)) (Val.shru v (Vint n2)))
                (Val.ror v (Vint n2))).
  { intros. destruct v; simpl; auto.
    destruct (Int.ltu n1 Int.iwordsize) eqn:N1; auto.
    destruct (Int.ltu n2 Int.iwordsize) eqn:N2; auto.
    simpl. rewrite <- Int.or_ror; auto. }
  
  destruct (or_match a b); InvEval.
  
  - rewrite Val.or_commut. apply eval_orimm; auto.
  - apply eval_orimm; auto.
  - predSpec Int.eq Int.eq_spec (Int.add n1 n2) Int.iwordsize; auto.
    destruct (same_expr_pure t1 t2) eqn:?; auto.
    InvEval. exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst.
    exists (Val.ror v0 (Vint n2)); split. EvalOp. apply ROR; auto.
  - predSpec Int.eq Int.eq_spec (Int.add n1 n2) Int.iwordsize; auto.
    destruct (same_expr_pure t1 t2) eqn:?; auto.
    InvEval. exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst.
    exists (Val.ror v1 (Vint n2)); split. EvalOp. rewrite Val.or_commut. apply ROR; auto.
  - (*orn*) TrivialExists; simpl; congruence.
  - (*orn reversed*) rewrite Val.or_commut. TrivialExists; simpl; congruence.
  - apply DEFAULT.
Qed.

Theorem eval_xorimm:
  forall n, unary_constructor_sound (xorimm n) (fun x => Val.xor x (Vint n)).
Proof.
  intros; red; intros until x. unfold xorimm.

  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. exists x; split. auto.
  destruct x; simpl; auto. subst n. rewrite Int.xor_zero. auto.

  intros. destruct (xorimm_match a); intros; InvEval.
  - TrivialExists. simpl. rewrite Int.xor_commut; auto.
  - subst. rewrite Val.xor_assoc. simpl. rewrite Int.xor_commut. 
    predSpec Int.eq Int.eq_spec (Int.xor n2 n) Int.zero.
    + exists v1; split; auto. destruct v1; simpl; auto. rewrite H0, Int.xor_zero; auto.  
    + TrivialExists.
  - TrivialExists.
Qed.

Theorem eval_xor: binary_constructor_sound xor Val.xor.
Proof.
  red; intros until y; unfold xor; case (xor_match a b); intros; InvEval.
  - rewrite Val.xor_commut. apply eval_xorimm; auto.
  - apply eval_xorimm; auto.
  - TrivialExists.
Qed.

Theorem eval_notint: unary_constructor_sound notint Val.notint.
Proof.
  assert (forall v, Val.lessdef (Val.notint (Val.notint v)) v).
    destruct v; simpl; auto. rewrite Int.not_involutive; auto.
    unfold notint; red; intros until x; case (notint_match a); intros; InvEval.
    - TrivialExists; simpl; congruence.
    - TrivialExists; simpl; congruence.
    - TrivialExists; simpl; congruence.
    - TrivialExists; simpl; congruence.
    - TrivialExists; simpl; congruence.
    - TrivialExists; simpl; congruence.
    - TrivialExists.
Qed.

Theorem eval_divs_base:
  forall le a b x y z,
    eval_expr ge sp e m le a x ->
    eval_expr ge sp e m le b y ->
    Val.divs x y = Some z ->
    exists v, eval_expr ge sp e m le (divs_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold divs_base.
  econstructor; split. eapply eval_helper_2; eauto. DeclHelper. UseHelper. auto.
Qed.

Theorem eval_mods_base:
  forall le a b x y z,
    eval_expr ge sp e m le a x ->
    eval_expr ge sp e m le b y ->
    Val.mods x y = Some z ->
    exists v, eval_expr ge sp e m le (mods_base a b) v /\ Val.lessdef z v.
Proof.
Admitted.

Theorem eval_divu_base:
  forall le a b x y z,
    eval_expr ge sp e m le a x ->
    eval_expr ge sp e m le b y ->
    Val.divu x y = Some z ->
    exists v, eval_expr ge sp e m le (divu_base a b) v /\ Val.lessdef z v.
Proof.
Admitted.

Theorem eval_modu_base:
  forall le a b x y z,
    eval_expr ge sp e m le a x ->
    eval_expr ge sp e m le b y ->
    Val.modu x y = Some z ->
    exists v, eval_expr ge sp e m le (modu_base a b) v /\ Val.lessdef z v.
Proof.
Admitted.

Theorem eval_shrximm:
  forall le a n x z,
    eval_expr ge sp e m le a x ->
    Val.shrx x (Vint n) = Some z ->
    exists v, eval_expr ge sp e m le (shrximm a n) v /\ Val.lessdef z v.
Proof.
  intros. unfold shrximm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. exists x; split; auto.
  destruct x; simpl in H0; try discriminate.
  destruct (Int.ltu Int.zero (Int.repr 31)); inv H0.
  replace (Int.shrx i Int.zero) with i. auto.
  unfold Int.shrx, Int.divs. rewrite Int.shl_zero.
  change (Int.signed Int.one) with 1. rewrite Z.quot_1_r. rewrite Int.repr_signed; auto.
  econstructor; split. EvalOp. auto.
(*
  intros. destruct x; simpl in H0; try discriminate. 
  destruct (Int.ltu n (Int.repr 31)) eqn:LTU; inv H0.
  unfold shrximm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  - subst n. exists (Vint i); split; auto.
    unfold Int.shrx, Int.divs. rewrite Z.quot_1_r. rewrite Int.repr_signed. auto.
  - assert (NZ: Int.unsigned n <> 0).
    { intro EQ; elim H0. rewrite <- (Int.repr_unsigned n). rewrite EQ; auto. }
    assert (LT: 0 <= Int.unsigned n < 31) by (apply Int.ltu_inv in LTU; assumption).
    assert (LTU2: Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize = true).
    { unfold Int.ltu; apply zlt_true.
      unfold Int.sub. change (Int.unsigned Int.iwordsize) with 32. 
      rewrite Int.unsigned_repr. omega. 
      assert (32 < Int.max_unsigned) by reflexivity. omega. }
    assert (X: eval_expr ge sp e m le
               (Eop (Oshrimm (Int.repr (Int.zwordsize - 1))) (a ::: Enil))
               (Vint (Int.shr i (Int.repr (Int.zwordsize - 1))))).
    { EvalOp. }
    assert (Y: eval_expr ge sp e m le (shrximm_inner a n)
               (Vint (Int.shru (Int.shr i (Int.repr (Int.zwordsize - 1))) (Int.sub Int.iwordsize n)))).
    { EvalOp. simpl. rewrite LTU2. auto. }
    TrivialExists. 
    constructor. EvalOp. simpl; eauto. constructor. 
    simpl. unfold Int.ltu; rewrite zlt_true. rewrite Int.shrx_shr_2 by auto. reflexivity. 
    change (Int.unsigned Int.iwordsize) with 32; omega.
*)
Qed.

Theorem eval_shl: binary_constructor_sound shl Val.shl.
Proof.
  red; intros until y; unfold shl; case (shl_match b); intros.
  InvEval. apply eval_shlimm; auto.
  TrivialExists.
Qed.

Theorem eval_shr: binary_constructor_sound shr Val.shr.
Proof.
  red; intros until y; unfold shr; case (shr_match b); intros.
  InvEval. apply eval_shrimm; auto.
  TrivialExists.
Qed.

Theorem eval_shru: binary_constructor_sound shru Val.shru.
Proof.
  red; intros until y; unfold shru; case (shru_match b); intros.
  InvEval. apply eval_shruimm; auto.
  TrivialExists.
Qed.

Theorem eval_negf: unary_constructor_sound negf Val.negf.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_absf: unary_constructor_sound absf Val.absf.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_addf: binary_constructor_sound addf Val.addf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_subf: binary_constructor_sound subf Val.subf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_mulf: binary_constructor_sound mulf Val.mulf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_negfs: unary_constructor_sound negfs Val.negfs.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_absfs: unary_constructor_sound absfs Val.absfs.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_addfs: binary_constructor_sound addfs Val.addfs.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_subfs: binary_constructor_sound subfs Val.subfs.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_mulfs: binary_constructor_sound mulfs Val.mulfs.
Proof.
  red; intros; TrivialExists.
Qed.

Section COMP_IMM.

Variable default: comparison -> int -> condition.
Variable intsem: comparison -> int -> int -> bool.
Variable sem: comparison -> val -> val -> val.

Hypothesis sem_int: forall c x y, sem c (Vint x) (Vint y) = Val.of_bool (intsem c x y).
Hypothesis sem_undef: forall c v, sem c Vundef v = Vundef.
Hypothesis sem_eq: forall x y, sem Ceq (Vint x) (Vint y) = Val.of_bool (Int.eq x y).
Hypothesis sem_ne: forall x y, sem Cne (Vint x) (Vint y) = Val.of_bool (negb (Int.eq x y)).
Hypothesis sem_default: forall c v n, sem c v (Vint n) = Val.of_optbool (eval_condition (default c n) (v :: nil) m).

Lemma eval_compimm:
  forall le c a n2 x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (compimm default intsem c a n2) v
         /\ Val.lessdef (sem c x (Vint n2)) v.
Proof.
  intros until x.
  unfold compimm; case (compimm_match c a); intros.
(* constant *)
  - InvEval. rewrite sem_int. TrivialExists. simpl. destruct (intsem c0 n1 n2); auto.
(* eq cmp *)
  - InvEval. inv H. simpl in H5. inv H5.
    destruct (Int.eq_dec n2 Int.zero).
    + subst n2. TrivialExists.
      simpl. rewrite eval_negate_condition.
      destruct (eval_condition c0 vl m); simpl.
      unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_eq; auto.
      rewrite sem_undef; auto.
    + destruct (Int.eq_dec n2 Int.one). subst n2. TrivialExists.
      simpl. destruct (eval_condition c0 vl m); simpl.
      unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_eq; auto.
      rewrite sem_undef; auto.
      exists (Vint Int.zero); split. EvalOp.
      destruct (eval_condition c0 vl m); simpl.
      unfold Vtrue, Vfalse. destruct b; rewrite sem_eq; rewrite Int.eq_false; auto.
      rewrite sem_undef; auto.
(* ne cmp *)
  - InvEval. inv H. simpl in H5. inv H5.
    destruct (Int.eq_dec n2 Int.zero).
    + subst n2. TrivialExists.
      simpl. destruct (eval_condition c0 vl m); simpl.
      unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_ne; auto.
      rewrite sem_undef; auto.
    + destruct (Int.eq_dec n2 Int.one). subst n2. TrivialExists.
      simpl. rewrite eval_negate_condition. destruct (eval_condition c0 vl m); simpl.
      unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_ne; auto.
      rewrite sem_undef; auto.
      exists (Vint Int.one); split. EvalOp.
      destruct (eval_condition c0 vl m); simpl.
      unfold Vtrue, Vfalse. destruct b; rewrite sem_ne; rewrite Int.eq_false; auto.
      rewrite sem_undef; auto.
(* default *)
  - TrivialExists. simpl. rewrite sem_default. auto.
Qed.

Hypothesis sem_swap:
  forall c x y, sem (swap_comparison c) x y = sem c y x.

Lemma eval_compimm_swap:
  forall le c a n2 x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (compimm default intsem (swap_comparison c) a n2) v
         /\ Val.lessdef (sem c (Vint n2) x) v.
Proof.
  intros. rewrite <- sem_swap. eapply eval_compimm; eauto.
Qed.

End COMP_IMM.

Theorem eval_comp:
  forall c, binary_constructor_sound (comp c) (Val.cmp c).
Proof.
  intros; red; intros until y. unfold comp; case (comp_match a b); intros; InvEval.
  eapply eval_compimm_swap; eauto.
  intros. unfold Val.cmp. rewrite Val.swap_cmp_bool; auto.
  eapply eval_compimm; eauto.
  TrivialExists.
Qed.

Theorem eval_compu:
  forall c, binary_constructor_sound (compu c) (Val.cmpu (Mem.valid_pointer m) c).
Proof.
  intros; red; intros until y. unfold compu; case (compu_match a b); intros; InvEval.
  eapply eval_compimm_swap; eauto.
  intros. unfold Val.cmpu. rewrite Val.swap_cmpu_bool; auto.
  eapply eval_compimm; eauto.
  TrivialExists.
Qed.

Theorem eval_compf:
  forall c, binary_constructor_sound (compf c) (Val.cmpf c).
Proof.
  intros; red; intros. unfold compf. TrivialExists.
Qed.

Theorem eval_compfs:
  forall c, binary_constructor_sound (compfs c) (Val.cmpfs c).
Proof.
  intros; red; intros. unfold compfs. TrivialExists.
Qed.

Theorem eval_cast8signed: unary_constructor_sound cast8signed (Val.sign_ext 8).
Proof.
  red; intros until x. unfold cast8signed. case (cast8signed_match a); intros; InvEval.
  TrivialExists.
  TrivialExists.
Qed.

Theorem eval_cast8unsigned: unary_constructor_sound cast8unsigned (Val.zero_ext 8).
Proof.
  red; intros until x. unfold cast8unsigned.
  rewrite Val.zero_ext_and. apply eval_andimm. compute; auto.
Qed.

Theorem eval_cast16signed: unary_constructor_sound cast16signed (Val.sign_ext 16).
Proof.
  red; intros until x. unfold cast16signed. case (cast16signed_match a); intros; InvEval.
  TrivialExists.
  TrivialExists.
Qed.

Theorem eval_cast16unsigned: unary_constructor_sound cast16unsigned (Val.zero_ext 16).
Proof.
  red; intros until x. unfold cast8unsigned.
  rewrite Val.zero_ext_and. apply eval_andimm. compute; auto.
Qed.

Theorem eval_intoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (intoffloat a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intoffloat. TrivialExists.
Qed.

Theorem eval_intuoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intuoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (intuoffloat a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intuoffloat. TrivialExists.
Qed.

Theorem eval_floatofintu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatofintu x = Some y ->
  exists v, eval_expr ge sp e m le (floatofintu a) v /\ Val.lessdef y v.
Proof.
  intros until y; unfold floatofintu. case (floatofintu_match a); intros.
  InvEval. simpl in H0. TrivialExists.
  TrivialExists.
Qed.

Theorem eval_floatofint:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatofint x = Some y ->
  exists v, eval_expr ge sp e m le (floatofint a) v /\ Val.lessdef y v.
Proof.
  intros until y; unfold floatofint. case (floatofint_match a); intros.
  InvEval. simpl in H0. TrivialExists.
  TrivialExists.
Qed.

Theorem eval_intofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (intofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intofsingle. TrivialExists.
Qed.

Theorem eval_singleofint:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.singleofint x = Some y ->
  exists v, eval_expr ge sp e m le (singleofint a) v /\ Val.lessdef y v.
Proof.
  intros; unfold singleofint; TrivialExists.
Qed.

Theorem eval_intuofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intuofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (intuofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intuofsingle. TrivialExists.
Qed.

Theorem eval_singleofintu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.singleofintu x = Some y ->
  exists v, eval_expr ge sp e m le (singleofintu a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intuofsingle. TrivialExists.
Qed.

Theorem eval_singleoffloat: unary_constructor_sound singleoffloat Val.singleoffloat.
Proof.
  red; intros. unfold singleoffloat. TrivialExists.
Qed.

Theorem eval_floatofsingle: unary_constructor_sound floatofsingle Val.floatofsingle.
Proof.
  red; intros. unfold floatofsingle. TrivialExists.
Qed.

Theorem eval_addressing:
  forall le chunk a v b ofs,
  eval_expr ge sp e m le a v ->
  v = Vptr b ofs ->
  match addressing chunk a with (mode, args) =>
    exists vl,
    eval_exprlist ge sp e m le args vl /\
    eval_addressing ge sp mode vl = Some v
  end.
Proof.
  intros until v. unfold addressing; case (addressing_match a); intros; InvEval.
  - exists (@nil val);  split. eauto with evalexpr. simpl. auto.
  - destruct (Archi.pic_code tt).
  + exists (Vptr b ofs0 :: nil); split.
    constructor. EvalOp. simpl. congruence. constructor. simpl. rewrite Ptrofs.add_zero. congruence.
  + exists (@nil val); split. constructor. simpl; auto.
  - exists (v1 :: nil); split. eauto with evalexpr. simpl.
    destruct v1; simpl in H; try discriminate.
  - exists (v1 :: nil); split. eauto with evalexpr. simpl.
    destruct v1; simpl in H; try discriminate. destruct Archi.ptr64 eqn:SF; inv H. 
    simpl. auto.
  - exists (v :: nil);  split. eauto with evalexpr. subst. simpl. rewrite Ptrofs.add_zero; auto.
Qed.

Theorem eval_builtin_arg:
  forall a v,
  eval_expr ge sp e m nil a v ->
  CminorSel.eval_builtin_arg ge sp e m (builtin_arg a) v.
Proof.
  intros until v. unfold builtin_arg; case (builtin_arg_match a); intros.
- InvEval. constructor.
- InvEval. constructor.
- InvEval. constructor.
- InvEval. simpl in H5. inv H5. constructor.
- InvEval. subst v. constructor; auto.
- inv H. InvEval. simpl in H6; inv H6. constructor; auto.
- destruct Archi.ptr64 eqn:SF.
+ constructor; auto.
+ InvEval. replace v with (if Archi.ptr64 then Val.addl v1 (Vint n) else Val.add v1 (Vint n)).
  repeat constructor; auto.
  rewrite SF; auto.
- destruct Archi.ptr64 eqn:SF.
+ InvEval. replace v with (if Archi.ptr64 then Val.addl v1 (Vlong n) else Val.add v1 (Vlong n)).
  repeat constructor; auto.
+ constructor; auto.
- constructor; auto.
Qed.

End CMCONSTR.
