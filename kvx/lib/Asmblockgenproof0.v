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

(** * "block" version of Asmgenproof0

    This module is largely adapted from Asmgenproof0.v of the other backends
    It needs to stand apart because of the block structure, and the distinction control/basic that there isn't in the other backends
    It has similar definitions than Asmgenproof0, but adapted to this new structure *)

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
Require Import Conventions1.
Require Import Axioms.
Require Import Machblockgenproof. (* FIXME: only use to import [is_tail_app] and [is_tail_app_inv] *)
Require Import Asmblockprops.

Module MB:=Machblock.
Module AB:=Asmblock.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma undef_regs_other:
  forall r rl rs,
  (forall r', In r' rl -> r <> r') ->
  undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto.
  rewrite IHrl by auto. rewrite Pregmap.gso; auto.
Qed.

Fixpoint preg_notin (r: preg) (rl: list mreg) : Prop :=
  match rl with
  | nil => True
  | r1 :: nil => r <> preg_of r1
  | r1 :: rl => r <> preg_of r1 /\ preg_notin r rl
  end.

Remark preg_notin_charact:
  forall r rl,
  preg_notin r rl <-> (forall mr, In mr rl -> r <> preg_of mr).
Proof.
  induction rl; simpl; intros.
  tauto.
  destruct rl.
  simpl. split. intros. intuition congruence. auto.
  rewrite IHrl. split.
  intros [A B]. intros. destruct H. congruence. auto.
  auto.
Qed.

Lemma undef_regs_other_2:
  forall r rl rs,
  preg_notin r rl ->
  undef_regs (map preg_of rl) rs r = rs r.
Proof.
  intros. apply undef_regs_other. intros.
  exploit list_in_map_inv; eauto. intros [mr [A B]]. subst.
  rewrite preg_notin_charact in H. auto.
Qed.

(** * Agreement between Mach registers and processor registers *)

Record agree (ms: Mach.regset) (sp: val) (rs: AB.regset) : Prop := mkagree {
  agree_sp: rs#SP = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r, agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall ms sp rs, agree ms sp rs ->
  forall l, Val.lessdef_list (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma sp_val:
  forall ms sp rs, agree ms sp rs -> sp = rs#SP.
Proof.
  intros. destruct H; auto.
Qed.

Lemma ireg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  freg_of r = OK r' ->
  Val.lessdef (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, data_preg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H0; auto. auto.
  intros. rewrite H0; auto. apply preg_of_data.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Mach.Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto. apply not_eq_sym. apply preg_of_not_SP.
  intros. unfold Mach.Regmap.set. destruct (Mach.RegEq.eq r0 r). congruence.
  rewrite H1. auto. apply preg_of_data.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Corollary agree_set_mreg_parallel:
  forall ms sp rs r v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Mach.Regmap.set r v ms) sp (Pregmap.set (preg_of r) v' rs).
Proof.
  intros. eapply agree_set_mreg; eauto. rewrite Pregmap.gss; auto. intros; apply Pregmap.gso; auto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  data_preg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextblock:
  forall ms sp rs b,
  agree ms sp rs -> agree ms sp (nextblock b rs).
Proof.
  intros. unfold nextblock. apply agree_set_other. auto. auto.
Qed.

Lemma agree_set_pair:
  forall sp p v v' ms rs,
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Mach.set_pair p v ms) sp (set_pair (map_rpair preg_of p) v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_set_mreg_parallel; auto.
- apply agree_set_mreg_parallel. apply agree_set_mreg_parallel; auto.
  apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed.

Lemma agree_undef_nondata_regs:
  forall ms sp rl rs,
  agree ms sp rs ->
  (forall r, In r rl -> data_preg r = false) ->
  agree ms sp (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto.
  apply IHrl. apply agree_exten with rs; auto.
  intros. apply Pregmap.gso. red; intros; subst.
  assert (data_preg a = false) by auto. congruence.
  intros. apply H0; auto.
Qed.

Lemma agree_undef_regs:
  forall ms sp rl rs rs',
  agree ms sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Mach.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite <- agree_sp0. apply H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite Mach.undef_regs_same; auto.
  rewrite Mach.undef_regs_other; auto. rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_set_undef_mreg:
  forall ms sp rs r v rl rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Mach.Regmap.set r v (Mach.undef_regs rl ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  apply agree_undef_regs with rs; auto.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' (preg_of r)).
  congruence. auto.
  intros. rewrite Pregmap.gso; auto.
Qed.

Lemma agree_undef_caller_save_regs:
  forall ms sp rs,
  agree ms sp rs ->
  agree (Mach.undef_caller_save_regs ms) sp (undef_caller_save_regs rs).
Proof.
  intros. destruct H. unfold Mach.undef_caller_save_regs, undef_caller_save_regs; split.
- unfold proj_sumbool; rewrite dec_eq_true. auto.
- auto.
- intros. unfold proj_sumbool. rewrite dec_eq_false by (apply preg_of_not_SP). 
  destruct (List.in_dec preg_eq (preg_of r) (List.map preg_of (List.filter is_callee_save all_mregs))); simpl.
+ apply list_in_map_inv in i. destruct i as (mr & A & B). 
  assert (r = mr) by (apply preg_of_injective; auto). subst mr; clear A.
  apply List.filter_In in B. destruct B as [C D]. rewrite D. auto.
+ destruct (is_callee_save r) eqn:CS; auto.
  elim n. apply List.in_map. apply List.filter_In. auto using all_mregs_complete. 
Qed.

Lemma agree_change_sp:
  forall ms sp rs sp',
  agree ms sp rs -> sp' <> Vundef ->
  agree ms sp' (rs#SP <- sp').
Proof.
  intros. inv H. split; auto.
  intros. rewrite Pregmap.gso; auto with asmgen.
Qed.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall ms sp rs m m' l v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Mach.extcall_arg ms m sp l v ->
  exists v', AB.extcall_arg rs m' l v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val; eauto.
  unfold Mach.load_stack in H2.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ H) in A.
  exists v'; split; auto.
  econstructor. eauto. assumption.
Qed.

Lemma extcall_arg_pair_match:
  forall ms sp rs m m' p v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Mach.extcall_arg_pair ms m sp p v ->
  exists v', AB.extcall_arg_pair rs m' p v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1.
- exploit extcall_arg_match; eauto. intros (v' & A & B). exists v'; split; auto. constructor; auto.
- exploit extcall_arg_match. eauto. eauto. eexact H2. intros (v1 & A1 & B1).
  exploit extcall_arg_match. eauto. eauto. eexact H3. intros (v2 & A2 & B2).
  exists (Val.longofwords v1 v2); split. constructor; auto. apply Val.longofwords_lessdef; auto.
Qed.


Lemma extcall_args_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall ll vl,
  list_forall2 (Mach.extcall_arg_pair ms m sp) ll vl ->
  exists vl', list_forall2 (AB.extcall_arg_pair rs m') ll vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros.
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_pair_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall ms m m' sp rs sg args,
  agree ms sp rs -> Mem.extends m m' ->
  Mach.extcall_arguments ms m sp sg args ->
  exists args', AB.extcall_arguments rs m' sg args' /\ Val.lessdef_list args args'.
Proof.
  unfold Mach.extcall_arguments, AB.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

Remark builtin_arg_match:
  forall ge (rs: regset) sp m a v,
  eval_builtin_arg ge (fun r => rs (preg_of r)) sp m a v ->
  eval_builtin_arg ge rs sp m (map_builtin_arg preg_of a) v.
Proof.
  induction 1; simpl; eauto with barg.
Qed.

Lemma builtin_args_match:
  forall ge ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall al vl, eval_builtin_args ge ms sp m al vl ->
  exists vl', eval_builtin_args ge rs sp m' (map (map_builtin_arg preg_of) al) vl'
           /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros; simpl.
  exists (@nil val); split; constructor.
  exploit (@eval_builtin_arg_lessdef _ ge ms (fun r => rs (preg_of r))); eauto.
  intros; eapply preg_val; eauto.
  intros (v1' & A & B).
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto. apply builtin_arg_match; auto.
Qed.

Lemma agree_set_res:
  forall res ms sp rs v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Mach.set_res res v ms) sp (AB.set_res (map_builtin_res preg_of res) v' rs).
Proof.
  induction res; simpl; intros.
- eapply agree_set_mreg; eauto. rewrite Pregmap.gss. auto.
  intros. apply Pregmap.gso; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_lessdef; auto.
  apply Val.loword_lessdef; auto.
Qed.

Lemma set_res_other:
  forall r res v rs,
  data_preg r = false ->
  set_res (map_builtin_res preg_of res) v rs r = rs r.
Proof.
  induction res; simpl; intros.
- apply Pregmap.gso. red; intros; subst r. rewrite preg_of_data in H; discriminate.
- auto.
- rewrite IHres2, IHres1; auto.
Qed.

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


Local Hint Resolve code_tail_0 code_tail_S: core.

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

Lemma size_blocks_pos c: 0 <= size_blocks c.
Proof.
  induction c as [| a l ]; simpl; try omega.
  generalize (size_positive a); omega.
Qed.

Remark code_tail_positive:
  forall fn ofs c,
  code_tail ofs fn c -> 0 <= ofs.
Proof.
  induction 1; intros; simpl.
  - omega.
  - generalize (size_positive bi). omega.
Qed.

Remark code_tail_size:
  forall fn ofs c,
  code_tail ofs fn c -> size_blocks fn = ofs + size_blocks c.
Proof.
  induction 1; intros; simpl; try omega.
Qed.

Remark code_tail_bounds fn ofs c:
  code_tail ofs fn c -> 0 <= ofs <= size_blocks fn.
Proof.
  intro H; 
  exploit code_tail_size; eauto.
  generalize (code_tail_positive _ _ _ H), (size_blocks_pos c).
  omega.
Qed.

Local Hint Resolve code_tail_next: core.

Lemma code_tail_next_int:
  forall fn ofs bi c,
  size_blocks fn <= Ptrofs.max_unsigned ->
  code_tail (Ptrofs.unsigned ofs) fn (bi :: c) ->
  code_tail (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (size bi)))) fn c.
Proof.
  intros. 
  exploit code_tail_size; eauto.
  simpl; generalize (code_tail_positive _ _ _ H0), (size_positive bi), (size_blocks_pos c).
  intros.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr.
  - rewrite Ptrofs.unsigned_repr; eauto.
    omega.
  - rewrite Ptrofs.unsigned_repr; omega.
Qed.

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
  transl_blocks f c false = OK tc ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) tc.

Lemma transl_blocks_tail:
  forall f c1 c2, is_tail c1 c2 ->
  forall tc2 ep2, transl_blocks f c2 ep2 = OK tc2 ->
  exists tc1, exists ep1, transl_blocks f c1 ep1 = OK tc1 /\ is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  exists tc2; exists ep2; split; auto with coqlib.
  monadInv H0. exploit IHis_tail; eauto. intros (tc1 & ep1 & A & B).
  exists tc1; exists ep1; split. auto.
  eapply is_tail_trans with x0; eauto with coqlib.
Qed.

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1; eauto.
  destruct IHis_tail; eauto. 
Qed.

Section RETADDR_EXISTS.

Hypothesis transf_function_inv:
  forall f tf, transf_function f = OK tf ->
  exists tc ep, transl_blocks f (Machblock.fn_code f) ep = OK tc /\ is_tail tc (fn_blocks tf).

Hypothesis transf_function_len:
  forall f tf, transf_function f = OK tf -> size_blocks (fn_blocks tf) <= Ptrofs.max_unsigned.


Lemma return_address_exists:
  forall b f c, is_tail (b :: c) f.(MB.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. destruct (transf_function f) as [tf|] eqn:TF.
  + exploit transf_function_inv; eauto. intros (tc1 & ep1 & TR1 & TL1).
    exploit transl_blocks_tail; eauto. intros (tc2 & ep2 & TR2 & TL2).
    monadInv TR2.
    assert (TL3: is_tail x0 (fn_blocks tf)).
    { apply is_tail_trans with tc1; auto. 
      apply is_tail_trans with (x++x0); auto. eapply is_tail_app.
    }
    exploit is_tail_code_tail. eexact TL3. intros [ofs CT].
    exists (Ptrofs.repr ofs). red; intros.
    rewrite Ptrofs.unsigned_repr. congruence.
    exploit code_tail_bounds; eauto.
    intros; apply transf_function_len in TF. omega.
  + exists Ptrofs.zero; red; intros. congruence.
Qed.

End RETADDR_EXISTS.

(** [transl_code_at_pc pc fb f c ep tf tc] holds if the code pointer [pc] points
  within the Asmblock code generated by translating Machblock function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc (ge: MB.genv):
    val -> block -> MB.function -> MB.code -> bool -> AB.function -> AB.bblocks -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_blocks f c ep = OK tc ->
    code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc.

Remark code_tail_no_bigger:
  forall pos c1 c2, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall fn c pos pos',
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

Lemma return_address_offset_correct:
  forall ge b ofs fb f c tf tc ofs',
  transl_code_at_pc ge (Vptr b ofs) fb f c false tf tc ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros. inv H. red in H0.
  exploit code_tail_unique. eexact H12. eapply H0; eauto. intro.
  rewrite <- (Ptrofs.repr_unsigned ofs).
  rewrite <- (Ptrofs.repr_unsigned ofs').
  congruence.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: bblocks) {struct c} : option bblocks :=
  match c with
  | nil => None
  | bb1 :: bbl => if is_label lbl bb1 then Some c else find_label lbl bbl
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos'
  /\ code_tail (pos' - pos) c c'
  /\ pos <= pos' <= pos + size_blocks c.
Proof.
  induction c.
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  - intros. inv H. exists pos. split; auto. split.
    replace (pos - pos) with 0 by omega. constructor. constructor; try omega.
    generalize (size_blocks_pos c). generalize (size_positive a). omega.
  - intros. generalize (IHc (pos+size a) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + (size a))) + (size a)) by omega.
  constructor. auto. generalize (size_positive a). omega.
Qed.

(** Helper lemmas to reason about
- the "code is tail of" property
- correct translation of labels. *)

Definition tail_nolabel (k c: bblocks) : Prop :=
  is_tail k c /\ forall lbl, find_label lbl c = find_label lbl k.

Lemma tail_nolabel_refl:
  forall c, tail_nolabel c c.
Proof.
  intros; split. apply is_tail_refl. auto.
Qed.

Lemma tail_nolabel_trans:
  forall c1 c2 c3, tail_nolabel c2 c3 -> tail_nolabel c1 c2 -> tail_nolabel c1 c3.
Proof.
  intros. destruct H; destruct H0; split.
  eapply is_tail_trans; eauto.
  intros. rewrite H1; auto.
Qed.

Definition nolabel (b: bblock) :=
  match (header b) with nil => True | _ => False end.

Hint Extern 1 (nolabel _) => exact I : labels.

Lemma tail_nolabel_cons:
  forall b c k,
  nolabel b -> tail_nolabel k c -> tail_nolabel k (b :: c).
Proof.
  intros. destruct H0. split.
  constructor; auto.
  intros. simpl. rewrite <- H1. destruct b as [hd bdy ex]; simpl in *.
  destruct hd as [|l hd]; simpl in *.
  - assert (is_label lbl {| AB.header := nil; AB.body := bdy; AB.exit := ex; AB.correct := correct |} = false).
    { apply is_label_correct_false. simpl header. apply in_nil. }
    rewrite H2. auto.
  - contradiction.
Qed.

Hint Resolve tail_nolabel_refl: labels.

Ltac TailNoLabel :=
  eauto with labels;
  match goal with
  | [ |- tail_nolabel _ (_ :: _) ] => apply tail_nolabel_cons; [auto; exact I | TailNoLabel]
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: assertion_failed = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; TailNoLabel
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H;  TailNoLabel
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; TailNoLabel
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; TailNoLabel
  | _ => idtac
  end.

Remark tail_nolabel_find_label:
  forall lbl k c, tail_nolabel k c -> find_label lbl c = find_label lbl k.
Proof.
  intros. destruct H. auto.
Qed.

Remark tail_nolabel_is_tail:
  forall k c, tail_nolabel k c -> is_tail k c.
Proof.
  intros. destruct H. auto.
Qed.

Lemma exec_body_pc:
  forall ge l rs1 m1 rs2 m2,
  exec_body ge l rs1 m1 = Next rs2 m2 ->
  rs2 PC = rs1 PC.
Proof.
  induction l.
  - intros. inv H. auto.
  - intros until m2. intro EXEB.
    inv EXEB. destruct (exec_basic_instr _ _ _ _) eqn:EBI; try discriminate.
    eapply IHl in H0. rewrite H0.
    erewrite exec_basic_instr_pc; eauto.
Qed.

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: function.

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: list instruction -> regset -> mem ->
                         list instruction -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_basic_instr ge i1 rs1 m1 = Next rs2 m2 ->
      exec_straight ((PBasic i1) ::g c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_basic_instr ge i rs1 m1 = Next rs2 m2 ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight ((PBasic i) :: c) rs1 m1 c' rs3 m3.

Inductive exec_control_rel: option control -> bblock -> regset -> mem ->
                             regset -> mem -> Prop :=
  | exec_control_rel_intro:
      forall rs1 m1 b rs1' ctl rs2 m2,
      rs1' = nextblock b rs1 ->
      exec_control ge fn ctl rs1' m1 = Next rs2 m2 ->
      exec_control_rel ctl b rs1 m1 rs2 m2.

Inductive exec_bblock_rel: bblock -> regset -> mem -> regset -> mem -> Prop :=
  | exec_bblock_rel_intro:
      forall rs1 m1 b rs2 m2,
      exec_bblock ge fn b rs1 m1 = Next rs2 m2 ->
      exec_bblock_rel b rs1 m1 rs2 m2.

Lemma exec_straight_body:
  forall c l rs1 m1 rs2 m2,
  exec_straight c rs1 m1 nil rs2 m2 ->
  code_to_basics c = Some l ->
  exec_body ge l rs1 m1 = Next rs2 m2.
Proof.
  induction c as [|i c].
  - intros until m2. intros EXES CTB. inv EXES.
  - intros until m2. intros EXES CTB. inv EXES.
    + inv CTB. simpl. rewrite H6. auto.
    + inv CTB. destruct (code_to_basics c); try discriminate. inv H0. eapply IHc in H7; eauto.
      rewrite <- H7. simpl. rewrite H1. auto.
Qed.

Lemma exec_straight_body2:
  forall c rs1 m1 c' rs2 m2,
  exec_straight c rs1 m1 c' rs2 m2 ->
  exists body,
     exec_body ge body rs1 m1 = Next rs2 m2
  /\ (basics_to_code body) ++g c' = c.
Proof.
  intros until m2. induction 1.
  - exists (i1::nil). split; auto. simpl. rewrite H. auto.
  - destruct IHexec_straight as (bdy & EXEB & BTC).
    exists (i:: bdy). split; simpl.
    + rewrite H. auto.
    + congruence.
Qed.

Lemma exec_straight_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_step with rs2 m2; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3,
  exec_basic_instr ge i1 rs1 m1 = Next rs2 m2 ->
  exec_basic_instr ge i2 rs2 m2 = Next rs3 m3 ->
  exec_straight (i1 ::g i2 ::g c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_basic_instr ge i1 rs1 m1 = Next rs2 m2 ->
  exec_basic_instr ge i2 rs2 m2 = Next rs3 m3 ->
  exec_basic_instr ge i3 rs3 m3 = Next rs4 m4 ->
  exec_straight (i1 ::g i2 ::g i3 ::g c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** Like exec_straight predicate, but on blocks *)

Inductive exec_straight_blocks: bblocks -> regset -> mem ->
                                bblocks -> regset -> mem -> Prop :=
  | exec_straight_blocks_one:
      forall b1 c rs1 m1 rs2 m2,
      exec_bblock ge fn b1 rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr rs1#PC (Ptrofs.repr (size b1)) ->
      exec_straight_blocks (b1 :: c) rs1 m1 c rs2 m2
  | exec_straight_blocks_step:
      forall b c rs1 m1 rs2 m2 c' rs3 m3,
      exec_bblock ge fn b rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr rs1#PC (Ptrofs.repr (size b)) ->
      exec_straight_blocks c rs2 m2 c' rs3 m3 ->
      exec_straight_blocks (b :: c) rs1 m1 c' rs3 m3.

Lemma exec_straight_blocks_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight_blocks c1 rs1 m1 c2 rs2 m2 ->
  exec_straight_blocks c2 rs2 m2 c3 rs3 m3 ->
  exec_straight_blocks c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_blocks_step with rs2 m2; auto.
  apply exec_straight_blocks_step with rs2 m2; auto.
Qed.

(** Linking exec_straight with exec_straight_blocks *)

Lemma exec_straight_pc:
  forall c c' rs1 m1 rs2 m2,
  exec_straight c rs1 m1 c' rs2 m2 ->
  rs2 PC = rs1 PC.
Proof.
  induction c; intros; try (inv H; fail).
  inv H.
  - eapply exec_basic_instr_pc; eauto.
  - rewrite (IHc c' rs3 m3 rs2 m2); auto.
    erewrite exec_basic_instr_pc; eauto.
Qed.

Lemma regset_same_assign (rs: regset) r:
  rs # r <- (rs r) = rs.
Proof.
  apply functional_extensionality. intros x. destruct (preg_eq x r); subst; Simpl.
Qed.

Lemma exec_straight_through_singleinst:
  forall a b rs1 m1 rs2 m2 rs2' m2' lb,
  bblock_single_inst (PBasic a) = b ->
  exec_straight (a ::g nil) rs1 m1 nil rs2 m2 ->
  nextblock b rs2 = rs2' -> m2 = m2' ->
  exec_straight_blocks (b::lb) rs1 m1 lb rs2' m2'.
Proof.
  intros. subst. constructor 1. unfold exec_bblock. simpl body. erewrite exec_straight_body; eauto.
  simpl. rewrite regset_same_assign. auto.
  simpl; auto. unfold nextblock, incrPC; simpl. Simpl. erewrite exec_straight_pc; eauto.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight_blocks]) correspond to correct Asm executions. *)

Lemma exec_straight_steps_1:
  forall c rs m c' rs' m',
  exec_straight_blocks c rs m c' rs' m' ->
  size_blocks (fn_blocks fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks fn) c ->
  plus step ge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  econstructor; eauto.
  eapply find_bblock_tail. eauto.
  eapply plus_left'.
  econstructor; eauto.
  eapply find_bblock_tail. eauto.
  apply IHexec_straight_blocks with b0 (Ptrofs.add ofs (Ptrofs.repr (size b))).
  auto. rewrite H0. rewrite H3. reflexivity.
  auto.
  apply code_tail_next_int; auto.
  traceEq.
Qed.

Lemma exec_straight_steps_2:
  forall c rs m c' rs' m',
  exec_straight_blocks c rs m c' rs' m' ->
  size_blocks (fn_blocks fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks fn) c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Ptrofs.unsigned ofs') (fn_blocks fn) c'.
Proof.
  induction 1; intros.
  exists (Ptrofs.add ofs (Ptrofs.repr (size b1))). split.
  rewrite H0. rewrite H2. auto.
  apply code_tail_next_int; auto.
  apply IHexec_straight_blocks with (Ptrofs.add ofs (Ptrofs.repr (size b))).
  auto. rewrite H0. rewrite H3. reflexivity. auto.
  apply code_tail_next_int; auto.
Qed.

End STRAIGHTLINE.

(** * Properties of the Machblock call stack *)

Section MATCH_STACK.

Variable ge: MB.genv.

Inductive match_stack: list MB.stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f tf tc,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      transl_code_at_pc ge ra fb f c false tf tc ->
      sp <> Vundef ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Lemma parent_sp_def: forall s, match_stack s -> parent_sp s <> Vundef.
Proof.
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  auto.
Qed.

Lemma parent_ra_def: forall s, match_stack s -> parent_ra s <> Vundef.
Proof.
  induction 1; simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  inv H0. congruence.
Qed.

Lemma lessdef_parent_sp:
  forall s v,
  match_stack s -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

Lemma lessdef_parent_ra:
  forall s v,
  match_stack s -> Val.lessdef (parent_ra s) v -> v = parent_ra s.
Proof.
  intros. inv H0. auto. exploit parent_ra_def; eauto. tauto.
Qed.

End MATCH_STACK.
