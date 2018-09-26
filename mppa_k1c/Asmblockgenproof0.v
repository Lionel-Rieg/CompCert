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

Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
(*   destruct b. all: try discriminate.
  inv H1. auto.
 *)Qed.

(* FIXME - Replaced FR by IR for MPPA *)
Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
(*   destruct b. all: try discriminate.
  inv H1. auto.
 *)Qed.


Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

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

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence.
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
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

(* Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.
 *)

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

(* Lemma agree_undef_regs:
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
 *)

(* Lemma agree_undef_regs2:
  forall ms sp rl rs rs',
  agree (Mach.undef_regs rl ms) sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree (Mach.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite <- agree_sp0. apply H0; auto.
  rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
  intros. destruct (In_dec mreg_eq r rl).
  rewrite Mach.undef_regs_same; auto.
  rewrite H0; auto.
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n.
  exploit preg_of_injective; eauto. congruence.
Qed.
 *)

(* Lemma agree_set_undef_mreg:
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
 *)

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

Local Hint Resolve code_tail_next.

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
  transl_blocks f c = OK tc ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) tc.

(* NB: these two lemma should go into [Coqlib.v] *) 
Lemma is_tail_app A (l1: list A): forall l2, is_tail l2 (l1 ++ l2).
Proof.
  induction l1; simpl; auto with coqlib.
Qed.
Hint Resolve is_tail_app: coqlib.

Lemma is_tail_app_inv A (l1: list A): forall l2 l3, is_tail (l1 ++ l2) l3 -> is_tail l2 l3.
Proof.
  induction l1; simpl; auto with coqlib.
  intros l2 l3 H; inversion H; eauto with coqlib.
Qed.
Hint Resolve is_tail_app_inv: coqlib.


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

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1; eauto.
  destruct IHis_tail; eauto. 
Qed.

Section RETADDR_EXISTS.

Hypothesis transf_function_inv:
  forall f tf, transf_function f = OK tf ->
  exists tc, transl_blocks f (Machblock.fn_code f) = OK tc /\ is_tail tc (fn_blocks tf).

Hypothesis transf_function_len:
  forall f tf, transf_function f = OK tf -> size_blocks (fn_blocks tf) <= Ptrofs.max_unsigned.


(* NB: the hypothesis in comment on [b] is not needed in the proof ! *)
Lemma return_address_exists:
  forall b f (* sg ros *) c, (* b.(MB.exit) = Some (MBcall sg ros) -> *) is_tail (b :: c) f.(MB.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. destruct (transf_function f) as [tf|] eqn:TF.
  + exploit transf_function_inv; eauto. intros (tc1 & TR1 & TL1).
    exploit transl_blocks_tail; eauto. intros (tc2 & TR2 & TL2).
    unfold return_address_offset.
    monadInv TR2.
    assert (TL3: is_tail x0 (fn_blocks tf)).
    { apply is_tail_trans with tc1; eauto with coqlib. }
    exploit is_tail_code_tail; eauto.
    intros [ofs CT].
    exists (Ptrofs.repr ofs). intros.
    rewrite Ptrofs.unsigned_repr. congruence.
    exploit code_tail_bounds; eauto.
    intros; apply transf_function_len in TF. omega.
  + exists Ptrofs.zero; red; intros. congruence.
Qed.

End RETADDR_EXISTS.

(** [transl_code_at_pc pc fb f c ep tf tc] holds if the code pointer [pc] points
  within the Asm code generated by translating Mach function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc (ge: MB.genv):
    val -> block -> MB.function -> MB.code -> bool -> AB.function -> AB.bblocks -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_blocks f c = OK tc ->
    code_tail (Ptrofs.unsigned ofs) (fn_blocks tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc.

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: function.

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: bblocks -> regset -> mem ->
                         bblocks -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall b1 c rs1 m1 rs2 m2,
      exec_bblock ge fn b1 rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr (rs1 PC) (Ptrofs.repr (size b1)) ->
      exec_straight (b1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall b c rs1 m1 rs2 m2 c' rs3 m3,
      exec_bblock ge fn b rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.offset_ptr (rs1 PC) (Ptrofs.repr (size b)) ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight (b :: c) rs1 m1 c' rs3 m3.

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
  forall b1 b2 c rs1 m1 rs2 m2 rs3 m3,
  exec_bblock ge fn b1 rs1 m1 = Next rs2 m2 ->
  exec_bblock ge fn b2 rs2 m2 = Next rs3 m3 ->
  rs2#PC = Val.offset_ptr rs1#PC (Ptrofs.repr (size b1)) ->
  rs3#PC = Val.offset_ptr rs2#PC (Ptrofs.repr (size b2)) ->
  exec_straight (b1 :: b2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall b1 b2 b3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_bblock ge fn b1 rs1 m1 = Next rs2 m2 ->
  exec_bblock ge fn b2 rs2 m2 = Next rs3 m3 ->
  exec_bblock ge fn b3 rs3 m3 = Next rs4 m4 ->
  rs2#PC = Val.offset_ptr rs1#PC (Ptrofs.repr (size b1)) ->
  rs3#PC = Val.offset_ptr rs2#PC (Ptrofs.repr (size b2)) ->
  rs4#PC = Val.offset_ptr rs3#PC (Ptrofs.repr (size b3)) ->
  exec_straight (b1 :: b2 :: b3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct Asm executions. *)

Lemma exec_straight_steps_1:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  size_blocks (fn_blocks fn) <= Ptrofs.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Ptrofs.unsigned ofs) (fn_blocks fn) c ->
  plus step ge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  repeat (econstructor; eauto).
  eapply find_bblock_tail. eauto.
  eapply plus_left'.
  repeat (econstructor; eauto).
  eapply find_bblock_tail. eauto.
  apply IHexec_straight with b0 (Ptrofs.add ofs (Ptrofs.repr (size b))).
  auto. rewrite H0. rewrite H3. reflexivity.
  auto.
  apply code_tail_next_int; auto.
  traceEq.
Qed.

Lemma exec_straight_steps_2:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
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
  apply IHexec_straight with (Ptrofs.add ofs (Ptrofs.repr (size b))).
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