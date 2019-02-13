(** Implementation of the example illustrating how to use ImpDep. *)

Require Export DepExample.
Require Export Impure.ImpIO.
Export Notations.

Require Import ImpDep.

Open Scope impure.

Module P<: ImpParam.

Module R := Pos.

Inductive value_wrap :=
  | Std (v:value)  (* value = DepExample.value *)
  | Mem (m:mem)
  .

Inductive op_wrap :=
  (* constants *)
  | Imm (i:Z)
  (* arithmetic operation *)
  | ARITH (op: arith_op)
  | LOAD
  | STORE
  .

Definition op_eval (op: op_wrap) (l:list value_wrap): option value_wrap :=
  match op, l with
  | Imm i, [] => Some (Std i)
  | ARITH op, [Std v1; Std v2] => Some (Std (arith_op_eval op v1 v2))
  | LOAD, [Mem m; Std base; Std offset] =>
     match (Z.add base offset) with
     | Zpos srce => Some (Std (m srce))
     | _ => None
     end
  | STORE, [Mem m; Std srce; Std base; Std offset] =>
     match (Z.add base offset) with
     | Zpos dest => Some (Mem (assign m dest srce))
     | _ => None
     end
  | _, _ => None
  end.


Definition value:=value_wrap.
Definition op:=op_wrap.


Definition op_eq (o1 o2: op_wrap): ?? bool :=
  match o1, o2 with
  | Imm i1, Imm i2 => phys_eq i1 i2
  | ARITH o1, ARITH o2 => phys_eq o1 o2
  | LOAD, LOAD => RET true
  | STORE, STORE => RET true
  | _, _ => RET false
  end.

Lemma op_eq_correct o1 o2: 
 WHEN op_eq o1 o2 ~> b THEN b=true -> o1 = o2.
Proof.
  destruct o1, o2; wlp_simplify; congruence.
Qed.

End P.


Module L <: ISeqLanguage with Module LP:=P.

Module LP:=P.

Include MkSeqLanguage P.

End L.


Module IDT := ImpDepTree L ImpPosDict.

(** Compilation from DepExample to L *)

Definition the_mem: P.R.t := 1.
Definition reg_map (r: reg): P.R.t := Pos.succ r.

Coercion L.Name: P.R.t >-> L.exp.

Definition comp_op (o:operand): L.exp :=
  match o with
  | Imm i => L.Op (P.Imm i) L.Enil
  | Reg r => reg_map r
  end.

Definition comp_inst (i: inst): L.macro :=
  match i with
  | MOVE dest src => 
     [ (reg_map dest, (comp_op src)) ]
  | ARITH dest op src1 src2 =>
     [ (reg_map dest, L.Op (P.ARITH op) (L.Econs (comp_op src1) (L.Econs (comp_op src2) L.Enil))) ]
  | LOAD dest base offset =>
     [ (reg_map dest, L.Op P.LOAD (L.Econs the_mem (L.Econs (reg_map base) (L.Econs (comp_op offset) L.Enil)))) ]
  | STORE srce base offset =>
     [ (the_mem, L.Op P.STORE (L.Econs the_mem (L.Econs (reg_map srce) (L.Econs (reg_map base) (L.Econs (comp_op offset) L.Enil))))) ]
  | MEMSWAP x base offset =>
     [ (reg_map x, L.Op P.LOAD (L.Econs the_mem (L.Econs (reg_map base) (L.Econs (comp_op offset) L.Enil))));
       (the_mem, L.Old (L.Op P.STORE (L.Econs the_mem (L.Econs (reg_map x) (L.Econs (reg_map base) (L.Econs (comp_op offset) L.Enil)))))) ]
  end.

Fixpoint comp_bblock (p: bblock): L.bblock :=
  match p with
  | nil => nil
  | i::p' => (comp_inst i)::(comp_bblock p')
  end.

(** Correctness proof of the compiler *)

Lemma the_mem_separation: forall r, reg_map r <> the_mem.
Proof.
  intros r; apply Pos.succ_not_1.
Qed.

Lemma reg_map_separation: forall r1 r2, r1 <> r2 -> reg_map r1 <> reg_map r2.
Proof.
  unfold reg_map; intros r1 r2 H1 H2; lapply (Pos.succ_inj r1 r2); auto.
Qed.

Local Hint Resolve the_mem_separation reg_map_separation.

Definition match_state (s: state) (m:L.mem): Prop :=
  m the_mem = P.Mem (sm s)  /\ forall r, m (reg_map r) = P.Std (rm s r).

Definition trans_state (s: state): L.mem :=
  fun x => 
  if Pos.eq_dec x the_mem 
  then P.Mem (sm s)
  else P.Std (rm s (Pos.pred x)).

Lemma match_trans_state (s:state): match_state s (trans_state s).
Proof.
  unfold trans_state; constructor 1.
  - destruct (Pos.eq_dec the_mem the_mem); try congruence.
  - intros r; destruct (Pos.eq_dec (reg_map r) the_mem).
    * generalize the_mem_separation; subst; congruence.
    * unfold reg_map; rewrite Pos.pred_succ. auto.
Qed.

Definition match_option_state (os: option state) (om:option L.mem): Prop :=
  match os with
  | Some s => exists m, om = Some m /\ match_state s m
  | None => om = None
  end.

Lemma comp_op_correct o s m old: match_state s m -> L.exp_eval (comp_op o) m old = Some (P.Std (operand_eval o (rm s))).
Proof.
  destruct 1 as [H1 H2]; destruct o; simpl; auto.
  rewrite H2; auto.
Qed.

Lemma comp_bblock_correct_aux p: forall s m,  match_state s m -> match_option_state (sem_bblock p s) (L.run (comp_bblock p) m).
Proof.
  induction p as [| i p IHp]; simpl; eauto.
  intros s m H; destruct i; simpl; erewrite !comp_op_correct; eauto; simpl.
  - (* MOVE *)
    apply IHp.
    destruct H as [H1 H2]; constructor 1; simpl.
    + rewrite L.assign_diff; auto.
    + unfold assign; intros r; destruct (Pos.eq_dec dest r).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
  - (* ARITH *)
    apply IHp.
    destruct H as [H1 H2]; constructor 1; simpl.
    + rewrite L.assign_diff; auto.
    + unfold assign; intros r; destruct (Pos.eq_dec dest r).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
  - (* LOAD *)
    destruct H as [H1 H2].
    rewrite H1, H2; simpl.
    unfold get_addr.
    destruct (rm s base + operand_eval offset (rm s))%Z; simpl; auto.
    apply IHp.
    constructor 1; simpl.
    + rewrite L.assign_diff; auto.
    + unfold assign; intros r; destruct (Pos.eq_dec dest r).
      * subst; rewrite L.assign_eq; auto.
      * rewrite L.assign_diff; auto.
  - (* STORE *)
    destruct H as [H1 H2].
    rewrite H1, !H2; simpl.
    unfold get_addr.
    destruct (rm s base + operand_eval offset (rm s))%Z; simpl; auto.
    apply IHp.
    constructor 1; simpl; auto.
    + intros r; rewrite L.assign_diff; auto.
  - (* MEMSWAP *)
    destruct H as [H1 H2].
    rewrite H1, !H2; simpl.
    unfold get_addr.
    destruct (rm s base + operand_eval offset (rm s))%Z; simpl; auto.
    apply IHp.
    constructor 1; simpl; auto.
    intros r0; rewrite L.assign_diff; auto.
    unfold assign; destruct (Pos.eq_dec r r0).
    * subst; rewrite L.assign_eq; auto.
    * rewrite L.assign_diff; auto.
Qed.

Lemma comp_bblock_correct p s: match_option_state (sem_bblock p s) (L.run (comp_bblock p) (trans_state s)).
Proof.
  eapply comp_bblock_correct_aux. apply match_trans_state.
Qed.

Lemma state_equiv_from_match (s1 s2: state) (m: L.mem) : 
  (match_state s1 m) -> (match_state s2 m) -> (state_equiv s1 s2).
Proof.
  unfold state_equiv, match_state. intuition.
  - congruence. 
  - assert (P.Std (rm s1 x) = P.Std (rm s2 x)); congruence.
Qed.

Definition match_option_stateX (om:option L.mem) (os:option state): Prop :=
  match om with
  | Some m => exists s, os = Some s /\ match_state s m
  | None => os = None
  end.

Local Hint Resolve state_equiv_from_match.

Lemma res_equiv_from_match (os1 os2: option state) (om: option L.mem): 
  (match_option_state os1 om) -> (match_option_stateX om os2) -> (res_equiv os1 os2).
Proof.
  destruct os1 as [s1|]; simpl.
  - intros [m [H1 H2]]; subst; simpl.
    intros [s2 [H3 H4]]; subst; simpl.
    eapply ex_intro; intuition eauto.
  - intro; subst; simpl; auto.
Qed.


Lemma match_option_state_intro_X om os: match_option_state os om -> match_option_stateX om os.
Proof.
  destruct os as [s | ]; simpl.
  - intros [m [H1 H2]]. subst; simpl. eapply ex_intro; intuition eauto.
  - intros; subst; simpl; auto.
Qed.


Lemma match_from_res_eq om1 om2 os: 
  L.res_eq om2 om1 -> match_option_stateX om1 os ->  match_option_stateX om2 os.
Proof.
  destruct om2 as [m2 | ]; simpl.
  - intros [m [H1 H2]]. subst; simpl.
    intros [s [H3 H4]]; subst; simpl.
    eapply ex_intro; intuition eauto.
    unfold match_state in * |- *.
    intuition (rewrite H2; auto).
  - intros; subst; simpl; auto.
Qed.

Lemma bblock_equiv_reduce p1 p2: L.bblock_equiv (comp_bblock p1) (comp_bblock p2) -> bblock_equiv p1 p2.
Proof.
  unfold L.bblock_equiv, bblock_equiv.
  intros; eapply res_equiv_from_match.
  apply comp_bblock_correct.
  eapply match_from_res_eq. eauto.
  apply match_option_state_intro_X. 
  apply comp_bblock_correct.
Qed.




(* NB: pretty-printing functions below only mandatory for IDT.verb_bblock_eq_test *)
Local Open Scope string_scope.

Definition string_of_name (x: P.R.t): ?? pstring :=
  match x with
  | xH => RET (Str ("the_mem"))
  | _ as x => 
     DO s <~ string_of_Z (Zpos (Pos.pred x)) ;;
     RET ("R" +; s)
  end.

Definition string_of_op (op: P.op): ?? pstring :=
  match op with
  | P.Imm i => 
     DO s <~ string_of_Z i ;;
     RET s
  | P.ARITH ADD => RET (Str "ADD")
  | P.ARITH SUB => RET (Str "SUB")
  | P.ARITH MUL => RET (Str "MUL")
  | P.LOAD => RET (Str "LOAD")
  | P.STORE => RET (Str "STORE")
  end.

Definition bblock_eq_test (verb: bool) (p1 p2: bblock) : ?? bool :=
  if verb then
    IDT.verb_bblock_eq_test string_of_name string_of_op (comp_bblock p1) (comp_bblock p2)
  else
    IDT.bblock_eq_test (comp_bblock p1) (comp_bblock p2).

Local Hint Resolve IDT.bblock_eq_test_correct bblock_equiv_reduce IDT.verb_bblock_eq_test_correct: wlp.


Theorem bblock_eq_test_correct verb p1 p2 : 
  WHEN bblock_eq_test verb p1 p2 ~> b THEN b=true -> bblock_equiv p1 p2.
Proof.
  wlp_simplify.
Qed.
Global Opaque bblock_eq_test.
Hint Resolve bblock_eq_test_correct: wlp.

(* TEST: we can coerce this bblock_eq_test into a pure function (even if this is a little unsafe). *)
(*
Import UnsafeImpure.

Definition pure_eq_test v (p1 p2: bblock) : bool := unsafe_coerce (bblock_eq_test v p1 p2).

Theorem pure_eq_test_correct v p1 p2 : 
   pure_eq_test v p1 p2 = true -> bblock_equiv p1 p2.
Proof.
   unfold pure_eq_test. intros; eapply bblock_eq_test_correct.
   - apply unsafe_coerce_not_really_correct; eauto.
   - eauto.
Qed.
*)