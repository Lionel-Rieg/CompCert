(** Syntax and Sequential Semantics of Abstract Basic Blocks.
*)
Require Import ImpPrelude.

Module Type PseudoRegisters.

Parameter t: Type.

Parameter eq_dec: forall (x y: t), { x = y } + { x<>y }.

End PseudoRegisters.


(** * Parameters of the language of Basic Blocks *)
Module Type LangParam.

Declare Module R: PseudoRegisters.

Parameter value: Type.

(** Declare the type of operations *)

Parameter op: Type. (* type of operations *)

Parameter genv: Type. (* environment to be used for evaluating an op *)

Parameter op_eval: genv -> op -> list value -> option value.

End LangParam.



(** * Syntax and (sequential) semantics of "basic blocks" *)
Module MkSeqLanguage(P: LangParam).

Export P.

Local Open Scope list.

Section SEQLANG.

Variable ge: genv.

Definition mem := R.t -> value.

Definition assign (m: mem) (x:R.t) (v: value): mem 
  := fun y => if R.eq_dec x y then v else m y.


(** expressions *)

Inductive exp :=
  | PReg (x:R.t)
  | Op (o:op) (le: list_exp)
  | Old (e: exp)
with list_exp :=
  | Enil
  | Econs (e:exp) (le:list_exp)
  | LOld (le: list_exp)
.

Fixpoint exp_eval (e: exp) (m old: mem): option value :=
  match e with
  | PReg x => Some (m x)
  | Op o le => 
     match list_exp_eval le m old with
     | Some lv => op_eval ge o lv
     | _ => None
     end
  | Old e => exp_eval e old old
  end
with list_exp_eval (le: list_exp) (m old: mem): option (list value) :=
  match le with
  | Enil => Some nil
  | Econs e le' =>
     match exp_eval e m old, list_exp_eval le' m old with
     | Some v, Some lv => Some (v::lv)
     | _, _ => None
     end
  | LOld le => list_exp_eval le old old
  end.

Definition inst := list (R.t * exp). (* = a sequence of assignments *) 

Fixpoint inst_run (i: inst) (m old: mem): option mem :=
  match i with
  | nil => Some m
  | (x, e)::i' =>
     match exp_eval e m old with
     | Some v' => inst_run i' (assign m x v') old
     | None => None
     end
  end.

Definition bblock := list inst.

Fixpoint run (p: bblock) (m: mem): option mem :=
  match p with
  | nil => Some m
  | i::p' =>
     match inst_run i m m with
     | Some m' => run p' m'
     | None => None
     end
  end.

(* A few useful lemma *)
Lemma assign_eq m x v:
  (assign m x v) x = v.
Proof.
  unfold assign. destruct (R.eq_dec x x); try congruence.
Qed.

Lemma assign_diff m x y v:
  x<>y -> (assign m x v) y = m y.
Proof.
  unfold assign. destruct (R.eq_dec x y); try congruence.
Qed.

Lemma assign_skips m x y:
  (assign m x (m x)) y = m y.
Proof.
  unfold assign. destruct (R.eq_dec x y); try congruence.
Qed.

Lemma assign_swap m x1 v1 x2 v2 y:
 x1 <> x2 -> (assign (assign m x1 v1) x2 v2) y = (assign (assign m x2 v2) x1 v1) y.
Proof.
  intros; destruct (R.eq_dec x2 y).
  - subst. rewrite assign_eq, assign_diff; auto. rewrite assign_eq; auto.
  - rewrite assign_diff; auto. 
    destruct (R.eq_dec x1 y).
    + subst; rewrite! assign_eq. auto.
    + rewrite! assign_diff; auto. 
Qed.


(** A small theory of bblock simulation *)

(* equalities on bblock outputs *)
Definition res_eq (om1 om2: option mem): Prop :=
  match om1 with
  | Some m1 => exists m2, om2 = Some m2 /\ forall x, m1 x = m2 x 
  | None => om2 = None
  end.

Scheme exp_mut := Induction for exp Sort Prop
with list_exp_mut := Induction for list_exp Sort Prop.

Lemma exp_equiv e old1 old2:
  (forall x, old1 x = old2 x) ->
  forall m1 m2, (forall x, m1 x = m2 x) -> 
   (exp_eval e m1 old1) = (exp_eval e m2 old2).
Proof.
  intros H1.
  induction e using exp_mut with (P0:=fun l =>  forall m1 m2, (forall x, m1 x = m2 x) -> list_exp_eval l m1 old1 = list_exp_eval l m2 old2); simpl; try congruence; auto.
  - intros; erewrite IHe; eauto.
  - intros; erewrite IHe, IHe0; auto.
Qed.

Definition bblock_simu (p1 p2: bblock): Prop
  := forall m, (run p1 m) <> None -> res_eq (run p1 m) (run p2 m).

Lemma inst_equiv_refl i old1 old2: 
  (forall x, old1 x = old2 x) ->
  forall m1 m2, (forall x, m1 x = m2 x) -> 
  res_eq (inst_run i m1 old1) (inst_run i m2 old2).
Proof.
  intro H; induction i as [ | [x e]]; simpl; eauto.
  intros m1 m2 H1. erewrite exp_equiv; eauto.
  destruct (exp_eval e m2 old2); simpl; auto.
  apply IHi.
  unfold assign; intro y. destruct (R.eq_dec x y); auto. 
Qed.

Lemma bblock_equiv_refl p: forall m1 m2, (forall x, m1 x = m2 x) -> res_eq (run p m1) (run p m2).
Proof.
  induction p as [ | i p']; simpl; eauto.
  intros m1 m2 H; lapply (inst_equiv_refl i m1 m2); auto.
  intros X; lapply (X m1 m2); auto; clear X.
  destruct (inst_run i m1 m1); simpl.
  - intros [m3 [H1 H2]]; rewrite H1; simpl; auto.
  - intros H1; rewrite H1; simpl; auto.
Qed.

Lemma res_eq_sym om1 om2: res_eq om1 om2 -> res_eq om2 om1.
Proof.
  destruct om1; simpl.
  - intros [m2 [H1 H2]]; subst; simpl. eauto.
  - intros; subst; simpl; eauto.
Qed.

Lemma res_eq_trans (om1 om2 om3: option mem): 
  (res_eq om1 om2) -> (res_eq om2 om3) -> (res_eq om1 om3).
Proof.
  destruct om1; simpl.
  - intros [m2 [H1 H2]]; subst; simpl.
    intros [m3 [H3 H4]]; subst; simpl.
    eapply ex_intro; intuition eauto. rewrite H2; auto.
  - intro; subst; simpl; auto.
Qed.

Lemma bblock_simu_alt p1 p2: bblock_simu p1 p2 <-> (forall m1 m2,  (forall x, m1 x = m2 x) -> (run p1 m1)<>None -> res_eq (run p1 m1) (run p2 m2)).
Proof.
  unfold bblock_simu; intuition.
  intros; eapply res_eq_trans. eauto.
  eapply bblock_equiv_refl; eauto.
Qed.


Lemma run_app p1: forall m1 p2,
   run (p1++p2) m1 = 
     match run p1 m1 with 
     | Some m2 => run p2 m2 
     | None => None
     end.
Proof.
   induction p1; simpl; try congruence.
   intros; destruct (inst_run _ _ _); simpl; auto.
Qed.

Lemma run_app_None p1 m1 p2:
   run p1 m1 = None ->
   run (p1++p2) m1 = None.
Proof.
   intro H; rewrite run_app. rewrite H; auto.
Qed.

Lemma run_app_Some p1 m1 m2 p2:
   run p1 m1 = Some m2 ->
   run (p1++p2) m1 = run p2 m2.
Proof.
   intros H; rewrite run_app. rewrite H; auto.
Qed.

End SEQLANG.

Module Terms.

(** terms in the symbolic evaluation 
NB: such a term represents the successive computations in one given pseudo-register
*)

Inductive term :=
  | Input (x:R.t) (hid:hashcode)
  | App (o: op) (l: list_term) (hid:hashcode)
with list_term :=
  | LTnil (hid:hashcode)
  | LTcons (t:term) (l:list_term) (hid:hashcode)
  .

Scheme term_mut := Induction for term Sort Prop
with list_term_mut := Induction for list_term Sort Prop.

Bind Scope pattern_scope with term.
Delimit Scope term_scope with term.
Delimit Scope pattern_scope with pattern.

Notation "[ ]" := (LTnil _) (format "[ ]"): pattern_scope.
Notation "[ x ]" := (LTcons x [] _): pattern_scope.
Notation "[ x ; y ; .. ; z ]" := (LTcons x (LTcons y .. (LTcons z (LTnil _) _) .. _) _): pattern_scope.
Notation "o @ l" := (App o l _) (at level 50, no associativity): pattern_scope.

Import HConsingDefs.

Notation "[ ]" := (LTnil unknown_hid) (format "[ ]"): term_scope.
Notation "[ x ]" := (LTcons x [] unknown_hid): term_scope.
Notation "[ x ; y ; .. ; z ]" := (LTcons x (LTcons y .. (LTcons z (LTnil unknown_hid) unknown_hid) .. unknown_hid) unknown_hid): term_scope.
Notation "o @ l" := (App o l unknown_hid) (at level 50, no associativity): term_scope.

Local Open Scope pattern_scope.

Fixpoint term_eval (ge: genv) (t: term) (m: mem): option value :=
  match t with
  | Input x _ => Some (m x)
  | o @ l =>
     match list_term_eval ge l m with
     | Some v => op_eval ge o v
     | _ => None
     end
  end
with list_term_eval ge (l: list_term) (m: mem) {struct l}: option (list value) :=
  match l with
  | [] => Some nil
  | LTcons t l' _ => 
    match term_eval ge t m, list_term_eval ge l' m with
    | Some v, Some lv => Some (v::lv)
    | _, _ => None
    end
  end.


Definition term_get_hid (t: term): hashcode :=
  match t with
  | Input _ hid => hid
  | App _ _ hid => hid
  end.

Definition list_term_get_hid (l: list_term): hashcode :=
  match l with
  | LTnil hid => hid
  | LTcons _ _ hid => hid
  end.


Definition allvalid ge (l: list term) m := forall t, List.In t l -> term_eval ge t m <> None.

Record pseudo_term: Type := {
  mayfail: list term;
  effect: term
}.

Definition match_pseudo_term (t: term) (pt: pseudo_term) :=
      (forall ge m, term_eval ge t m <> None <-> allvalid ge pt.(mayfail) m)
   /\ (forall ge m0 m1, term_eval ge t m0 = Some m1 -> term_eval ge pt.(effect) m0 = Some m1).

Import ImpCore.Notations.
Local Open Scope impure_scope.

Record reduction (t:term):= {
  result:> ?? pseudo_term;
  result_correct: WHEN result ~> pt THEN match_pseudo_term t pt;
}.
Hint Resolve result_correct: wlp.

Program Definition identity_reduce (t: term): reduction t := {| result := RET {| mayfail := [t]; effect := t |} |}.
Obligation 1.
  unfold match_pseudo_term, allvalid; wlp_simplify; congruence.
Qed.
Global Opaque identity_reduce.

Program Definition failsafe_reduce (is_constant: op -> bool | forall ge o, is_constant o = true -> op_eval ge o nil <> None) (t: term) :=
  match t with
  | Input x _ => {| result := RET {| mayfail := []; effect := t |} |}
  | o @ [] => match is_constant o with 
              | true => {| result := RET {| mayfail := []; effect := t |} |}
              | false => identity_reduce t
              end
  | _ => identity_reduce t
  end.
Obligation 1.
  unfold match_pseudo_term, allvalid; simpl; wlp_simplify; congruence.
Qed.
Obligation 2.
  unfold match_pseudo_term, allvalid; simpl; wlp_simplify.
Qed.
Obligation 3.
  intuition congruence.
Qed.

End Terms.

End MkSeqLanguage.


Module Type SeqLanguage.

Declare Module LP: LangParam.

Include MkSeqLanguage LP.

End SeqLanguage.

