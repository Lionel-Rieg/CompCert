(** Syntax and Sequential Semantics of Abstract Basic Blocks.
*)


Module Type ResourceNames.

Parameter t: Type.

Parameter eq_dec: forall (x y: t), { x = y } + { x<>y }.

End ResourceNames.


(** * Parameters of the language of Basic Blocks *)
Module Type LangParam.

Declare Module R: ResourceNames.

Parameter value: Type.

(** Declare the type of operations *)

Parameter op: Type. (* type of operations *)

(* NB: possible generalization
 - relation after/before.
*)
Parameter op_eval: op -> list value -> option value.

End LangParam.



(** * Syntax and (sequential) semantics of "basic blocks" *)
Module MkSeqLanguage(P: LangParam).

Export P.

Local Open Scope list.

Definition mem := R.t -> value.

Definition assign (m: mem) (x:R.t) (v: value): mem 
  := fun y => if R.eq_dec x y then v else m y.

Inductive exp :=
  | Name (x:R.t)
  | Op (o:op) (le: list_exp)
  | Old (e: exp)
with list_exp :=
  | Enil
  | Econs (e:exp) (le:list_exp)
  | LOld (le: list_exp)
  .

Fixpoint exp_eval (e: exp) (m old: mem): option value :=
  match e with
  | Name x => Some (m x)
  | Op o le => 
     match list_exp_eval le m old with
     | Some lv => op_eval o lv
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

Definition macro := list (R.t * exp). (* = a sequence of assignments *) 

Fixpoint macro_run (i: macro) (m old: mem): option mem :=
  match i with
  | nil => Some m
  | (x, e)::i' =>
     match exp_eval e m old with
     | Some v' => macro_run i' (assign m x v') old
     | None => None
     end
  end.

Definition bblock := list macro.

Fixpoint run (p: bblock) (m: mem): option mem :=
  match p with
  | nil => Some m
  | i::p' =>
     match macro_run i m m with
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


(** A small theory of bblockram equality *)

(* equalities on bblockram outputs *)
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

Definition bblock_equiv (p1 p2: bblock): Prop
  := forall m, res_eq (run p1 m) (run p2 m).

Lemma alt_macro_equiv_refl i old1 old2: 
  (forall x, old1 x = old2 x) ->
  forall m1 m2, (forall x, m1 x = m2 x) -> 
  res_eq (macro_run i m1 old1) (macro_run i m2 old2).
Proof.
  intro H; induction i as [ | [x e]]; simpl; eauto.
  intros m1 m2 H1. erewrite exp_equiv; eauto.
  destruct (exp_eval e m2 old2); simpl; auto.
  apply IHi.
  unfold assign; intro y. destruct (R.eq_dec x y); auto. 
Qed.

Lemma alt_bblock_equiv_refl p: forall m1 m2, (forall x, m1 x = m2 x) -> res_eq (run p m1) (run p m2).
Proof.
  induction p as [ | i p']; simpl; eauto.
  intros m1 m2 H; lapply (alt_macro_equiv_refl i m1 m2); auto.
  intros X; lapply (X m1 m2); auto; clear X.
  destruct (macro_run i m1 m1); simpl.
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

Lemma bblock_equiv_alt p1 p2: bblock_equiv p1 p2 <-> (forall m1 m2,  (forall x, m1 x = m2 x) -> res_eq (run p1 m1) (run p2 m2)).
Proof.
  unfold bblock_equiv; intuition.
  intros; eapply res_eq_trans. eapply alt_bblock_equiv_refl; eauto.
  eauto.
Qed.
 
End MkSeqLanguage.


Module Type SeqLanguage.

Declare Module LP: LangParam.

Include MkSeqLanguage LP.

End SeqLanguage.

