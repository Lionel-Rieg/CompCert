Require Export ImpIO.

Import Notations.
Local Open Scope impure.


Axiom string_of_hashcode: hashcode -> ?? caml_string.
Extract Constant string_of_hashcode => "string_of_int".

Axiom hash: forall {A}, A -> ?? hashcode.
Extract Constant hash => "Hashtbl.hash".

(**************************)
(* (Weak) Sets            *)


Import Dict.

Axiom make_dict: forall {A B}, (hash_params A) -> ?? Dict.t A B.
Extract Constant make_dict => "ImpHConsOracles.make_dict".


Module Sets.

Definition t {A} (mod: A -> Prop) := Dict.t A {x | mod x}.

Definition empty {A} (hp: hash_params A) {mod:A -> Prop}: ?? t mod :=
  make_dict hp.

Program Fixpoint add {A} (l: list A) {mod: A -> Prop} (d: t mod): forall {H:forall x, List.In x l -> mod x}, ?? unit :=
  match l with
  | nil => fun H => RET ()
  | x::l' => fun H =>
    d.(set)(x,x);;
    add l' d
  end.

Program Definition create {A} (hp: hash_params A) (l:list A): ?? t (fun x => List.In x l) :=
  DO d <~ empty hp (mod:=fun x => List.In x l);;
  add l (mod:=fun x => List.In x l) d (H:=_);;
  RET d.
Global Opaque create.

Definition is_present {A} (hp: hash_params A) (x:A) {mod} (d:t mod): ?? bool :=
  DO oy <~ (d.(get)) x;;
  match oy with
  | Some y => hp.(test_eq) x (`y)
  | None => RET false
  end.

Local Hint Resolve test_eq_correct: wlp.

Lemma is_present_correct A (hp: hash_params A) x mod (d:t mod):
 WHEN is_present hp x d ~> b THEN b=true -> mod x.
Proof.
  wlp_simplify; subst; eauto.
  - apply proj2_sig.
  - discriminate. 
Qed.
Hint Resolve is_present_correct: wlp.
Global Opaque is_present.

Definition msg_assert_incl: pstring := "Sets.assert_incl".

Fixpoint assert_incl {A} (hp: hash_params A) (l: list A) {mod} (d:t mod): ?? unit :=
  match l with
  | nil => RET ()
  | x::l' =>
    DO b <~ is_present hp x d;;
    if b then
      assert_incl hp l' d
    else (
      hp.(log) x;;
      FAILWITH msg_assert_incl
    )
  end.

Lemma assert_incl_correct A (hp: hash_params A) l mod (d:t mod):
 WHEN assert_incl hp l d ~> _ THEN forall x, List.In x l -> mod x.
Proof.
  induction l; wlp_simplify; subst; eauto.
Qed.
Hint Resolve assert_incl_correct: wlp.
Global Opaque assert_incl.

Definition assert_list_incl {A} (hp: hash_params A) (l1 l2: list A): ?? unit :=
  (* println "";;print("dict_create ");;*)
  DO d <~ create hp l2;;
  (*print("assert_incl ");;*)
  assert_incl hp l1 d.

Lemma assert_list_incl_correct A (hp: hash_params A) l1 l2:
 WHEN assert_list_incl hp l1 l2 ~> _ THEN List.incl l1 l2.
Proof.
  wlp_simplify.
Qed.
Global Opaque assert_list_incl.
Hint Resolve assert_list_incl_correct.

End Sets.

(********************************)
(* (Weak) HConsing              *)


Axiom xhCons: forall {A}, ((A -> A -> ?? bool) * (pre_hashV A -> ?? hashV A)) -> ?? hashConsing A.
Extract Constant xhCons => "ImpHConsOracles.xhCons".

Definition hCons_eq_msg: pstring := "xhCons: hash_eq differs".

Definition hCons {A} (hash_eq: A -> A -> ?? bool) (unknownHash_msg: pre_hashV A -> ?? pstring): ?? (hashConsing A) :=
  DO hco <~ xhCons (hash_eq, fun v => DO s <~ unknownHash_msg v ;; FAILWITH s) ;;
  RET {|
      hC := fun x => 
       DO x' <~ hC hco x ;;
       DO b0 <~ hash_eq (pre_data x) (data x') ;;
       assert_b b0 hCons_eq_msg;;
       RET x';
      hC_known := fun x => 
       DO x' <~ hC_known hco x ;;
       DO b0 <~ hash_eq (pre_data x) (data x') ;;
       assert_b b0 hCons_eq_msg;;
       RET x';
      next_log := next_log hco;
      export := export hco;
      |}.

Lemma hCons_correct: forall A (hash_eq: A -> A -> ?? bool) msg,
  WHEN hCons hash_eq msg ~> hco THEN
    ((forall x y, WHEN hash_eq x y ~> b THEN b=true -> x=y) -> forall x, WHEN hC hco x ~> x' THEN (pre_data x)=(data x'))
 /\ ((forall x y, WHEN hash_eq x y ~> b THEN b=true -> x=y) -> forall x, WHEN hC_known hco x ~> x' THEN (pre_data x)=(data x')).
Proof.
  wlp_simplify.
Qed.
Global Opaque hCons.
Hint Resolve hCons_correct: wlp.

Definition hCons_spec {A} (hco: hashConsing A) :=
  (forall x, WHEN hC hco x ~> x' THEN (pre_data x)=(data x')) /\ (forall x, WHEN hC_known hco x ~> x' THEN (pre_data x)=(data x')).
