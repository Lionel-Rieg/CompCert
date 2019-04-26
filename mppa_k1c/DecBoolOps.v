Set Implicit Arguments.

Theorem and_dec : forall A B C D : Prop,
    { A } + { B } -> { C } + { D } ->
    { A /\ C } + { (B /\ C) \/ (B /\ D) \/ (A /\ D) }.
Proof.
  intros A B C D AB CD.
  destruct AB; destruct CD.
  - left. tauto.
  - right. tauto.
  - right. tauto.
  - right. tauto.
Qed.

  