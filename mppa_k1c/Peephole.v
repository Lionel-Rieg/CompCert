Require Import Asmvliw.

Definition optimize_body (insns : list basic) := insns.

Program Definition optimize_bblock (bb : bblock) :=
  let optimized := optimize_body (body bb) in
  let wf_ok := wf_bblockb optimized (exit bb) in
  {| header := header bb;
     body := if wf_ok then optimized else (body bb);
     exit := exit bb |}.
Next Obligation.
  destruct (wf_bblockb (optimize_body (body bb))) eqn:Rwf.
  - rewrite Rwf. simpl. trivial.
  - exact (correct bb).
Qed.
