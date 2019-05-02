Require Import Coqlib.
Require Import Asmvliw.
Require Import Values.
Require Import Integers.

Parameter print_found_store : forall A : Type, Z -> A -> A.

Fixpoint optimize_body (insns : list basic) : list basic :=
  match insns with
  | nil => nil
  | h0 :: t0 =>
    match t0 with
    | h1 :: t1 =>
        match h0, h1 with
        | (PStoreRRO Psd_a rs0 ra0 (Ofsimm ofs0)),
          (PStoreRRO Psd_a rs1 ra1 (Ofsimm ofs1)) =>
          let zofs0 := Ptrofs.signed ofs0 in
          let zofs1 := Ptrofs.signed ofs1 in
          if zofs1 =? zofs0 + 8
          then let h0' := print_found_store basic zofs0 h0 in
               h0' :: (optimize_body t0)
          else h0 :: (optimize_body t0)
        | _, _ => h0 :: (optimize_body t0)
        end   
    | nil => h0 :: nil
    end
  end.

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
