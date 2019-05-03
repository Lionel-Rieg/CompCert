Require Import Coqlib.
Require Import Asmvliw.
Require Import Values.
Require Import Integers.

Definition gpreg_q_list : list gpreg_q :=
R0R1 :: R2R3 :: R4R5 :: R6R7 :: R8R9
:: R10R11 :: R12R13 :: R14R15 :: R16R17 :: R18R19
:: R20R21 :: R22R23 :: R24R25 :: R26R27 :: R28R29
:: R30R31 :: R32R33 :: R34R35 :: R36R37 :: R38R39
:: R40R41 :: R42R43 :: R44R45 :: R46R47 :: R48R49
:: R50R51 :: R52R53 :: R54R55 :: R56R57 :: R58R59
:: R60R61 :: R62R63 :: nil.

Fixpoint gpreg_q_search_rec r0 r1 l :=
  match l with
  | h :: t =>
    let (s0, s1) := gpreg_q_expand h in
    if (gpreg_eq r0 s0) && (gpreg_eq r1 s1)
    then Some h
    else gpreg_q_search_rec r0 r1 t
  | nil => None
  end.

Definition gpreg_q_search (r0 : gpreg) (r1 : gpreg) : option gpreg_q :=
  gpreg_q_search_rec r0 r1 gpreg_q_list.

Parameter print_found_store : forall A : Type, Z -> A -> A.

Fixpoint optimize_body (insns : list basic) : list basic :=
  match insns with
  | nil => nil
  | h0 :: t0 =>
    match t0 with
    | h1 :: t1 =>
        match h0, h1 with
        | (PStoreRRO Psd_a rs0 ra0 ofs0),
          (PStoreRRO Psd_a rs1 ra1 ofs1) =>
          match gpreg_q_search rs0 rs1 with
          | Some rs0rs1 =>
            let zofs0 := Ptrofs.signed ofs0 in
            let zofs1 := Ptrofs.signed ofs1 in
            if (zofs1 =? zofs0 + 8) && (ireg_eq ra0 ra1)
            then let h0' := print_found_store basic zofs0 h0 in
                 (PStore (PStoreQRRO rs0rs1 ra0 ofs0)) :: Pnop :: (optimize_body t1)
            else h0 :: (optimize_body t0)
          | None => h0 :: (optimize_body t0)
          end
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
