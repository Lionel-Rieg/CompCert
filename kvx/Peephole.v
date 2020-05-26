(* *************************************************************)
(*                                                             *)
(*             The Compcert verified compiler                  *)
(*                                                             *)
(*           Sylvain Boulmé     Grenoble-INP, VERIMAG          *)
(*           David Monniaux     CNRS, VERIMAG                  *)
(*           Cyril Six          Kalray                         *)
(*                                                             *)
(*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  *)
(*  This file is distributed under the terms of the INRIA      *)
(*  Non-Commercial License Agreement.                          *)
(*                                                             *)
(* *************************************************************)

Require Import Coqlib.
Require Import Asmvliw.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Compopts.

Definition gpreg_q_list : list gpreg_q :=
R0R1 :: R2R3 :: R4R5 :: R6R7 :: R8R9
:: R10R11 :: R12R13 :: R14R15 :: R16R17 :: R18R19
:: R20R21 :: R22R23 :: R24R25 :: R26R27 :: R28R29
:: R30R31 :: R32R33 :: R34R35 :: R36R37 :: R38R39
:: R40R41 :: R42R43 :: R44R45 :: R46R47 :: R48R49
:: R50R51 :: R52R53 :: R54R55 :: R56R57 :: R58R59
:: R60R61 :: R62R63 :: nil.

Definition gpreg_o_list : list gpreg_o :=
R0R1R2R3 :: R4R5R6R7 :: R8R9R10R11 :: R12R13R14R15
:: R16R17R18R19 :: R20R21R22R23 :: R24R25R26R27 :: R28R29R30R31
:: R32R33R34R35 :: R36R37R38R39 :: R40R41R42R43 :: R44R45R46R47
:: R48R49R50R51 :: R52R53R54R55 :: R56R57R58R59 :: R60R61R62R63 :: nil.

Fixpoint gpreg_q_search_rec r0 r1 l :=
  match l with
  | h :: t =>
    let (s0, s1) := gpreg_q_expand h in
    if (gpreg_eq r0 s0) && (gpreg_eq r1 s1)
    then Some h
    else gpreg_q_search_rec r0 r1 t
  | nil => None
  end.

Fixpoint gpreg_o_search_rec r0 r1 r2 r3 l :=
  match l with
  | h :: t =>
    match gpreg_o_expand h with
    | (((s0, s1), s2), s3) =>
      if (gpreg_eq r0 s0) && (gpreg_eq r1 s1) &&
         (gpreg_eq r2 s2) && (gpreg_eq r3 s3)
      then Some h
      else gpreg_o_search_rec r0 r1 r2 r3 t
    end
  | nil => None
  end.

Definition gpreg_q_search (r0 : gpreg) (r1 : gpreg) : option gpreg_q :=
  gpreg_q_search_rec r0 r1 gpreg_q_list.

Definition gpreg_o_search r0 r1 r2 r3 : option gpreg_o :=
  gpreg_o_search_rec r0 r1 r2 r3 gpreg_o_list.

Parameter print_found_store: forall A, Z -> A -> A.

Definition coalesce_octuples := true.

Fixpoint coalesce_mem (insns : list basic) : list basic :=
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
            then
              if coalesce_octuples
              then
                match t1 with
                | (PStoreRRO Psd_a rs2 ra2 ofs2) :: 
                  (PStoreRRO Psd_a rs3 ra3 ofs3) :: t3 =>
                  match gpreg_o_search rs0 rs1 rs2 rs3 with
                  | Some octuple =>
                    let zofs2 := Ptrofs.signed ofs2 in
                    let zofs3 := Ptrofs.signed ofs3 in
                    if (zofs2 =? zofs0 + 16) && (ireg_eq ra0 ra2) &&
                                             (zofs3 =? zofs0 + 24) && (ireg_eq ra0 ra3)
                    then (PStore (PStoreORRO octuple ra0 ofs0)) :: Pnop :: Pnop :: Pnop :: (coalesce_mem t3)
                    else (PStore (PStoreQRRO rs0rs1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
                  | None => (PStore (PStoreQRRO rs0rs1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
                  end
                | _ => (PStore (PStoreQRRO rs0rs1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
                end
              else (PStore (PStoreQRRO rs0rs1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
            else h0 :: (coalesce_mem t0)
          | None => h0 :: (coalesce_mem t0)
          end
            
        | (PLoad (PLoadRRO TRAP Pld_a rd0 ra0 ofs0)),
          (PLoad (PLoadRRO TRAP Pld_a rd1 ra1 ofs1)) =>
          match gpreg_q_search rd0 rd1 with
          | Some rd0rd1 =>
            let zofs0 := Ptrofs.signed ofs0 in
            let zofs1 := Ptrofs.signed ofs1 in
            if (zofs1 =? zofs0 + 8) && (ireg_eq ra0 ra1) && negb (ireg_eq ra0 rd0)
            then
              if coalesce_octuples
              then
                match t1 with
                | (PLoad (PLoadRRO TRAP Pld_a rd2 ra2 ofs2)) :: 
                  (PLoad (PLoadRRO TRAP Pld_a rd3 ra3 ofs3)) :: t3 =>
                  match gpreg_o_search rd0 rd1 rd2 rd3 with
                  | Some octuple =>
                    let zofs2 := Ptrofs.signed ofs2 in
                    let zofs3 := Ptrofs.signed ofs3 in
                    if (zofs2 =? zofs0 + 16) && (ireg_eq ra0 ra2) &&
                       (zofs3 =? zofs0 + 24) && (ireg_eq ra0 ra3) &&
                       negb (ireg_eq ra0 rd1) && negb (ireg_eq ra0 rd2)
                    then (PLoad (PLoadORRO octuple ra0 ofs0)) :: Pnop :: Pnop :: Pnop :: (coalesce_mem t3)
                    else (PLoad (PLoadQRRO rd0rd1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
                  | None  => (PLoad (PLoadQRRO rd0rd1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
                  end
                | _ =>  (PLoad (PLoadQRRO rd0rd1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
                end
              else (PLoad (PLoadQRRO rd0rd1 ra0 ofs0)) :: Pnop :: (coalesce_mem t1)
            else h0 :: (coalesce_mem t0)
          | None => h0 :: (coalesce_mem t0)
          end
        | _, _ => h0 :: (coalesce_mem t0)
        end   
    | nil => h0 :: nil
    end
  end.

Definition optimize_body (insns : list basic) :=
  if Compopts.optim_coalesce_mem tt
  then coalesce_mem insns
  else insns.

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
