Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.
Require Import Mach.
Require Import Linking.
Require Import Machblock.

Inductive Machblock_inst: Type :=
| MB_label (lbl: label) 
| MB_basic (bi: basic_inst)
| MB_cfi   (cfi: control_flow_inst).

Definition trans_inst (i:Mach.instruction) : Machblock_inst :=
  match i with
  | Mcall sig ros         => MB_cfi (MBcall sig ros)
  | Mtailcall sig ros     => MB_cfi (MBtailcall sig ros)
  | Mbuiltin ef args res  => MB_cfi (MBbuiltin ef args res)
  | Mgoto lbl             => MB_cfi (MBgoto lbl)
  | Mcond cond args lbl   => MB_cfi (MBcond cond args lbl)
  | Mjumptable arg tbl    => MB_cfi (MBjumptable arg tbl)
  | Mreturn               => MB_cfi (MBreturn)
  | Mgetstack ofs ty dst          => MB_basic (MBgetstack ofs ty dst)
  | Msetstack src ofs ty          => MB_basic (MBsetstack src ofs ty)
  | Mgetparam ofs ty dst          => MB_basic (MBgetparam ofs ty dst)
  | Mop       op args res         => MB_basic (MBop       op args res)
  | Mload     chunk addr args dst => MB_basic (MBload     chunk addr args dst)
  | Mstore    chunk addr args src => MB_basic (MBstore    chunk addr args src)
  | Mlabel l => MB_label l
  end.

Definition add_to_new_bblock (i:Machblock_inst) : bblock :=
  match i with
  | MB_label l => {| header := l::nil; body := nil; exit := None |}
  | MB_basic i => {| header := nil; body := i::nil; exit := None |}
  | MB_cfi i => {| header := nil; body := nil; exit := Some i |}
  end.

(* ajout d'une instruction en début d'une liste de blocks *)
(* Soit /1\ ajout en tête de block, soit /2\ ajout dans un nouveau block*)
(* bl est vide -> /2\ *)
(* cfi -> /2\ (ajout dans exit)*)
(* basic -> /1\ si header vide, /2\ si a un header *)
(* label -> /1\ (dans header)*)
Definition add_to_code (i:Machblock_inst) (bl:code) : code :=
  match bl with
  | h::bl0 => match i with
              | MB_label l => {| header := l::(header h); body := (body h); exit := (exit h) |}::bl0
              | MB_cfi i0 => add_to_new_bblock(i)::bl
              | MB_basic i0 => match (header h) with
                               |_::_ => (add_to_new_bblock i)::bl
                               | nil => {| header := (header h); body := i0::(body h); exit := (exit h) |}::bl0
                               end
              end
  | _ => (add_to_new_bblock i)::nil
  end.
  
Fixpoint trans_code_rev (c: Mach.code) (bl:code) : code := 
  match c with
  | nil => bl
  | i::c0 =>
    trans_code_rev c0 (add_to_code (trans_inst i) bl)
  end.

Function trans_code (c: Mach.code) : code :=
  trans_code_rev (List.rev_append c nil) nil.

(* à finir pour passer des Mach.function au function, etc. *)
Definition transf_function (f: Mach.function) : function :=
  {| fn_sig:=Mach.fn_sig f;
     fn_code:=trans_code (Mach.fn_code f);
     fn_stacksize := Mach.fn_stacksize f;
     fn_link_ofs := Mach.fn_link_ofs f;
     fn_retaddr_ofs := Mach.fn_retaddr_ofs f
 |}.

Definition transf_fundef (f: Mach.fundef) : fundef :=
  transf_fundef transf_function f.

Definition transf_program (src: Mach.program) : program :=
  transform_program transf_fundef src.
