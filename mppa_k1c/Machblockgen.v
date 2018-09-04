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


Fixpoint to_bblock_header (c: Mach.code): list label * Mach.code :=
  match c with
  | (Mlabel l)::c' => 
      let (h, c'') := to_bblock_header c' in
      (l::h, c'')
  | _ => (nil, c)
  end.

Definition to_basic_inst(i: Mach.instruction): option basic_inst :=
  match i with
  | Mgetstack ofs ty dst          => Some (MBgetstack ofs ty dst)
  | Msetstack src ofs ty          => Some (MBsetstack src ofs ty)
  | Mgetparam ofs ty dst          => Some (MBgetparam ofs ty dst)
  | Mop       op args res         => Some (MBop       op args res)
  | Mload     chunk addr args dst => Some (MBload     chunk addr args dst)
  | Mstore    chunk addr args src => Some (MBstore    chunk addr args src)
  | _ => None
  end.

Fixpoint to_bblock_body(c: Mach.code): bblock_body * Mach.code :=
  match c with
  | nil => (nil,nil)
  | i::c' =>
    match to_basic_inst i with
    | Some bi =>
       let (p,c'') := to_bblock_body c' in
       (bi::p, c'')
    | None => (nil, c)
    end
  end.


Definition to_cfi (i: Mach.instruction): option control_flow_inst :=
  match i with
  | Mcall sig ros         => Some (MBcall sig ros)
  | Mtailcall sig ros     => Some (MBtailcall sig ros)
  | Mbuiltin ef args res  => Some (MBbuiltin ef args res)
  | Mgoto lbl             => Some (MBgoto lbl)
  | Mcond cond args lbl   => Some (MBcond cond args lbl)
  | Mjumptable arg tbl    => Some (MBjumptable arg tbl)
  | Mreturn               => Some (MBreturn)
  | _ => None
  end.

Definition to_bblock_exit (c: Mach.code): option control_flow_inst * Mach.code :=
  match c with
  | nil => (None,nil)
  | i::c' =>
    match to_cfi i with
    | Some bi as o => (o, c')
    | None => (None, c)
    end
  end.

Inductive code_nature: Set := IsEmpty | IsLabel | IsBasicInst | IsCFI.

Definition get_code_nature (c: Mach.code): code_nature :=
  match c with
  | nil => IsEmpty
  | (Mlabel _)::_ => IsLabel
  | i::_ => match to_basic_inst i with
         | Some _ => IsBasicInst
         | None => IsCFI
         end
  end.

Lemma cn_eqdec (cn1 cn2: code_nature): { cn1=cn2 } + {cn1 <> cn2}.
Proof.
  decide equality.
Qed.

Lemma get_code_nature_nil c: c<>nil -> get_code_nature c <> IsEmpty.
Proof.
  intros H. unfold get_code_nature.
  destruct c; try (contradict H; auto; fail).
  destruct i; discriminate.
Qed.

Lemma get_code_nature_empty c: get_code_nature c = IsEmpty -> c = nil.
Proof.
  intros H. destruct c; auto. exploit (get_code_nature_nil (i::c)); discriminate || auto.
  intro F. contradict F.
Qed.

Lemma to_bblock_header_noLabel c:
  get_code_nature c <> IsLabel ->
  to_bblock_header c = (nil, c).
Proof.
  intros H. destruct c as [|i c]; auto.
  destruct i; simpl; auto.
  contradict H; simpl; auto.
Qed.

Lemma to_bblock_header_wfe c:
  forall h c0,
  to_bblock_header c = (h, c0) ->
  (length c >= length c0)%nat.
Proof.
  induction c as [ |i c]; simpl; intros h c' H.
  - inversion H; subst; clear H; simpl; auto.
  - destruct i; try (inversion H; subst; simpl; auto; fail).
    remember (to_bblock_header c) as bhc; destruct bhc as [h0 c0].
    inversion H; subst.
    lapply (IHc h0 c'); auto.
Qed.

Lemma to_bblock_header_wf c b c0:
  get_code_nature c = IsLabel ->
  to_bblock_header c = (b, c0) ->
  (length c > length c0)%nat.
Proof.
  intros H1 H2; destruct c; [ contradict H1; simpl; discriminate | ].
  destruct i; try discriminate.
  simpl in H2.
  remember (to_bblock_header c) as bh; destruct bh as [h c''].
  inversion H2; subst.
  exploit to_bblock_header_wfe; eauto.
  simpl; omega.
Qed.

Lemma to_bblock_body_noBasic c:
  get_code_nature c <> IsBasicInst ->
  to_bblock_body c = (nil, c).
Proof.
  intros H. destruct c as [|i c]; simpl; auto.
  destruct i; simpl; auto.
  all: contradict H; simpl; auto.
Qed.

Lemma to_bblock_body_wfe c b c0:
  to_bblock_body c = (b, c0) ->
  (length c >= length c0)%nat.
Proof.
  generalize b c0; clear b c0.
  induction c as [|i c].
  - intros b c0 H. simpl in H. inversion H; subst; auto.
  - intros b c0 H. simpl in H. destruct (to_basic_inst i).
    + remember (to_bblock_body c) as tbbc; destruct tbbc as [p c''].
      exploit (IHc p c''); auto. inversion H; subst; simpl; omega.
    + inversion H; subst; auto.
Qed.

(** Attempt to eliminate cons_to_bblock_body *)
(*
Lemma to_bblock_body_basic c:
  get_code_nature c = IsBasicInst ->
  exists i bi b c',
     to_basic_inst i = Some bi
  /\ c = i :: c'
  /\ to_bblock_body c = (bi::b, snd (to_bblock_body c')).
Proof.
  intros H.
  destruct c as [|i c]; try (contradict H; simpl; discriminate).
  destruct i eqn:I; try (contradict H; simpl; discriminate).
  all: simpl; destruct (to_bblock_body c)  as [p c''] eqn:TBBC; repeat (eapply ex_intro); (repeat split);
    simpl; eauto; rewrite TBBC; simpl; eauto.
Qed.

Lemma to_bblock_body_wf c b c0:
  get_code_nature c = IsBasicInst ->
  to_bblock_body c = (b, c0) ->
  (length c > length c0)%nat.
Proof.
  intros H1 H2; exploit to_bblock_body_basic; eauto.
  intros X. destruct X as (i & bi & b' & c' & X1 & X2 & X3).
  exploit to_bblock_body_wfe. eauto. subst. simpl.
  rewrite X3 in H2. inversion H2; clear H2; subst.
  simpl; omega.
Qed.
*)

Inductive cons_to_bblock_body c0: Mach.code -> bblock_body -> Prop :=
  Cons_to_bbloc_body i bi c' b':
    to_basic_inst i = Some bi
    -> to_bblock_body c' = (b', c0)
    -> cons_to_bblock_body c0 (i::c') (bi::b').

Lemma to_bblock_body_IsBasicInst c b c0:
  get_code_nature c = IsBasicInst ->
  to_bblock_body c = (b, c0) ->
  cons_to_bblock_body c0 c b.
Proof.
  intros H1 H2. destruct c; [ contradict H1; simpl; discriminate | ].
  remember (to_basic_inst i) as tbii. destruct tbii.
  - simpl in H2. rewrite <- Heqtbii in H2.
    remember (to_bblock_body c) as tbbc. destruct tbbc as [p1 c1].
    inversion H2. subst. eapply Cons_to_bbloc_body; eauto.
  - destruct i; try discriminate.
Qed.

Lemma to_bblock_body_wf c b c0:
  get_code_nature c = IsBasicInst ->
  to_bblock_body c = (b, c0) ->
  (length c > length c0)%nat.
Proof.
  intros H1 H2; exploit to_bblock_body_IsBasicInst; eauto.
  intros X. destruct X.
  exploit to_bblock_body_wfe; eauto. subst. simpl.
  simpl; omega.
Qed.

Lemma to_bblock_exit_noCFI c:
  get_code_nature c <> IsCFI ->
  to_bblock_exit c = (None, c).
Proof.
  intros H. destruct c as [|i c]; simpl; auto.
  destruct i; simpl; auto.
  all: contradict H; simpl; auto.
Qed.

Lemma to_bblock_exit_wf c b c0:
  get_code_nature c = IsCFI ->
  to_bblock_exit c = (b, c0) ->
  (length c > length c0)%nat.
Proof.
  intros H1 H2. destruct c as [|i c]; try discriminate.
  destruct i; try discriminate;
  unfold to_bblock_header in H2; inversion H2; auto.
Qed.

Lemma to_bblock_exit_wfe c b c0:
  to_bblock_exit c = (b, c0) ->
  (length c >= length c0)%nat.
Proof.
  intros H. destruct c as [|i c].
  - simpl in H. inversion H; subst; clear H; auto.
  - destruct i; try ( simpl in H; inversion H; subst; clear H; auto ).
    all: simpl; auto.
Qed.

Definition to_bblock(c: Mach.code): bblock * Mach.code :=
  let (h,c0) := to_bblock_header c in
  let (bdy, c1) := to_bblock_body c0 in
  let (ext, c2) := to_bblock_exit c1 in
  ({| header := h; body := bdy; exit := ext |}, c2)
  .

Lemma to_bblock_acc_label c l b c':
  to_bblock c = (b, c') ->
  to_bblock (Mlabel l :: c) = ({| header := l::(header b); body := (body b); exit := (exit b) |}, c').
Proof.
  unfold to_bblock; simpl.
  remember (to_bblock_header c) as bhc; destruct bhc as [h c0].
  remember (to_bblock_body c0) as bbc; destruct bbc as [bdy c1].
  remember (to_bblock_exit c1) as bbc; destruct bbc as [ext c2].
  intros H; inversion H; subst; clear H; simpl; auto.
Qed.

Lemma to_bblock_basic_then_label i c bi:
  get_code_nature (i::c) = IsBasicInst ->
  get_code_nature c = IsLabel ->
  to_basic_inst i = Some bi ->
  fst (to_bblock (i::c)) = {| header := nil; body := bi::nil; exit := None |}.
Proof.
  intros H1 H2 H3.
  destruct c as [|i' c]; try (contradict H1; simpl; discriminate).
  destruct i'; try (contradict H1; simpl; discriminate).
  destruct i; simpl in *; inversion H3; subst; auto.
Qed.

Lemma to_bblock_CFI i c cfi:
  get_code_nature (i::c) = IsCFI ->
  to_cfi i = Some cfi ->
  fst (to_bblock (i::c)) = {| header := nil; body := nil; exit := Some cfi |}.
Proof.
  intros H1 H2.
  destruct i; try discriminate.
  all: subst; rewrite <- H2; simpl; auto.
Qed.

Lemma to_bblock_noLabel c:
  get_code_nature c <> IsLabel ->
  fst (to_bblock c) = {|
    header := nil;
    body := body (fst (to_bblock c));
    exit := exit (fst (to_bblock c))
  |}.
Proof.
  intros H.
  destruct c as [|i c]; simpl; auto.
  apply bblock_eq; simpl;
  destruct i; (
      try (
        remember (to_bblock _) as bb;
        unfold to_bblock in *;
        remember (to_bblock_header _) as tbh;
        destruct tbh;
        destruct (to_bblock_body _);
        destruct (to_bblock_exit _);
        subst; simpl; inversion Heqtbh; auto; fail
      )
    || contradict H; simpl; auto ).
Qed.

Lemma to_bblock_body_nil c c':
  to_bblock_body c = (nil, c') ->
  c = c'.
Proof.
  intros H.
  destruct c as [|i c]; [ simpl in *; inversion H; auto |].
  destruct i; try ( simpl in *; remember (to_bblock_body c) as tbc; destruct tbc as [p c'']; inversion H ).
  all: auto.
Qed.

Lemma to_bblock_exit_nil c c':
  to_bblock_exit c = (None, c') ->
  c = c'.
Proof.
  intros H.
  destruct c as [|i c]; [ simpl in *; inversion H; auto |].
  destruct i; try ( simpl in *; remember (to_bblock_exit c) as tbe; destruct tbe as [p c'']; inversion H ).
  all: auto.
Qed.

Lemma to_bblock_label b l c c':
  to_bblock (Mlabel l :: c) = (b, c') ->
  (header b) = l::(tail (header b)) /\ to_bblock c = ({| header:=tail (header b); body := body b; exit := exit b |}, c').
Proof.
  unfold to_bblock; simpl.
  remember (to_bblock_header c) as bhc; destruct bhc as [h c0].
  remember (to_bblock_body c0) as bbc; destruct bbc as [bdy c1].
  remember (to_bblock_exit c1) as bbc; destruct bbc as [ext c2].
  intros H; inversion H; subst; clear H; simpl; auto.
Qed.

Lemma to_bblock_basic c i bi:
  get_code_nature (i::c) = IsBasicInst ->
  to_basic_inst i = Some bi ->
  get_code_nature c <> IsLabel ->
  fst (to_bblock (i::c)) = {|
    header := nil;
    body := bi :: body (fst (to_bblock c));
    exit := exit (fst (to_bblock c))
  |}.
Proof.
  intros.
  destruct c; try (destruct i; inversion H0; subst; simpl; auto; fail).
  apply bblock_eq; simpl.
(* header *)
  + destruct i; simpl; auto; (
      exploit to_bblock_noLabel; [rewrite H; discriminate | intro; rewrite H2; simpl; auto]).
(* body *)
(* FIXME - the proof takes some time to prove.. N² complexity :( *)
  + unfold to_bblock.
    remember (to_bblock_header _) as tbh; destruct tbh.
    remember (to_bblock_body _) as tbb; destruct tbb.
    remember (to_bblock_exit _) as tbe; destruct tbe.
    simpl.
    destruct i; destruct i0.
    all: try (simpl in H1; contradiction).
    all: try discriminate.
    all: try (
    simpl in Heqtbh; inversion Heqtbh; clear Heqtbh; subst;
    simpl in Heqtbb; remember (to_bblock_body c) as tbbc; destruct tbbc;
    inversion Heqtbb; clear Heqtbb; subst; simpl in *; clear H H1;
    inversion H0; clear H0; subst; destruct (to_bblock_body c);
    inversion Heqtbbc; clear Heqtbbc; subst;
    destruct (to_bblock_exit c1); simpl; auto; fail).
(* exit *)
  + unfold to_bblock.
    remember (to_bblock_header _) as tbh; destruct tbh.
    remember (to_bblock_body _) as tbb; destruct tbb.
    remember (to_bblock_exit _) as tbe; destruct tbe.
    simpl.
    destruct i; destruct i0.
    all: try (simpl in H1; contradiction).
    all: try discriminate.
    all: try (
    simpl in Heqtbh; inversion Heqtbh; clear Heqtbh; subst;
    simpl in Heqtbb; remember (to_bblock_body c) as tbbc; destruct tbbc; 
    inversion Heqtbb; clear Heqtbb; subst; simpl in *; clear H H1;
    inversion H0; clear H0; subst; destruct (to_bblock_body c) eqn:TBBC;
    inversion Heqtbbc; clear Heqtbbc; subst;
    destruct (to_bblock_exit c1) eqn:TBBE; simpl;
    inversion Heqtbe; clear Heqtbe; subst; auto; fail).
Qed.

Lemma to_bblock_size_single_label c i:
  get_code_nature (i::c) = IsLabel ->
  size (fst (to_bblock (i::c))) = Datatypes.S (size (fst (to_bblock c))).
Proof.
  intros H.
  destruct i; try discriminate.
  remember (to_bblock c) as bl. destruct bl as [b c'].
  erewrite to_bblock_acc_label; eauto.
  unfold size; simpl.
  auto.
Qed.

Lemma to_bblock_size_label_neqz c:
  get_code_nature c = IsLabel ->
  size (fst (to_bblock c)) <> 0%nat.
Proof.
  destruct c as [ |i c]; try discriminate.
  intros; rewrite to_bblock_size_single_label; auto.
Qed.

Lemma to_bblock_size_basic_neqz c:
  get_code_nature c = IsBasicInst ->
  size (fst (to_bblock c)) <> 0%nat.
Proof.
  intros H. destruct c as [|i c]; try (contradict H; auto; simpl; discriminate).
  destruct i; try (contradict H; simpl; discriminate);
  (
    destruct (get_code_nature c) eqn:gcnc;
    (* Case gcnc is not IsLabel *)
    try (erewrite to_bblock_basic; eauto; [
        unfold size; simpl; auto
      | simpl; auto
      | rewrite gcnc; discriminate
    ]);
    erewrite to_bblock_basic_then_label; eauto; [
        unfold size; simpl; auto
      | simpl; auto
    ]
  ).
Qed.

Lemma to_bblock_size_cfi_neqz c:
  get_code_nature c = IsCFI ->
  size (fst (to_bblock c)) <> 0%nat.
Proof.
  intros H. destruct c as [|i c]; try (contradict H; auto; simpl; discriminate).
  destruct i; discriminate.
Qed.

Lemma to_bblock_size_single_basic c i:
  get_code_nature (i::c) = IsBasicInst ->
  get_code_nature c <> IsLabel ->
  size (fst (to_bblock (i::c))) = Datatypes.S (size (fst (to_bblock c))).
Proof.
  intros.
  destruct i; try (contradict H; simpl; discriminate); try (
    (exploit to_bblock_basic; eauto);
      [remember (to_basic_inst _) as tbi; destruct tbi; eauto |];
    intro; rewrite H1; unfold size; simpl;
    assert ((length (header (fst (to_bblock c)))) = 0%nat);
      exploit to_bblock_noLabel; eauto; intro; rewrite H2; simpl; auto;
    rewrite H2; auto
  ).
Qed.

Lemma to_bblock_wf c b c0:
  c <> nil ->
  to_bblock c = (b, c0) ->
  (length c > length c0)%nat.
Proof.
  intro H; lapply (get_code_nature_nil c); eauto.
  intro H'; remember (get_code_nature c) as gcn.
  unfold to_bblock.
  remember (to_bblock_header c) as p1; eauto.
  destruct p1 as [h c1].
  intro H0.
  destruct gcn.
  - contradict H'; auto.
  - exploit to_bblock_header_wf; eauto.
    remember (to_bblock_body c1) as p2; eauto.
    destruct p2 as [h2 c2].
    exploit to_bblock_body_wfe; eauto.
    remember (to_bblock_exit c2) as p3; eauto.
    destruct p3 as [h3 c3].
    exploit to_bblock_exit_wfe; eauto.
    inversion H0. omega.
  - exploit to_bblock_header_noLabel; eauto. rewrite <- Heqgcn. discriminate.
    intro. rewrite H1 in Heqp1. inversion Heqp1. clear Heqp1. subst.
    remember (to_bblock_body c) as p2; eauto.
    destruct p2 as [h2 c2].
    exploit to_bblock_body_wf; eauto.
    remember (to_bblock_exit c2) as p3; eauto.
    destruct p3 as [h3 c3].
    exploit to_bblock_exit_wfe; eauto.
    inversion H0. omega.
  - exploit to_bblock_header_noLabel; eauto. rewrite <- Heqgcn. discriminate.
    intro. rewrite H1 in Heqp1. inversion Heqp1; clear Heqp1; subst.
    remember (to_bblock_body c) as p2; eauto.
    destruct p2 as [h2 c2].
    exploit (to_bblock_body_noBasic c); eauto. rewrite <- Heqgcn. discriminate.
    intros H2; rewrite H2 in Heqp2; inversion Heqp2; clear Heqp2; subst.
    remember (to_bblock_exit c) as p3; eauto.
    destruct p3 as [h3 c3].
    exploit (to_bblock_exit_wf c h3 c3); eauto.
    inversion H0. omega.
Qed.

Lemma to_bblock_nonil i c0:
  size (fst (to_bblock (i :: c0))) <> 0%nat.
Proof.
  intros H. remember (i::c0) as c. remember (get_code_nature c) as gcnc. destruct gcnc.
  - contradict Heqgcnc. subst. simpl. destruct i; discriminate.
  - eapply to_bblock_size_label_neqz; eauto.
  - eapply to_bblock_size_basic_neqz; eauto.
  - eapply to_bblock_size_cfi_neqz; eauto.
Qed.

Function trans_code (c: Mach.code) { measure length c }: code :=
  match c with
  | nil => nil
  | _ =>
     let (b, c0) := to_bblock c in
     b::(trans_code c0)
  end.
Proof.
  intros; eapply to_bblock_wf; eauto. discriminate.
Qed.

Lemma trans_code_nonil c:
  c <> nil -> trans_code c <> nil.
Proof.
  intros H.
  induction c, (trans_code c) using trans_code_ind; simpl; auto. discriminate.
Qed.

Lemma trans_code_step c b lb0 hb c1 bb c2 eb c3:
  trans_code c = b :: lb0 ->
  to_bblock_header c = (hb, c1) ->
  to_bblock_body c1 = (bb, c2) ->
  to_bblock_exit c2 = (eb, c3) ->
  hb = header b /\ bb = body b /\ eb = exit b /\ trans_code c3 = lb0.
Proof.
  intros.
  induction c, (trans_code c) using trans_code_ind. discriminate. clear IHc0.
  subst. destruct _x as [|i c]; try (contradict y; auto; fail).
  inversion H; subst. clear H. unfold to_bblock in e0.
  remember (to_bblock_header (i::c)) as hd. destruct hd as [hb' c1'].
  remember (to_bblock_body c1') as bd. destruct bd as [bb' c2'].
  remember (to_bblock_exit c2') as be. destruct be as [eb' c3'].
  inversion e0. simpl.
  inversion H0. subst.
  rewrite <- Heqbd in H1. inversion H1. subst.
  rewrite <- Heqbe in H2. inversion H2. subst.
  auto.
Qed.

Lemma trans_code_cfi i c cfi:
  to_cfi i = Some cfi ->
  trans_code (i :: c) = {| header := nil ; body := nil ; exit := Some cfi |} :: trans_code c.
Proof.
  intros. rewrite trans_code_equation. remember (to_bblock _) as tb; destruct tb as [b c0].
  destruct i; try (contradict H; discriminate).
  all: unfold to_bblock in Heqtb; remember (to_bblock_header _) as tbh; destruct tbh as [h c0'];
      remember (to_bblock_body c0') as tbb; destruct tbb as [bdy c1'];
      remember (to_bblock_exit c1') as tbe; destruct tbe as [ext c2]; simpl in *;
      inversion Heqtbh; subst; inversion Heqtbb; subst; inversion Heqtbe; subst;
      inversion Heqtb; subst; rewrite H; auto.
Qed.

(* à finir pour passer des Mach.function au function, etc. *)
Definition trans_function (f: Mach.function) : function :=
  {| fn_sig:=Mach.fn_sig f;
     fn_code:=trans_code (Mach.fn_code f);
     fn_stacksize := Mach.fn_stacksize f;
     fn_link_ofs := Mach.fn_link_ofs f;
     fn_retaddr_ofs := Mach.fn_retaddr_ofs f
 |}.

Definition trans_fundef (f: Mach.fundef) : fundef :=
  transf_fundef trans_function f.

Definition transf_program (src: Mach.program) : program :=
  transform_program trans_fundef src.
