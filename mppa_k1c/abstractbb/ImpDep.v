(** Dependency Graph of Abstract Basic Blocks

using imperative hash-consing technique in order to get a linear equivalence test.

*)

Require Export Impure.ImpHCons.
Export Notations.

Require Export DepTreeTheory.

Require Import PArith.


Local Open Scope impure.

Import ListNotations.
Local Open Scope list_scope.


Module Type ImpParam.

Include LangParam.

Parameter op_eq: op -> op -> ?? bool.

Parameter op_eq_correct: forall o1 o2, 
 WHEN op_eq o1 o2 ~> b THEN
  b=true -> o1 = o2.

End ImpParam.


Module Type ISeqLanguage.

Declare Module LP: ImpParam.

Include MkSeqLanguage LP.

End ISeqLanguage.


Module Type ImpDict.

Include PseudoRegDictionary.

Parameter eq_test: forall {A}, t A -> t A -> ?? bool.

Parameter eq_test_correct: forall A (d1 d2: t A),
 WHEN eq_test d1 d2 ~> b THEN
  b=true -> forall x, get d1 x = get d2 x.

(* NB: we could also take an eq_test on R.t (but not really useful with "pure" dictionaries  *)


(* only for debugging *)
Parameter not_eq_witness: forall {A}, t A -> t A -> ?? option R.t.

End ImpDict.

Module ImpDepTree (L: ISeqLanguage) (Dict: ImpDict with Module R:=L.LP.R).

Module DT := DepTree L Dict.

Import DT.

Section CanonBuilding.

Variable hC_tree: pre_hashV tree -> ?? hashV tree.
Hypothesis hC_tree_correct: forall t, WHEN hC_tree t ~> t' THEN pre_data t=data t'.

Variable hC_list_tree: pre_hashV list_tree -> ?? hashV list_tree.
Hypothesis hC_list_tree_correct: forall t, WHEN hC_list_tree t ~> t' THEN pre_data t=data t'.

Variable ge: genv.

(* First, we wrap constructors for hashed values !*)

Local Open Scope positive.
Local Open Scope list_scope.

Definition hTname (x:R.t) (debug: option pstring): ?? hashV tree :=
   DO hc <~ hash 1;;
   DO hv <~ hash x;;
   hC_tree {| pre_data:=Tname x; hcodes :=[hc;hv]; debug_info := debug |}.

Lemma hTname_correct x dbg: 
  WHEN hTname x dbg ~> t THEN (data t)=(Tname x).
Proof.
  wlp_simplify.
Qed.
Global Opaque hTname.
Hint Resolve hTname_correct: wlp.

Definition hTop (o:op) (l: hashV list_tree) (debug: option pstring) : ?? hashV tree :=
   DO hc <~ hash 2;; 
   DO hv <~ hash o;;
   hC_tree {| pre_data:=Top o (data l); 
              hcodes:=[hc;hv;hid l]; 
              debug_info := debug  |}.

Lemma hTop_correct o l dbg : 
  WHEN hTop o l dbg ~> t THEN (data t)=(Top o (data l)).
Proof.
  wlp_simplify.
Qed.
Global Opaque hTop.
Hint Resolve hTop_correct: wlp.

Definition hTerase (t1 t2: hashV tree) (debug: option pstring): ?? hashV tree :=
   DO hc <~ hash 3;; 
   hC_tree {| pre_data:=Terase (data t1) (data t2); 
              hcodes:=[hc;hid t1; hid t2]; debug_info := debug |}.

Lemma hTerase_correct t1 t2 dbg: 
  WHEN hTerase t1 t2 dbg ~> t THEN (data t)=(Terase (data t1) (data t2)).
Proof.
  wlp_simplify.
Qed.
Global Opaque hTerase.
Hint Resolve hTerase_correct: wlp.

Definition hTnil (_: unit): ?? hashV list_tree :=
   hC_list_tree {| pre_data:=Tnil; hcodes := nil; debug_info := None |} .

Lemma hTnil_correct x: 
  WHEN hTnil x ~> l THEN (data l)=Tnil.
Proof.
  wlp_simplify.
Qed.
Global Opaque hTnil.
Hint Resolve hTnil_correct: wlp.


Definition hTcons (t: hashV tree) (l: hashV list_tree): ?? hashV list_tree :=
   hC_list_tree {| pre_data:=Tcons (data t) (data l); hcodes := [hid t; hid l]; debug_info := None |}.

Lemma hTcons_correct t l: 
  WHEN hTcons t l ~> l' THEN (data l')=Tcons (data t) (data l).
Proof.
  wlp_simplify.
Qed.
Global Opaque hTcons.
Hint Resolve hTcons_correct: wlp.

(* Second, we use these hashed constructors ! *)


Definition hdeps:= Dict.t (hashV tree).

(* pseudo deps_get *)
Definition pdeps_get (d:hdeps) x : tree := 
   match Dict.get d x with 
   | None => Tname x
   | Some t => (data t)
   end.

Definition hdeps_get (d:hdeps) x dbg : ?? hashV tree := 
   match Dict.get d x with 
   | None => hTname x dbg
   | Some t => RET t
   end.

Lemma hdeps_get_correct (d:hdeps) x dbg:
  WHEN hdeps_get d x dbg ~> t THEN (data t) = pdeps_get d x.
Proof.
  unfold hdeps_get, pdeps_get; destruct (Dict.get d x); wlp_simplify.
Qed.
Global Opaque hdeps_get.
Hint Resolve hdeps_get_correct: wlp.

Fixpoint hexp_tree (e: exp) (d od: hdeps) (dbg: option pstring) : ?? hashV tree :=
  match e with
  | PReg x => hdeps_get d x dbg
  | Op o le =>
     DO lt <~ hlist_exp_tree le d od;; 
     hTop o lt dbg
  | Old e => hexp_tree e od od dbg
  end
with hlist_exp_tree (le: list_exp) (d od: hdeps): ?? hashV list_tree :=
  match le with
  | Enil => hTnil tt
  | Econs e le' => 
     DO t <~ hexp_tree e d od None;;
     DO lt <~ hlist_exp_tree le' d od;;
     hTcons t lt
  | LOld le => hlist_exp_tree le od od
  end.

Lemma hexp_tree_correct_x e od1 od2:
  (forall x, pdeps_get od1 x = deps_get od2 x) ->
 forall d1 d2 dbg,
  (forall x, pdeps_get d1 x = deps_get d2 x) ->
  WHEN hexp_tree e d1 od1 dbg ~> t THEN data t = exp_tree e d2 od2.
Proof.
  intro H.
  induction e using exp_mut with (P0:=fun le =>  forall d1 d2,
     (forall x, pdeps_get d1 x = deps_get d2 x) ->
     WHEN hlist_exp_tree le d1 od1 ~> lt THEN data lt = list_exp_tree le d2 od2); simpl; wlp_simplify; congruence.
Qed.
Global Opaque hexp_tree.

Lemma hexp_tree_correct e d1 od1 dbg:
  WHEN hexp_tree e d1 od1 dbg ~> t THEN forall od2 d2, (forall x, pdeps_get od1 x = deps_get od2 x) -> (forall x, pdeps_get d1 x = deps_get d2 x) -> data t = exp_tree e d2 od2.
Proof.
  intros t H od2 d2 H1 H2; apply (hexp_tree_correct_x e od1 od2 H1 d1 d2 dbg H2 t H). 
Qed.
Hint Resolve hexp_tree_correct: wlp.

Variable debug_assign: R.t -> ?? option pstring.

Fixpoint hinst_deps (i: inst) (d od: hdeps): ?? hdeps :=
  match i with
  | nil => RET d
  | (x, e)::i' =>
     DO dbg <~ debug_assign x;;
     DO t0 <~ hdeps_get d x None;;
     DO v' <~ (if failsafe (data t0) 
      then 
        hexp_tree e d od dbg 
      else
        DO t1 <~ hexp_tree e d od None;; 
        hTerase t1 t0 dbg);;
     hinst_deps i' (Dict.set d x v') od
  end.

Lemma pset_spec_eq d x t:
  pdeps_get (Dict.set d x t) x = (data t).
Proof.
  unfold pdeps_get; rewrite Dict.set_spec_eq; simpl; auto.
Qed.

Lemma pset_spec_diff d x y t:
  x <> y -> pdeps_get (Dict.set d x t) y = pdeps_get d y.
Proof.
 unfold pdeps_get; intros; rewrite Dict.set_spec_diff; simpl; auto.
Qed.

Lemma pempty_spec x: pdeps_get Dict.empty x = Tname x.
Proof.
 unfold pdeps_get; rewrite Dict.empty_spec; simpl; auto.
Qed.

Hint Rewrite pset_spec_eq pempty_spec: dict_rw.


Lemma hinst_deps_correct i: forall d1 od1,
  WHEN hinst_deps i d1 od1 ~> d1' THEN
    forall od2 d2, (forall x, pdeps_get od1 x = deps_get od2 x) ->
    (forall x, pdeps_get d1 x = deps_get d2 x) -> 
    forall x, pdeps_get d1' x = deps_get (inst_deps i d2 od2) x.
Proof.
  induction i; simpl; wlp_simplify.
  + cutrewrite (failsafe (deps_get d2 a0) = failsafe (data exta0)). 
    - erewrite H0, H2; simpl; eauto. clear exta2 Hexta2 H2; auto.
      intros x0; destruct (R.eq_dec a0 x0).
      * subst. autorewrite with dict_rw. rewrite set_spec_eq. erewrite H1; eauto.
      * rewrite set_spec_diff, pset_spec_diff; auto.
    - rewrite H, H4; auto.
  + cutrewrite (failsafe (deps_get d2 a0) = failsafe (data exta0)).
    - erewrite H0, H3; simpl; eauto. clear exta3 Hexta3 H3; auto.
      intros x0; destruct (R.eq_dec a0 x0).
      * subst; autorewrite with dict_rw. rewrite H2.
        erewrite H, H1; eauto. rewrite set_spec_eq. congruence.
      * rewrite set_spec_diff, pset_spec_diff; auto.
   - rewrite H, H5; auto.
Qed.
Global Opaque hinst_deps.
Hint Resolve hinst_deps_correct: wlp.

(* logging info: we log the number of inst-instructions passed ! *)
Variable log: unit -> ?? unit. 

Fixpoint hbblock_deps_rec (p: bblock) (d: hdeps): ?? hdeps :=
  match p with
  | nil => RET d
  | i::p' =>
     log tt;;
     DO d' <~ hinst_deps i d d;;
     hbblock_deps_rec p' d'
  end.

Lemma hbblock_deps_rec_correct p: forall d1,
  WHEN hbblock_deps_rec p d1 ~> d1' THEN
    forall d2, (forall x, pdeps_get d1 x = deps_get d2 x) -> forall x, pdeps_get d1' x = deps_get (bblock_deps_rec p d2) x.
Proof.
  induction p; simpl; wlp_simplify.
Qed.
Global Opaque hbblock_deps_rec.
Hint Resolve hbblock_deps_rec_correct: wlp.


Definition hbblock_deps: bblock -> ?? hdeps
 := fun p => hbblock_deps_rec p Dict.empty.

Lemma hbblock_deps_correct p:
  WHEN hbblock_deps p ~> d1 THEN forall x, pdeps_get d1 x = deps_get (bblock_deps p) x.
Proof.
  unfold bblock_deps; wlp_simplify. erewrite H; eauto.
  intros; autorewrite with dict_rw; auto. rewrite empty_spec. reflexivity.
Qed.
Global Opaque hbblock_deps.

End CanonBuilding.

(* Now, we build the hash-Cons value from a "hash_eq".

Informal specification: 
  [hash_eq] must be consistent with the "hashed" constructors defined above.

We expect that pre_hashV values in the code of these "hashed" constructors verify:

  (hash_eq (pre_data x) (pre_data y) ~> true) <-> (hcodes x)=(hcodes y)    

*)

Definition tree_hash_eq (ta tb: tree): ?? bool := 
  match ta, tb with
  | Tname xa, Tname xb =>
     if R.eq_dec xa xb  (* Inefficient in some cases ? *)
     then RET true
     else RET false
  | Top oa lta, Top ob ltb => 
     DO b <~ op_eq oa ob ;;
     if b then phys_eq lta ltb
     else RET false
  | Terase t1a t2a, Terase t1b t2b =>
      DO b <~ phys_eq t1a t1b ;;
      if b 
      then phys_eq t2a t2b
      else RET false
  | _,_ => RET false
  end.

Local Hint Resolve op_eq_correct: wlp.

Lemma tree_hash_eq_correct: forall ta tb, WHEN tree_hash_eq ta tb ~> b THEN b=true -> ta=tb.
Proof.
  destruct ta, tb; wlp_simplify; (discriminate || (subst; auto)).
Qed.
Global Opaque tree_hash_eq.
Hint Resolve tree_hash_eq_correct: wlp.

Definition list_tree_hash_eq (lta ltb: list_tree): ?? bool := 
  match lta, ltb with
  | Tnil, Tnil => RET true
  | Tcons ta lta, Tcons tb ltb => 
      DO b <~ phys_eq ta tb ;;
     if b then phys_eq lta ltb
     else RET false
  | _,_ => RET false
  end.

Lemma list_tree_hash_eq_correct: forall lta ltb, WHEN list_tree_hash_eq lta ltb ~> b THEN b=true -> lta=ltb.
Proof.
  destruct lta, ltb; wlp_simplify; (discriminate || (subst; auto)).
Qed.
Global Opaque list_tree_hash_eq.
Hint Resolve list_tree_hash_eq_correct: wlp.

Lemma pdeps_get_intro d1 d2:
  (forall x, Dict.get d1 x = Dict.get d2 x) -> (forall x, pdeps_get d1 x = pdeps_get d2 x).
Proof.
  unfold pdeps_get; intros H x; rewrite H. destruct (Dict.get d2 x); auto.
Qed.

Local Hint Resolve hbblock_deps_correct Dict.eq_test_correct: wlp.


(*** A GENERIC EQ_TEST: IN ORDER TO SUPPORT SEVERAL DEBUGGING MODE !!! ***)

Section Prog_Eq_Gen.

Variable dbg1: R.t -> ?? option pstring. (* debugging of p1 insts *)
Variable dbg2: R.t -> ?? option pstring. (* log of p2 insts *)
Variable log1: unit -> ?? unit. (* log of p1 insts *)
Variable log2: unit -> ?? unit. (* log of p2 insts *)


Variable hco_tree: hashConsing tree.
Hypothesis hco_tree_correct: hCons_spec hco_tree.
Variable hco_list: hashConsing list_tree.
Hypothesis hco_list_correct: hCons_spec hco_list.

Variable print_error_end: hdeps -> hdeps -> ?? unit.
Variable print_error: pstring -> ?? unit.

Program Definition g_bblock_eq_test (p1 p2: bblock): ?? bool :=
  DO r <~ (TRY
    DO d1 <~ hbblock_deps (hC hco_tree) (hC hco_list) dbg1 log1 p1 ;;
    DO d2 <~ hbblock_deps (hC_known hco_tree) (hC_known hco_list) dbg2 log2 p2 ;;
    DO b <~ Dict.eq_test d1 d2 ;;
    if b then RET true
    else (
      print_error_end d1 d2 ;;
      RET false
    )
  CATCH_FAIL s, _ =>
    print_error s;;
    RET false
  ENSURE (fun b => b=true -> forall ge, bblock_equiv ge p1 p2));;
  RET (`r).
Obligation 1.
  destruct hco_tree_correct as [X1 X2], hco_list_correct as [Y1 Y2].
  constructor 1; wlp_simplify; try congruence.
  apply bblock_deps_equiv; auto.
  intros; rewrite <- H, <- H0.
  apply pdeps_get_intro. auto.
Qed.

Theorem g_bblock_eq_test_correct p1 p2:
  WHEN g_bblock_eq_test p1 p2 ~> b THEN b=true -> forall ge, bblock_equiv ge p1 p2.
Proof.
  wlp_simplify.
  destruct exta; simpl in * |- *; auto.
Qed.
Global Opaque g_bblock_eq_test.

End Prog_Eq_Gen.



Definition skip (_:unit): ?? unit := RET tt.
Definition no_dbg (_:R.t): ?? option pstring := RET None.


Definition msg_prefix: pstring := "*** ERROR INFO from bblock_eq_test: ".
Definition msg_error_on_end: pstring := "mismatch in final assignments !".
Definition msg_unknow_tree: pstring := "unknown tree node".
Definition msg_unknow_list_tree: pstring := "unknown list node".
Definition msg_number: pstring := "on 2nd bblock -- on inst num ".

Definition print_error_end (_ _: hdeps): ?? unit
 := println (msg_prefix +; msg_error_on_end).

Definition print_error (log: logger unit) (s:pstring): ?? unit
 := DO n <~ log_info log ();;
    println (msg_prefix +; msg_number +; n +; " -- " +; s). 


Program Definition bblock_eq_test (p1 p2: bblock): ?? bool :=
  DO log <~ count_logger ();;
  DO hco_tree <~ mk_annot (hCons tree_hash_eq (fun _ => RET msg_unknow_tree));;
  DO hco_list <~ mk_annot (hCons list_tree_hash_eq (fun _ => RET msg_unknow_list_tree));;
  g_bblock_eq_test no_dbg no_dbg skip (log_insert log) hco_tree _ hco_list _ print_error_end (print_error log) p1 p2.
Obligation 1.  
  generalize (hCons_correct _ _ _ _ H0); clear H0.
  constructor 1; wlp_simplify.
Qed.
Obligation 2.  
  generalize (hCons_correct _ _ _ _ H); clear H.
  constructor 1; wlp_simplify.
Qed.

Local Hint Resolve g_bblock_eq_test_correct.

Theorem bblock_eq_test_correct p1 p2:
  WHEN bblock_eq_test p1 p2 ~> b THEN b=true -> forall ge, bblock_equiv ge p1 p2.
Proof.
  wlp_simplify.
Qed.
Global Opaque bblock_eq_test.



(** This is only to print info on each bblock_eq_test run **)
Section Verbose_version.

Variable string_of_name: R.t -> ?? pstring.
Variable string_of_op: op -> ?? pstring.

Definition tree_id (id: caml_string): pstring := "E" +; (CamlStr id).
Definition list_id (id: caml_string): pstring := "L" +; (CamlStr id).

Local Open Scope string_scope.

Definition print_raw_htree (td: pre_hashV tree): ?? unit :=
  match pre_data td, hcodes td with
  | (Tname x), _ => 
    DO s <~ string_of_name x;;
    println( "init_access " +; s)
  | (Top o Tnil), _ => 
    DO so <~ string_of_op o;;
    println so
  | (Top o _), [ _; _; lid ] =>
    DO so <~ string_of_op o;;
    DO sl <~ string_of_hashcode lid;;
    println (so +; " " +; (list_id sl))
  | (Terase _ _), [ _ ; t1; t2 ] =>
    DO st1 <~ string_of_hashcode t1 ;;
    DO st2 <~ string_of_hashcode t2 ;;
    println((tree_id st1) +; " erases " +; (tree_id st2))
  | _, _ => FAILWITH "unexpected hcodes"
  end.

Definition print_raw_hlist(ld: pre_hashV list_tree): ?? unit :=
  match pre_data ld, hcodes ld with
  | Tnil, _ => println ""
  | (Tcons _ _), [ t ; l ] =>
    DO st <~ string_of_hashcode t ;;
    DO sl <~ string_of_hashcode l ;;
    println((tree_id st) +; " " +; (list_id sl))
  | _, _ => FAILWITH "unexpected hcodes"
  end.

Section PrettryPrint.

Variable get_htree: hashcode -> ?? pre_hashV tree. 
Variable get_hlist: hashcode -> ?? pre_hashV list_tree.

(* NB: requires [t = pre_data pt] *)
Fixpoint string_of_tree (t: tree) (pt: pre_hashV tree) : ?? pstring :=
  match debug_info pt with
  | Some x => RET x
  | None => 
    match t, hcodes pt with
    | Tname x, _ => string_of_name x
    | Top o Tnil, _ => string_of_op o
    | Top o (_ as l), [ _; _; lid ] => 
      DO so <~ string_of_op o;;
      DO pl <~ get_hlist lid;;
      DO sl <~ string_of_list_tree l pl;;
      RET (so +; "(" +; sl +; ")")
    | Terase t _, [ _ ; tid; _ ] =>
      DO pt <~ get_htree tid ;;
      string_of_tree t pt
    | _, _ => FAILWITH "unexpected hcodes"
    end
  end
(* NB: requires [l = pre_data pl] *)
with string_of_list_tree (l: list_tree) (lt: pre_hashV list_tree): ?? pstring :=
  match l, hcodes lt with
  | Tnil, _ => RET (Str "")
  | Tcons t Tnil, [ tid ; l ] => 
     DO pt <~ get_htree tid;;
     string_of_tree t pt
  | Tcons t l', [ tid ; lid' ] => 
     DO pt <~ get_htree tid;;
     DO st <~ string_of_tree t pt;;
     DO pl' <~ get_hlist lid';;
     DO sl <~ string_of_list_tree l' pl';;
     RET (st +; "," +; sl)
    | _, _ => FAILWITH "unexpected hcodes"
  end.


End PrettryPrint.


Definition pretty_tree ext exl pt :=
  DO r <~ string_of_tree (get_hashV ext) (get_hashV exl) (pre_data pt) pt;;
  println(r).

Fixpoint print_head (head: list pstring): ?? unit :=
  match head with
  | i::head' => println ("--- inst " +; i);; print_head head'
  | _ => RET tt
  end.

Definition print_htree ext exl (head: list pstring) (hid: hashcode) (td: pre_hashV tree): ?? unit :=
  print_head head;;
  DO s <~ string_of_hashcode hid ;;
  print ((tree_id s) +; ": ");;
  print_raw_htree td;;
  match debug_info td with
  | Some x => 
     print("//  " +; x +; " <- ");;
     pretty_tree ext exl {| pre_data:=(pre_data td); hcodes:=(hcodes td); debug_info:=None |}
  | None => RET tt
  end.

Definition print_hlist (head: list pstring) (hid: hashcode) (ld: pre_hashV list_tree): ?? unit :=
  print_head head;;
  DO s <~ string_of_hashcode hid ;;
  print ((list_id s) +; ": ");;
  print_raw_hlist ld.

Definition print_tables ext exl: ?? unit :=
  println "-- tree table --" ;;
  iterall ext (print_htree ext exl);;
  println "-- list table --" ;;
  iterall exl print_hlist;;
  println "----------------".

Definition print_final_debug ext exl (d1 d2: hdeps): ?? unit 
 := DO b <~ Dict.not_eq_witness d1 d2 ;;
    match b with
    | Some x =>
      DO s <~ string_of_name x;;
      println("mismatch on: " +; s);;
      match Dict.get d1 x with 
      | None => println("=> unassigned in 1st bblock")
      | Some ht1 =>
         print("=> node expected from 1st bblock: ");;
         DO pt1 <~ get_hashV ext (hid ht1);;
         pretty_tree ext exl pt1
      end;;
      match Dict.get d2 x with 
      | None => println("=> unassigned in 2nd bblock")
      | Some ht2 =>
         print("=> node found from 2nd bblock: ");;
         DO pt2 <~ get_hashV ext (hid ht2);;
         pretty_tree ext exl pt2
      end
    | None => FAILWITH "bug in Dict.not_eq_witness ?"
    end.

Inductive witness:=
  | Htree (pt: pre_hashV tree)
  | Hlist (pl: pre_hashV list_tree)
  | Nothing
  .

Definition msg_tree (cr: cref witness) td :=
  set cr (Htree td);;
  RET msg_unknow_tree.

Definition msg_list (cr: cref witness) tl := 
  set cr (Hlist tl);;
  RET msg_unknow_list_tree.

Definition print_witness ext exl cr msg :=
  DO wit <~ get cr ();;
  match wit with
  | Htree pt =>
     println("=> unknown tree node: ");;
     pretty_tree ext exl {| pre_data:=(pre_data pt); hcodes:=(hcodes pt); debug_info:=None |};;
     println("=> encoded on " +; msg +; " graph as: ");;
     print_raw_htree pt
  | Hlist pl =>
     println("=> unknown list node: ");;
     DO r <~ string_of_list_tree (get_hashV ext) (get_hashV exl) (pre_data pl) pl;;
     println(r);;
     println("=> encoded on " +; msg +; " graph as: ");;
     print_raw_hlist pl
  | _ => println "Unexpected failure: no witness info (hint: hash-consing bug ?)"
  end.


Definition print_error_end1 hct hcl (d1 d2:hdeps): ?? unit
 := println "- GRAPH of 1st bblock";;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    print_tables ext exl;;
    print_error_end d1 d2;;
    print_final_debug ext exl d1 d2.

Definition print_error1  hct hcl cr log s : ?? unit
 := println "- GRAPH of 1st bblock";;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    print_tables ext exl;;
    print_error log s;;
    print_witness ext exl cr "1st".


Definition xmsg_number: pstring := "on 1st bblock -- on inst num ".

Definition print_error_end2 hct hcl (d1 d2:hdeps): ?? unit
 := println (msg_prefix +; msg_error_on_end);;
    println "- GRAPH of 2nd bblock";;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    print_tables ext exl.

Definition print_error2 hct hcl cr (log: logger unit) (s:pstring): ?? unit
 := DO n <~ log_info log ();;
    DO ext <~ export hct ();;
    DO exl <~ export hcl ();;
    println (msg_prefix +; xmsg_number +; n +; " -- " +; s);;
    print_witness ext exl cr "2nd";;
    println "- GRAPH of 2nd bblock";;
    print_tables ext exl.

Definition simple_debug (x: R.t): ?? option pstring :=
  DO s <~ string_of_name x;;
  RET (Some s).

Definition log_debug (log: logger unit) (x: R.t): ?? option pstring :=
  DO i <~ log_info log ();;
  DO sx <~ string_of_name x;;
  RET (Some (sx +; "@" +; i)).

Definition hlog (log: logger unit) (hct: hashConsing tree) (hcl: hashConsing list_tree): unit -> ?? unit :=
   (fun _ =>
      log_insert log tt ;;
      DO s <~ log_info log tt;;
      next_log hct s;;
      next_log hcl s
    ).

Program Definition verb_bblock_eq_test (p1 p2: bblock): ?? bool :=
  DO log1 <~ count_logger ();;
  DO log2 <~ count_logger ();;
  DO cr <~ make_cref Nothing;;
  DO hco_tree <~ mk_annot (hCons tree_hash_eq (msg_tree cr));;
  DO hco_list <~ mk_annot (hCons list_tree_hash_eq (msg_list cr));;
  DO result1 <~ g_bblock_eq_test
     (log_debug log1)
     simple_debug
     (hlog log1 hco_tree hco_list)
     (log_insert log2) 
     hco_tree _ 
     hco_list _ 
     (print_error_end1 hco_tree hco_list)
     (print_error1 hco_tree hco_list cr log2) 
     p1 p2;;
  if result1 
  then RET true
  else
    DO log1 <~ count_logger ();;
    DO log2 <~ count_logger ();;
    DO cr <~ make_cref Nothing;;
    DO hco_tree <~ mk_annot (hCons tree_hash_eq (msg_tree cr));;
    DO hco_list <~ mk_annot (hCons list_tree_hash_eq (msg_list cr));;
    DO result2 <~ g_bblock_eq_test 
       (log_debug log1)
       simple_debug
       (hlog log1 hco_tree hco_list)
       (log_insert log2)
       hco_tree _ 
       hco_list _ 
       (print_error_end2 hco_tree hco_list)
       (print_error2 hco_tree hco_list cr log2) 
       p2 p1;;
    if result2 
    then (
      println (msg_prefix +; " OOops - symmetry violation in bblock_eq_test  => this is a bug of bblock_eq_test ??");;
      RET false
    ) else RET false
   .
Obligation 1.  
  generalize (hCons_correct _ _ _ _ H0); clear H0.
  constructor 1; wlp_simplify.
Qed.
Obligation 2.  
  generalize (hCons_correct _ _ _ _ H); clear H.
  constructor 1; wlp_simplify.
Qed.
Obligation 3.  
  generalize (hCons_correct _ _ _ _ H0); clear H0.
  constructor 1; wlp_simplify.
Qed.
Obligation 4.  
  generalize (hCons_correct _ _ _ _ H); clear H.
  constructor 1; wlp_simplify.
Qed.

Theorem verb_bblock_eq_test_correct p1 p2:
  WHEN verb_bblock_eq_test p1 p2 ~> b THEN b=true -> forall ge, bblock_equiv ge p1 p2.
Proof.
  wlp_simplify.
Qed.
Global Opaque verb_bblock_eq_test.

End Verbose_version.


End ImpDepTree.

Require Import FMapPositive.

Module ImpPosDict <: ImpDict with Module R:=Pos.

Include PosDict.
Import PositiveMap.

Fixpoint eq_test {A} (d1 d2: t A): ?? bool :=
  match d1, d2 with
  | Leaf _, Leaf _ => RET true
  | Node l1 (Some x1) r1, Node l2 (Some x2) r2 =>
      DO b0 <~ phys_eq x1 x2 ;;
      if b0 then
        DO b1 <~ eq_test l1 l2 ;;
        if b1 then
          eq_test r1 r2
        else
           RET false
      else
         RET false
  | Node l1 None r1, Node l2 None r2 =>
      DO b1 <~ eq_test l1 l2 ;;
      if b1 then
        eq_test r1 r2
      else
        RET false
  | _, _ => RET false
  end.

Lemma eq_test_correct A d1: forall (d2: t A),
 WHEN eq_test d1 d2 ~> b THEN
  b=true -> forall x, get d1 x = get d2 x.
Proof.
  unfold get; induction d1 as [|l1 Hl1 [x1|] r1 Hr1]; destruct d2 as [|l2 [x2|] r2]; simpl; 
  wlp_simplify; (discriminate || (subst; destruct x; simpl; auto)).
Qed.
Global Opaque eq_test.

(* get some key of a non-empty d *)
Fixpoint pick {A} (d: t A): ?? R.t :=
  match d with
  | Leaf _ => FAILWITH "unexpected empty dictionary"
  | Node _ (Some _) _ => RET xH
  | Node (Leaf _) None r => 
    DO p <~ pick r;;
    RET (xI p)
  | Node l None _ =>
    DO p <~ pick l;;
    RET (xO p)
  end. 


Fixpoint not_eq_witness {A} (d1 d2: t A): ?? option R.t :=
  match d1, d2 with
  | Leaf _, Leaf _ => RET None
  | Node l1 (Some x1) r1, Node l2 (Some x2) r2 =>
      DO b0 <~ phys_eq x1 x2 ;;
      if b0 then
        DO b1 <~ not_eq_witness l1 l2;;
        match b1 with
        | None => 
          DO b2 <~ not_eq_witness r1 r2;;
          match b2 with
          | None => RET None
          | Some p => RET (Some (xI p))
          end
        | Some p => RET (Some (xO p))
        end
      else
         RET (Some xH)
  | Node l1 None r1, Node l2 None r2 =>
        DO b1 <~ not_eq_witness l1 l2;;
        match b1 with
        | None => 
          DO b2 <~ not_eq_witness r1 r2;;
          match b2 with
          | None => RET None
          | Some p => RET (Some (xI p))
          end
        | Some p => RET (Some (xO p))
        end
  | l, Leaf _ => DO p <~ pick l;; RET (Some p)
  | Leaf _, r => DO p <~ pick r;; RET (Some p)
  | _, _ => RET (Some xH)
  end.

End ImpPosDict.

