(** Demo of the example illustrating how to use ImpDep. *)

Require Import DepExampleEqTest.
Require Import Bool.

Open Scope Z_scope.

Module EqTests.

(**** TESTS DRIVER ! ****)

Record test_input := {
  name: pstring;
  expected: bool;
  verbose: bool;
  p1: bblock;
  p2: bblock;
}.

Definition run1 (t: test_input): ?? unit :=
  print ((name t) +; " =>");;
  DO result <~ bblock_eq_test (verbose t) (p1 t) (p2 t);;
  assert_b (eqb result (expected t))  "UNEXPECTED RESULT";;
  if expected t 
  then println " SUCCESS" 
  else RET tt  (* NB: in this case - bblock_eq_test is expected to have print an ERROR mesg *)
  .

Local Hint Resolve eqb_prop.

Lemma run1_correctness (t: test_input):
  WHEN run1 t ~> _ THEN (expected t)=true -> bblock_equiv (p1 t) (p2 t).
Proof.
  unfold run1; destruct t; simpl; wlp_simplify; subst.
Qed.
Global Opaque run1.
Hint Resolve run1_correctness: wlp.

Fixpoint run_all (l: list test_input): ?? unit :=
  match l with
  | nil => RET tt
  | t::l' =>
     println "" ;; (* SOME SPACES ! *)
     run1 t;;
     run_all l'
  end.

Lemma run_all_correctness l:
  WHEN run_all l ~> _ THEN (forall t, List.In t l -> (expected t)=true -> bblock_equiv (p1 t) (p2 t)).
Proof.
  induction l; simpl; wlp_simplify; subst; auto.
Qed.
Global Opaque run_all.

(**** TESTS ****)

Definition move (dst src: reg) := MOVE dst (Reg src).
Definition add_imm (dst src: reg) (z:Z) := ARITH dst ADD (Reg src) (Imm z).
Definition incr (r: reg) (z:Z) := add_imm r r z.
Definition add (dst src1 src2: reg) := ARITH dst ADD (Reg src1) (Reg src2).

Definition load (dst src:reg) (ofs:Z) := LOAD dst src (Imm ofs).
Definition store (src dst:reg) (ofs:Z) := STORE src dst (Imm ofs).
Definition memswap (r base:reg) (ofs:Z) := MEMSWAP r base (Imm ofs).

Definition R1: reg := 1%positive.
Definition R2: reg := 2%positive.
Definition R3: reg := 3%positive.
Definition R4: reg := 4%positive.


Definition demo: ?? unit := run_all [

    {| name:="move_ok" ;
       expected:=true;
       verbose:=true;
       p1:=[ move R2 R1; move R3 R1 ];
       p2:=[ move R3 R1; move R2 R3 ]; 
    |} ;
    {| name:="move_ko" ;
       expected:=false;
       verbose:=true;
       p1:=[ move R2 R1; move R3 R1 ];
       p2:=[ move R3 R1 ]; 
    |} ;

    {| name:="add_load_RAR_ok" ;
       expected:=true;
       verbose:=true;
       p1:=[ add_imm R1 R2 5; move R4 R2; load R3 R2 2  ];
       p2:=[ load R3 R2 2; add_imm R1 R2 5; move R4 R2 ]; |} ;

    {| name:="add_load_RAW_ko";
       expected:=false;
       verbose:=true;
       p1:=[ add_imm R1 R2 5; move R4 R2; load R3 R1 2 ];
       p2:=[ load R3 R1 2; add_imm R1 R2 5; move R4 R2 ]; |} ;

    {| name:="add_load_WAW_ko";
       expected:=false;
       verbose:=true;
       p1:=[ add_imm R3 R2 5; move R4 R2; load R3 R1 2 ];
       p2:=[ load R3 R1 2; add_imm R3 R2 5; move R4 R2 ]; |} ;

    {| name:="memswap_ok1";
       expected:=true;
       verbose:=true;
       p1:=[ add_imm R1 R2 5; memswap R3 R2 2 ];
       p2:=[ memswap R3 R2 2; add_imm R1 R2 5 ]; |} ;

    {| name:="memswap_ok2" ;
       expected:=true;
       verbose:=true;
       p1:=[ load R1 R2 2; store R3 R2 2; move R3 R1];
       p2:=[ memswap R3 R2 2 ; move R1 R3 ];
     |} ;

    {| name:="memswap_ko" ;
       expected:=false;
       verbose:=true;
       p1:=[ load R3 R2 2; store R3 R2 2];
       p2:=[ memswap R3 R2 2 ];
     |}
].


Fixpoint repeat_aux (n:nat) (rev_body next: bblock): bblock :=
  match n with
  | O => next
  | (S n) => repeat_aux n rev_body (List.rev_append rev_body next)
  end.

Definition repeat n body next := repeat_aux n (List.rev_append body []) next.


Definition inst1 := add R1 R1 R2. 

(* NB: returns [inst1^10; next] *)
Definition dummy1 next:= repeat 10%nat [inst1] next.

Definition main: ?? unit := run_all [

    {| name:="move_never_skips1" ;
       expected:=false;
       verbose:=false;
       p1:=[ move R2 R2 ];
       p2:=[ ]; 
    |} ;

    {| name:="move_compress_ok" ;
       expected:=true;
       verbose:=false;
       p1:=[ move R1 R2; move R2 R1; MOVE R1 (Imm 7) ];
       p2:=[ MOVE R1 (Imm 7); move R2 R2 ]; 
     |} ;

    {| name:="move_never_skip2" ;
       expected:=false;
       verbose:=false;
       p1:=[ move R1 R2; move R2 R1; MOVE R1 (Imm 7) ];
       p2:=[ MOVE R1 (Imm 7) ]; 
     |} ;

    {| name:="R2_RAR_ok1"; 
       expected:=true; 
       verbose:=false;
       p1:=dummy1 [ load R3 R2 2; store R3 R4 7 ];
       p2:=load R3 R2 2::store R3 R4 7::(dummy1 nil) |} ;
    {| name:="R2_RAR_ok2"; 
       expected:=true; 
       verbose:=false;
       p1:=dummy1 [ load R3 R2 2; store R3 R4 7 ];
       p2:=load R3 R2 2::(dummy1 [store R3 R4 7]) |} ;
    {| name:="R2_RAR_ok3"; 
       expected:=true; 
       verbose:=false;
       p1:=dummy1 [ load R3 R2 2; store R3 R4 7 ];
       p2:=load R3 R2 2::(repeat 4%nat [inst1;inst1] [store R3 R4 7; inst1; inst1]) |} ;
    {| name:="bad_register_name_ko"; 
       expected:=false; 
       verbose:=false;
       p1:=dummy1 [ load R3 R2 2 ];
       p2:=dummy1 [ load R3 R3 2 ] |} ;
    {| name:="bad_instruction_ko"; 
       expected:=false; 
       verbose:=false;
       p1:=dummy1 [ load R3 R2 2 ];
       p2:=dummy1 [ store R3 R2 2 ] |} ;
    {| name:="incompleteness_ko"; 
       expected:=false; 
       verbose:=false;
       p1:=dummy1 [ load R3 R2 2 ];
       p2:=[inst1; load R3 R2 2] |} ;


    {| name:="R2_WAR_ko"; 
       expected:=false; 
       verbose:=false;
       p1:=dummy1 [ load R2 R3 2 ];
       p2:=load R2 R3 2::(dummy1 nil) |} ;
    {| name:="bad_register_name_ko2"; 
       expected:=false; 
       verbose:=false;
       p1:=dummy1 [ load R2 R3 2 ];
       p2:=load R3 R2 2::(dummy1 nil) |} ;


    {| name:="load_RAR_ok1";
       expected:=true;
       verbose:=false;
       p1:=[ load R1 R2 2; load R3 R4 5];
       p2:=[ load R3 R4 5; load R1 R2 2]; |} ;
    {| name:="load_RAR_ok2";
       expected:=true;
       verbose:=false;
       p1:=[ load R1 R2 2; load R3 R2 5];
       p2:=[ load R3 R2 5; load R1 R2 2]; |} ;
    {| name:="load_WAW_ko";
       expected:=false;
       verbose:=false;
       p1:=[ load R1 R2 2; load R1 R4 5];
       p2:=[ load R1 R4 5; load R1 R2 2]; |} ;
    {| name:="load_store_WAR_ko";
       expected:=false;
       verbose:=false;
       p1:=[ load R1 R2 2; store R3 R4 5];
       p2:=[ store R3 R4 5; load R1 R2 2]; |}

  ].

Definition incr_R1_5 := incr R1 5.
Definition incr_R2_3 := incr R2 3.

Definition big_test (bigN:nat) (name: pstring): ?? unit :=
    println "";;
    println("---- Time of bigtest " +; name);;
    timer(run_all, [

    {| name:="big_test_ok1"; 
       expected:=true; 
       verbose:=false;
       p1:=repeat bigN [incr_R1_5;incr_R2_3] [incr_R2_3];
       p2:=repeat bigN [incr_R1_5] (repeat (S bigN) [incr_R2_3] nil) |} ;
    {| name:="big_test_ok2"; 
       expected:=true; 
       verbose:=false;
       p1:=repeat bigN [incr_R1_5;incr_R2_3] [incr_R2_3];
       p2:=repeat bigN [incr_R2_3;incr_R1_5] [incr_R2_3] |} ;
    {| name:="big_test_ok3"; 
       expected:=true; 
       verbose:=false;
       p1:=repeat bigN [incr_R1_5;incr_R2_3] [incr_R2_3];
       p2:=repeat (S bigN) [incr_R2_3] (repeat bigN [incr_R1_5] nil) |} ;
    {| name:="big_test_ko1"; 
       expected:=false; 
       verbose:=false;
       p1:=repeat bigN [incr_R1_5;incr_R2_3] [incr_R2_3];
       p2:=repeat bigN [incr_R1_5] (repeat bigN [incr_R2_3] nil) |} ;
    {| name:="big_test_ko2"; 
       expected:=false; 
       verbose:=false;
       p1:=repeat bigN [incr_R1_5;incr_R2_3] [incr_R2_3];
       p2:=repeat (S bigN) [incr_R1_5] (repeat bigN [incr_R2_3] nil) |}

  ]).

Fixpoint big_tests (l:list (nat * string)) :=
  match l with
  | nil => RET tt
  | (x,s)::l' => big_test x s;; big_tests l'
  end.

Local Open Scope nat_scope.
Local Open Scope string_scope.

Definition big_runs: ?? unit :=
  big_tests [(2500, "2500"); (5000, "5000"); (10000, "10000"); (20000, "20000")].


End EqTests.


Require Import DepExampleParallelTest.

Module ParaTests.


(**** TESTS DRIVER ! ****)

Record test_input := {
  name: pstring;
  expected: bool;
  bundle: bblock;
}.

Definition run1 (t: test_input): ?? unit :=
  print ((name t) +; " =>");;
  assert_b (eqb (bblock_is_para (bundle t)) (expected t))  "UNEXPECTED RESULT";;
  if expected t 
  then println " SUCCESS" 
  else println " FAILED (as expected)"
  .

Local Hint Resolve eqb_prop.

Definition correct_bundle p := forall s os', (sem_bblock_par p s os' <-> res_equiv os' (sem_bblock p s)).

Lemma run1_correctness (t: test_input):
  WHEN run1 t ~> _ THEN (expected t)=true -> correct_bundle (bundle t).
Proof.
  unfold run1; destruct t; simpl; wlp_simplify; subst.
  - unfold correct_bundle; intros; apply bblock_is_para_correct; auto.
  - discriminate.
Qed.
Global Opaque run1.
Hint Resolve run1_correctness: wlp.

Fixpoint run_all (l: list test_input): ?? unit :=
  match l with
  | nil => RET tt
  | t::l' =>
     run1 t;;
     run_all l'
  end.

Lemma run_all_correctness l:
  WHEN run_all l ~> _ THEN (forall t, List.In t l -> (expected t)=true -> correct_bundle (bundle t)).
Proof.
  induction l; simpl; wlp_simplify; subst; auto.
Qed.
Global Opaque run_all.

(**** TESTS ****)

Definition add_imm (dst src: reg) (z:Z) := ARITH dst ADD (Reg src) (Imm z).

Definition load (dst src:reg) (ofs:Z) := LOAD dst src (Imm ofs).
Definition store (src dst:reg) (ofs:Z) := STORE src dst (Imm ofs).
Definition memswap (r base:reg) (ofs:Z) := MEMSWAP r base (Imm ofs).

Definition R1: reg := 1%positive.
Definition R2: reg := 2%positive.
Definition R3: reg := 3%positive.
Definition R4: reg := 4%positive.
Definition R5: reg := 5%positive.
Definition R6: reg := 5%positive.


Definition main: ?? unit :=
  println "";;
  println "-- Parallel Checks --";; 
  run_all [
   {| name:="test_war_ok"; 
      expected:=true; 
      bundle:=[add_imm R1 R2 2;add_imm R2 R2 3]
    |};
   {| name:="test_raw_ko"; 
      expected:=false; 
      bundle:=[add_imm R1 R2 2;add_imm R2 R1 3]
    |};
   {| name:="test_waw_ko"; 
      expected:=false; 
      bundle:=[add_imm R1 R2 2;add_imm R1 R2 3]
    |};
   {| name:="test_war_load_store_ok"; 
      expected:=true; 
      bundle:=[load R1 R2 2;load R2 R3 3; store R3 R4 4]
    |};
   {| name:="test_raw_load_store_ko"; 
      expected:=false; 
      bundle:=[load R1 R2 2;store R5 R4 4;load R2 R3 3]
    |};
   {| name:="test_waw_load_store_ko"; 
      expected:=false; 
      bundle:=[load R1 R2 2;store R3 R2 3;store R5 R4 4]
    |};
   {| name:="test_arith_load_store_ok"; 
      expected:=true; 
      bundle:=[load R1 R2 2; add_imm R2 R4 3; load R3 R6 3; add_imm R4 R4 3; store R6 R5 4; add_imm R6 R6 7]
    |}
  ].
 
End ParaTests.

(*************************)
(* Extraction directives *)

Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.

Import ImpConfig.

Extraction Blacklist List String.

Separate Extraction BinIntDef EqTests ParaTests.

