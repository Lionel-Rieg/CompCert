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

(** basic instructions (ie no control-flow) *)
Inductive basic_inst: Type :=
  | MBgetstack: ptrofs -> typ -> mreg -> basic_inst
  | MBsetstack: mreg -> ptrofs -> typ -> basic_inst
  | MBgetparam: ptrofs -> typ -> mreg -> basic_inst
  | MBop: operation -> list mreg -> mreg -> basic_inst
  | MBload: trapping_mode -> memory_chunk -> addressing -> list mreg -> mreg -> basic_inst
  | MBstore: memory_chunk -> addressing -> list mreg -> mreg -> basic_inst
  .

Definition bblock_body := list basic_inst.

(** control flow instructions *)
Inductive control_flow_inst: Type :=
  | MBcall: signature -> mreg + ident -> control_flow_inst
  | MBtailcall: signature -> mreg + ident -> control_flow_inst
  | MBbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> control_flow_inst
  | MBgoto: label -> control_flow_inst
  | MBcond: condition -> list mreg -> label -> control_flow_inst
  | MBjumptable: mreg -> list label -> control_flow_inst
  | MBreturn: control_flow_inst
  .

Record bblock := mk_bblock {
  header: list label;
  body:   bblock_body;
  exit:   option control_flow_inst
}.

Lemma bblock_eq:
  forall b1 b2,
  header b1 = header b2 ->
  body b1 = body b2 ->
  exit b1 = exit b2 ->
  b1 = b2.
Proof.
  intros. destruct b1. destruct b2.
  simpl in *. subst. auto.
Qed.

Definition length_opt {A} (o: option A) : nat :=
  match o with
  | Some o => 1
  | None => 0
  end.

Definition size (b:bblock): nat := (length (header b))+(length (body b))+(length_opt (exit b)).

Lemma size_null b:
  size b = 0%nat ->
  header b = nil /\ body b = nil /\ exit b = None.
Proof.
  destruct b as [h b e]. simpl. unfold size. simpl.
  intros H.
  assert (length h = 0%nat) as Hh; [ omega |].
  assert (length b = 0%nat) as Hb; [ omega |].
  assert (length_opt e = 0%nat) as He; [ omega|].
  repeat split.
  destruct h; try (simpl in Hh; discriminate); auto.
  destruct b; try (simpl in Hb; discriminate); auto.
  destruct e; try (simpl in He; discriminate); auto.
Qed.

Definition code := list bblock.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: ptrofs;
    fn_retaddr_ofs: ptrofs }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition genv := Genv.t fundef unit.

(*** sémantique ***)

Lemma in_dec (lbl: label) (l: list label):  { List.In lbl l } + { ~(List.In lbl l) }.
Proof.
  apply List.in_dec.
  apply Pos.eq_dec.
Qed.

Definition is_label (lbl: label) (bb: bblock) : bool :=
  if in_dec lbl (header bb) then true else false.

Lemma is_label_correct_true lbl bb:
  List.In lbl (header bb) <-> is_label lbl bb = true. 
Proof.
  unfold is_label; destruct (in_dec lbl (header bb)); simpl; intuition.
Qed.

Lemma is_label_correct_false lbl bb:
  ~(List.In lbl (header bb)) <-> is_label lbl bb = false. 
Proof.
  unfold is_label; destruct (in_dec lbl (header bb)); simpl; intuition.
Qed.


Local Open Scope nat_scope.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | bb1 :: bbl => if is_label lbl bb1 then Some c else find_label lbl bbl
  end.

Section RELSEM.

Variable rao:function -> code -> ptrofs -> Prop.
Variable ge:genv.

Definition find_function_ptr
        (ge: genv) (ros: mreg + ident) (rs: regset) : option block :=
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

(** Machblock execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: block)       (**r pointer to calling function *)
             (sp: val)        (**r stack pointer in calling function *)
             (retaddr: val)   (**r Asm return address in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state.

Definition parent_sp (s: list stackframe) : val :=
  match s with
  | nil => Vnullptr
  | Stackframe f sp ra c :: s' => sp
  end.

Definition parent_ra (s: list stackframe) : val :=
  match s with
  | nil => Vnullptr
  | Stackframe f sp ra c :: s' => ra
  end.

Inductive basic_step (s: list stackframe) (fb: block) (sp: val) (rs: regset) (m:mem): basic_inst -> regset -> mem -> Prop :=
  | exec_MBgetstack:
      forall ofs ty dst v,
      load_stack m sp ty ofs = Some v ->
      basic_step s fb sp rs m (MBgetstack ofs ty dst) (rs#dst <- v) m
  | exec_MBsetstack:
      forall src ofs ty m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      basic_step s fb sp rs m (MBsetstack src ofs ty) rs' m'
  | exec_MBgetparam:
      forall ofs ty dst v rs' f,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      basic_step s fb sp rs m (MBgetparam ofs ty dst) rs' m
  | exec_MBop:
      forall op args v rs' res,
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      basic_step s fb sp rs m (MBop op args res) rs' m
  | exec_MBload:
      forall addr args a v rs' trap chunk dst,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      basic_step s fb sp rs m (MBload trap chunk addr args dst) rs' m
  | exec_MBload_notrap1:
      forall addr args rs' chunk dst,
      eval_addressing ge sp addr rs##args = None ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- (default_notrap_load_value chunk)) ->
      basic_step s fb sp rs m (MBload NOTRAP chunk addr args dst) rs' m
  | exec_MBload_notrap2:
      forall addr args a rs' chunk dst,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = None ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- (default_notrap_load_value chunk)) ->
      basic_step s fb sp rs m (MBload NOTRAP chunk addr args dst) rs' m
  | exec_MBstore:
      forall chunk addr args src m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      basic_step s fb sp rs m (MBstore chunk addr args src) rs' m'
  .


Inductive body_step (s: list stackframe) (f: block) (sp: val): bblock_body -> regset -> mem -> regset -> mem -> Prop :=
   | exec_nil_body:
       forall rs m,
       body_step s f sp nil rs m rs m
   | exec_cons_body:
       forall rs m bi p rs' m' rs'' m'',
       basic_step s f sp rs m bi rs' m' ->
       body_step s f sp p rs' m' rs'' m'' ->
       body_step s f sp (bi::p) rs m rs'' m''
   .

Inductive cfi_step: control_flow_inst -> state -> trace -> state -> Prop :=
  | exec_MBcall:
      forall s fb sp sig ros c b rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      rao f c ra ->
      cfi_step (MBcall sig ros) (State s fb sp (b::c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs m)
  | exec_MBtailcall:
      forall s fb stk soff sig ros c rs m f f' m',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      cfi_step (MBtailcall sig ros) (State s fb (Vptr stk soff) c rs m)
        E0 (Callstate s f' rs m')
  | exec_MBbuiltin:
      forall s f sp rs m ef args res b c vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      cfi_step (MBbuiltin ef args res) (State s f sp (b :: c) rs m)
         t (State s f sp c rs' m')
  | exec_MBgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      cfi_step (MBgoto lbl) (State s fb sp c rs m)
        E0 (State s fb sp c' rs m)
  | exec_MBcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      cfi_step (MBcond cond args lbl) (State s fb sp c rs m)
        E0 (State s fb sp c' rs' m)
  | exec_MBcond_false:
      forall s f sp cond args lbl b c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      cfi_step (MBcond cond args lbl) (State s f sp (b :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_MBjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      cfi_step (MBjumptable arg tbl) (State s fb sp c rs m)
        E0 (State s fb sp c' rs' m)
  | exec_MBreturn:
      forall s fb stk soff c rs m f m',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      cfi_step MBreturn (State s fb (Vptr stk soff) c rs m)
        E0 (Returnstate s rs m')
  .

Inductive exit_step: option control_flow_inst -> state -> trace -> state -> Prop :=
  | exec_Some_exit:
      forall ctl s t s',
      cfi_step ctl s t s' ->
      exit_step (Some ctl) s t s'
  | exec_None_exit:
      forall stk f sp b lb rs m,
      exit_step None (State stk f sp (b::lb) rs m) E0 (State stk f sp lb rs m)
  .

Inductive step: state -> trace -> state -> Prop :=
  | exec_bblock:
      forall sf f sp bb c rs m rs' m' t s',
        body_step sf f sp (body bb) rs m rs' m' ->
        exit_step (exit bb) (State sf f sp (bb::c) rs' m') t s' ->
        step (State sf f sp (bb::c) rs m) t s'
  | exec_function_internal:
      forall s fb rs m f m1 m2 m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m,
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f sp c rs m)
  .

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall fb m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some fb ->
      initial_state p (Callstate nil fb (Regmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = One r ->
      rs r = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).
