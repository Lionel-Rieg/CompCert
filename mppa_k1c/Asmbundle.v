Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.
Require Export Asmblock.
Require Import ListSet.


Fixpoint notIn {A} (x: A) (l:list A): Prop :=
  match l with
  | nil => True
  | a::l' => x <> a /\ notIn x l'
  end.

Lemma notIn_rewrite A (r:A) l: (~List.In r l) <-> notIn r l.
Proof.
  induction l; simpl; intuition.
Qed.


Section RELSEM.

Variable ge: genv.

(** List of all registers, to use for Pbuiltin dependencies *)
Definition all_gpregs := 
  GPR0 :: GPR1 :: GPR2 :: GPR3 :: GPR4 :: GPR5 :: GPR6 :: GPR7 :: GPR8 :: GPR9 ::
  GPR10 :: GPR11 :: GPR12 :: GPR13 :: GPR14 :: GPR15 :: GPR16 :: GPR17 :: GPR18 :: GPR19 ::
  GPR20 :: GPR21 :: GPR22 :: GPR23 :: GPR24 :: GPR25 :: GPR26 :: GPR27 :: GPR28 :: GPR29 ::
  GPR30 :: GPR31 :: GPR32 :: GPR33 :: GPR34 :: GPR35 :: GPR36 :: GPR37 :: GPR38 :: GPR39 ::
  GPR40 :: GPR41 :: GPR42 :: GPR43 :: GPR44 :: GPR45 :: GPR46 :: GPR47 :: GPR48 :: GPR49 ::
  GPR50 :: GPR51 :: GPR52 :: GPR53 :: GPR54 :: GPR55 :: GPR56 :: GPR57 :: GPR58 :: GPR59 ::
  GPR60 :: GPR61 :: GPR62 :: GPR63 :: nil.

Fact all_gpregs_complete : forall gpr, List.In gpr all_gpregs.
Proof.
  intros. destruct gpr; simpl.
  all: repeat ((try (left; reflexivity)); right).
Qed.

Definition all_pregs := (map IR all_gpregs) ++ (map FR all_gpregs) ++ (RA::PC::nil).

Fact all_pregs_complete : forall br, List.In br all_pregs.
Proof.
  intros. destruct br.
  - unfold all_pregs. apply in_app_iff. left. apply in_map. apply all_gpregs_complete.
  - unfold all_pregs. apply in_app_iff. right. apply in_app_iff. left. apply in_map. apply all_gpregs_complete.
  - unfold all_pregs. repeat (apply in_app_iff; right). simpl. left; auto.
  - unfold all_pregs. repeat (apply in_app_iff; right). simpl. right; auto.
Qed.

Definition writeregs (i: instruction): list preg :=
  match i with
  (* Control instructions *)
  | Pset rd rs => rd::nil
  | Pget rd rs => IR rd::nil
  | Pcall s => RA::nil
  (* Load *)
  | PLoadRRO i rd ra o => IR rd::nil
  (* Arith *)
  | PArithR i rd => IR rd::nil
  | PArithRR i rd rs => IR rd::nil
  | PArithRI32 i rd imm => IR rd::nil
  | PArithRI64 i rd imm => IR rd::nil
  | PArithRRR i rd rs1 rs2 => IR rd::nil
  | PArithRRI32 i rd rs imm => IR rd::nil
  | PArithRRI64 i rd rs imm => IR rd::nil
  (* Alloc and freeframe *)
  | Pallocframe _ _ => IR FP::IR GPR31::IR SP :: nil
  | Pfreeframe _ _ => IR GPR31::IR SP :: nil
  (* builtins : only implemented in OCaml, we know nothing about them *)
  | Pbuiltin _ _ _ => all_pregs
  (* Instructions that do not write *)
  | Pnop | Pret | Pgoto _ | Pj_l _ | Pcb _ _ _ | Pcbu _ _ _ | PStoreRRO _ _ _ _ => nil
  end.

(* Lemma update_PC_breg (rs: regset) v (r: preg):
  (rs#PC <- v) r = rs r.
Proof.
  rewrite Pregmap.gso; auto. congruence.
Qed.
 *)

(* Lemma update_pregs_diff (rs:regset) rd x r: r <> rd -> update_pregs rs (rs # rd <- x) r = rs r.
Proof.
  unfold update_pregs. intro H. rewrite Bregmap.gso; congruence.
Qed.
 *) 

(* Hint Rewrite update_PC_breg update_pregs_diff: regset_rw. *)

(* Fact writeregs_correct f i rs m rs' m' r: 
    ~(List.In r (writeregs i)) -> 
    (exec_bblock ge f (bblock_single_inst i) rs m) = Next rs' m' ->
    rs' r = rs r.
Proof.
  rewrite notIn_rewrite.
  unfold exec_bblock, nextblock, size; destruct i; simpl.
  destruct i; simpl.
  destruct i; simpl; try ( 
    destruct i; simpl; intro H; decompose [and] H; clear H;
    intros H; inversion_clear H;
    autorewrite with regset_rw; auto; fail).
  - (* LOAD *) destruct i; simpl. 
  destruct i; simpl; unfold exec_load; 
  destruct (Mem.loadv _ _ _); try discriminate;
  intro H; decompose [and] H; clear H;
  intros H; inversion_clear H;
  autorewrite with regset_rw; auto.
  - (* STORE *) destruct i; simpl. 
  destruct i; simpl; unfold exec_store;
  destruct (Mem.storev _ _ _ _); try discriminate;
  intro H; clear H;
  intros H; inversion_clear H;
  autorewrite with regset_rw; auto.
  - (* ALLOCFRAME *)
Admitted.
 *)

Definition readregs (i: instruction) : list preg :=
  match i with
  (* Control instructions *)
  | Pset rd rs => IR rs::nil
  | Pget rd rs => rs::nil
  | Pcb bt r l => IR r::nil
  | Pcbu bt r l => IR r::nil
  | Pret => RA::nil
  (* Load and store *)
  | PLoadRRO i rd ra o => IR ra :: nil
  | PStoreRRO i rs ra o => IR rs :: IR ra :: nil
  (* Arith *)
  | PArithRR i rd rs => IR rs :: nil
  | PArithRRR i rd rs1 rs2 => IR rs1 :: IR rs2 :: nil
  | PArithRRI32 i rd rs imm => IR rs :: nil
  | PArithRRI64 i rd rs imm => IR rs :: nil
  (* Alloc and freeframe (from the semantics) *) 
  | Pallocframe _ _ | Pfreeframe _ _ => IR SP :: nil
  (* builtins : only implemented in OCaml, we know nothing about them *)
  | Pbuiltin _ _ _ => all_pregs
  (* Instructions that do not read *)
  | Pnop | Pcall _ | Pgoto _ | Pj_l _ | PArithR _ _ | PArithRI32 _ _ _ | PArithRI64 _ _ _ => nil
  end.

Axiom TODO: False.

(* Definition outcome_equiv (r: preg) v (o1 o2: outcome (rgset:=regset))  :=
  match o1 with
  | Next rs1 m1 => exists rs2, exists m2, o2=Next rs2 m2 /\ (forall r, (rs1#r <-- v) r = rs2 r) /\ (forall chunk p, Mem.loadv chunk m1 p = Mem.loadv chunk m2 p)
  | Stuck => o2 = Stuck
  end.

Fact useregs_correct f i rs m r v: 
  ~(List.In r ((readregs i)++(writeregs i))) -> 
    outcome_equiv r v
                  (exec_bblock ge f (bblock_single_inst i) rs m) 
                  (exec_bblock ge f (bblock_single_inst i) (rs#r <-- v) m).
Proof.
  rewrite notIn_rewrite.
  unfold exec_bblock, nextblock, size; destruct i; simpl.
  + destruct i; simpl.
   - destruct i; simpl.
     * intro H; decompose [and] H; clear H. (* H useless *)
       elim TODO.
     * intro H; decompose [and] H; clear H.
       destruct i; simpl.
       simpl; eexists; eexists; constructor 1; eauto. 
       intuition. 
       destruct r0.
       rewrite! update_PC_breg.
    (* TODO: lemma on  rs # _ <-- _ *)
Abort.
 *)

(* alternative definition of disjoint *)
Definition disjoint_x {A: Type} (l l':list A) : Prop := forall r, In r l -> ~In r l'. (* TODO: use notIn instead ? *)

Example disjoint_x_ex1: disjoint_x (4::2::1::nil) (3::5::7::nil).
Proof.
  unfold disjoint_x; simpl. intuition.
Qed.

Lemma disjoint_x_nilr : forall A (l:list A), disjoint_x l nil.
Proof.
  unfold disjoint_x; simpl. intuition.
Qed.

Lemma disjoint_x_consl : forall A l l' (e:A), disjoint_x l l' -> (~ In e l') -> disjoint_x (e::l) l'.
Proof.
  unfold disjoint_x; simpl. intuition (subst; eauto).
Qed.

(* Inductive definition of disjoint, easier to reason with 

Sylvain: I am not sure. Actually, from the above definition, we can still prove the following "constructors" as lemma if needed
 (cf. example above).
*)

Inductive disjoint {A: Type} : list A -> list A -> Prop :=
  | disjoint_nilr : forall l, disjoint l nil
  | disjoint_nill : forall l, disjoint nil l
  | disjoint_consl : forall l l' e, disjoint l l' -> (~ In e l') -> disjoint (e::l) l'
  | disjoint_consr : forall l l' e, disjoint l l' -> (~ In e l) -> disjoint l (e::l')
  .

Example disjoint_ex1: disjoint (4::2::1::nil) (3::5::7::nil).
Proof.
  repeat constructor.
  all: try (intro H; simpl in H;
  repeat (match goal with h:_ \/ _ |- _ => inversion_clear h; [discriminate|] | _ => fail end); contradiction).
Qed.

Inductive depfree : list preg -> list preg -> list instruction -> Prop :=
  | depfree_nil : forall lr lw, depfree lr lw nil
  | depfree_cons : forall i lri lwi lw lr l,
                    lri = readregs i -> lwi = writeregs i ->
                    disjoint lwi lw -> (* Checking for WAW *)
                    disjoint lri lw -> (* Checking for RAW *)
                    depfree (lr++lri) (lw++lwi) l ->
                    depfree lr lw (i::l)
  .

(* une version alternative *)
Inductive depfreex : list preg -> list instruction -> Prop :=
  | depfreex_nil : forall lw, depfreex lw nil
  | depfreex_cons : forall i lri lwi lw l,
                    lri = readregs i -> lwi = writeregs i ->
                    disjoint_x lri lw -> (* Checking for RAW *)
                    disjoint_x lwi lw -> (* Checking for WAW *)
                    depfreex (lw++lwi) l ->
                    depfreex lw (i::l)
  .

Import ListNotations.

Open Scope list_scope.

Local Hint Resolve depfreex_nil depfreex_cons.

Example depfreex_2 i1 i2 lw1 lr2 lw2:
  lw1 = writeregs i1 ->
  lr2 = readregs i2 ->
  lw2 = writeregs i2 ->
  disjoint_x lr2 lw1 ->  (* RAW *)
  disjoint_x lw2 lw1 ->  (* WAW *)
  depfreex [] [i1;i2].
Proof.
  intros; eapply depfreex_cons; eauto;
  unfold disjoint_x; simpl; intuition.
Qed.

(* FIXME: STUB *)
Definition is_bundle (b:bblock):=True. 

Definition bundle_step (s:state) (t:trace) (s':state): Prop := 
  exists obi, stepin ge obi s t s' /\ forall bi, obi = Some bi -> is_bundle bi.

End RELSEM.

Definition bundle_semantics (p: program) :=
  Semantics bundle_step (initial_state p) final_state (Genv.globalenv p).



(*

(** * Instruction dependencies, definition of a bundle 

*)

(** NOTE: in all of these dependencies definitions, we do *not* consider PC.
          PC dependencies are fullfilled by the above separation in bblocks
 *)

(* (writereg i rd) holds if an instruction writes to a single register rd *)
Inductive writereg: instruction -> preg -> Prop :=
  | writereg_set:         forall rd rs,         writereg (Pset rd rs) rd
  | writereg_get:         forall rd rs,         writereg (Pget rd rs) rd
  | writereg_load:        forall i rd ra o,     writereg (PLoadRRO i rd ra o) rd
  | writereg_arith_r:     forall i rd,          writereg (PArithR i rd) rd
  | writereg_arith_rr:    forall i rd rs,       writereg (PArithRR i rd rs) rd
  | writereg_arith_ri32:  forall i rd imm,      writereg (PArithRI32 i rd imm) rd
  | writereg_arith_ri64:  forall i rd imm,      writereg (PArithRI64 i rd imm) rd
  | writereg_arith_rrr:   forall i rd rs1 rs2,  writereg (PArithRRR i rd rs1 rs2) rd
  | writereg_arith_rri32: forall i rd rs imm,   writereg (PArithRRI32 i rd rs imm) rd
  | writereg_arith_rri64: forall i rd rs imm,   writereg (PArithRRI64 i rd rs imm) rd
  .

(* (nowrite i) holds if an instruction doesn't write to any register *)
Inductive nowrite: instruction -> Prop :=
  | nowrite_ret:                      nowrite Pret
  | nowrite_call:   forall l,         nowrite (Pcall l)
  | nowrite_goto:   forall l,         nowrite (Pgoto l)
  | nowrite_jl:     forall l,         nowrite (Pj_l l)
  | nowrite_cb:     forall bt r l,    nowrite (Pcb bt r l)
  | nowrite_cbu:    forall bt r l,    nowrite (Pcbu bt r l)
  | nowrite_store:  forall i rs ra o, nowrite (PStoreRRO i rs ra o)
  | nowrite_label:  forall l,         nowrite (Plabel l)
  .

(* (readregs i lr) holds if an instruction reads from the register list lr, and only from it *)
Inductive readregs: instruction -> list preg -> Prop :=
  | readregs_set:         forall rd rs,         readregs (Pset rd rs) (IR rs::nil)
  | readregs_get:         forall rd rs,         readregs (Pget rd rs) (rs::nil)
  | readregs_cb:          forall bt r l,        readregs (Pcb bt r l) (IR r::nil)
  | readregs_cbu:         forall bt r l,        readregs (Pcbu bt r l) (IR r::nil)
  | readregs_load:        forall i rd ra o,     readregs (PLoadRRO i rd ra o) (IR ra::nil)
  | readregs_store:       forall i rs ra o,     readregs (PStoreRRO i rs ra o) (IR rs::IR ra::nil)
  | readregs_arith_rr:    forall i rd rs,       readregs (PArithRR i rd rs) (IR rs::nil)
  | readregs_arith_rrr:   forall i rd rs1 rs2,  readregs (PArithRRR i rd rs1 rs2) (IR rs1::IR rs2::nil)
  | readregs_arith_rri32: forall i rd rs imm,   readregs (PArithRRI32 i rd rs imm) (IR rs::nil)
  | readregs_arith_rri64: forall i rd rs imm,   readregs (PArithRRI64 i rd rs imm) (IR rs::nil)
  .

(* (noread i) holds if an instruction doesn't read any register *)
Inductive noread: instruction -> Prop :=
  | noread_ret:                           noread Pret
  | noread_call:        forall l,         noread (Pcall l)
  | noread_goto:        forall l,         noread (Pgoto l)
  | noread_jl:          forall l,         noread (Pj_l l)
  | noread_arith_r:     forall i rd,      noread (PArithR i rd)
  | noread_arith_ri32:  forall i rd imm,  noread (PArithRI32 i rd imm)
  | noread_arith_ri64:  forall i rd imm,  noread (PArithRI64 i rd imm)
  | noread_label:       forall l,         noread (Plabel l)
  .

(* (wawfree i i') holds if i::i' has no WAW dependency *)
Inductive wawfree: instruction -> instruction -> Prop :=
  | wawfree_write: forall i rs i' rs',
      writereg i rs -> writereg i' rs' -> rs <> rs' -> wawfree i i'
  | wawfree_free1: forall i i',
      nowrite i -> wawfree i i'
  | wawfree_free2: forall i i',
      nowrite i' -> wawfree i i'
  .

(* (rawfree i i') holds if i::i' has no RAW dependency *)
Inductive rawfree: instruction -> instruction -> Prop :=
  | rawfree_single: forall i rd i' rs,
      writereg i rd -> readregs i' (rs::nil) -> rd <> rs -> rawfree i i'
  | rawfree_double: forall i rd i' rs rs',
      writereg i rd -> readregs i' (rs::rs'::nil) -> rd <> rs -> rd <> rs' -> rawfree i i'
  | rawfree_free1: forall i i',
      nowrite i -> rawfree i i'
  | rawfree_free2: forall i i',
      noread i' -> rawfree i i'
  .

(* (depfree i i') holds if i::i' has no RAW or WAW dependency *)
Inductive depfree: instruction -> instruction -> Prop :=
  | mk_depfree: forall i i', rawfree i i' -> wawfree i i' -> depfree i i'.

(* (depfreelist i c) holds if i::c has no RAW or WAW dependency _in regards to i_ *)
Inductive depfreelist: instruction -> list instruction -> Prop :=
  | depfreelist_nil:  forall i,
      depfreelist i nil
  | depfreelist_cons: forall i i' l,
      depfreelist i l -> depfree i i' -> depfreelist i (i'::l)
  .

(* (depfreeall c) holds if c has no RAW or WAW dependency within itself *)
Inductive depfreeall: list instruction -> Prop :=
  | depfreeall_nil:
      depfreeall nil
  | depfreeall_cons: forall i l,
      depfreeall l -> depfreelist i l -> depfreeall (i::l)
  .

(** NOTE: we do not verify the resource constraints of the bundles,
          since not meeting them causes a failure when invoking the assembler *)

(* A bundle is well formed if his body and exit do not have RAW or WAW dependencies *)
Inductive wf_bundle: bblock -> Prop := 
  | mk_wf_bundle: forall b, depfreeall (body b ++ unfold_exit (exit b)) -> wf_bundle b.

Hint Constructors writereg nowrite readregs noread wawfree rawfree depfree depfreelist depfreeall wf_bundle.

Record bundle := mk_bundle {
  bd_block: bblock;
  bd_correct: wf_bundle bd_block
}.

Definition bundles := list bundle.

Definition unbundlize (lb: list bundle) := map bd_block lb.
Definition unfold_bd (lb: list bundle) := unfold (map bd_block lb).

Lemma unfold_bd_app: forall l l', unfold_bd (l ++ l') = unfold_bd l ++ unfold_bd l'.
Proof.
  intros l l'. unfold unfold_bd. rewrite map_app. rewrite unfold_app. auto.
Qed.

(** Some theorems on bundles construction *)
Lemma bundle_empty_correct: wf_bundle empty_bblock.
Proof.
  constructor. auto.
Qed.

Definition empty_bundle := {| bd_block := empty_bblock; bd_correct := bundle_empty_correct |}.

(** Bundlization. For now, we restrict ourselves to bundles containing 1 instruction *)

Definition single_inst_block (i: instruction) := acc_block i empty_bblock.

Fact single_inst_block_correct: forall i, wf_bundle (hd empty_bblock (single_inst_block i)).
Proof.
  intros i. unfold single_inst_block. unfold acc_block. destruct i.
  all:  simpl; constructor; simpl; auto.
Qed.

Definition bundlize_inst (i: instruction) :=
  {| bd_block := hd empty_bblock (single_inst_block i); bd_correct := single_inst_block_correct i |}.

Lemma bundlize_inst_conserv: forall c, unfold (unbundlize (map bundlize_inst c)) = c.
Proof.
  induction c as [|i c]; simpl; auto.
  rewrite IHc. destruct i; simpl; auto.
Qed.

Definition split_bblock (b: bblock) := map bundlize_inst (unfold_block b).

Fixpoint bundlize (lb: list bblock) :=
  match lb with
  | nil => nil
  | b :: lb => split_bblock b ++ bundlize lb
  end.

Lemma unfold_split_bblock: forall b, unfold_bd (split_bblock b) = unfold_block b.
Proof.
  intros b. unfold unfold_bd. unfold split_bblock. apply bundlize_inst_conserv.
Qed.

Theorem unfold_bundlize: forall lb, unfold_bd (bundlize lb) = unfold lb.
Proof.
  induction lb as [|b lb]; simpl; auto.
  rewrite unfold_bd_app. rewrite IHlb. rewrite unfold_split_bblock. auto.
Qed.

Theorem unfold_bundlize_fold: forall c, unfold_bd (bundlize (fold c)) = c.
Proof.
  intros. rewrite unfold_bundlize. rewrite unfold_fold. auto.
Qed.

Record function : Type := mkfunction { fn_sig: signature; fn_bundles: bundles }.
Definition fn_code := (fun (f: function) => unfold_bd (fn_bundles f)).
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
*)