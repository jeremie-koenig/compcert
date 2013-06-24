(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values 
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read. 

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there. 

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVfloat: float -> eventval
  | EVptr_global: ident -> int -> eventval.

Inductive event: Type :=
  | Event_syscall: ident -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> int -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> int -> eventval -> event
  | Event_annot: ident -> list eventval -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).
  
Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq := 
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.
 
Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3, 
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H. 
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl. 
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto. 
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto. 
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.   
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt. 
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq. 
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Global environment used to translate between global variable names and their block identifiers. *)
Variables F V: Type.
Variable ge: Genv.t F V.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_ptr: forall id b ofs,
      Genv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tint (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; constructor.
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Compatibility with memory injections *)

Variable f: block -> option (block * Z).

Definition meminj_preserves_globals : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Hypothesis glob_pres: meminj_preserves_globals.

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> val_inject f v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0. constructor. constructor.
  destruct glob_pres as [A [B C]].
  exploit A; eauto. intro EQ; rewrite H3 in EQ; inv EQ.
  rewrite Int.add_zero. econstructor; eauto. 
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v,
  eventval_match ev ty v -> val_inject f v v.
Proof.
  induction 1. constructor. constructor.
  destruct glob_pres as [A [B C]].
  exploit A; eauto. intro EQ.
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, val_list_inject f vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto. congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  decEq. eapply Genv.genv_vars_inj; eauto. 
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVfloat _ => True
  | EVptr_global id ofs => exists b, Genv.find_symbol ge id = Some b
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVfloat _ => Tfloat
  | EVptr_global id ofs => Tint
  end.

Lemma eventval_valid_match:
  forall ev ty,
  eventval_valid ev -> eventval_type ev = ty -> exists v, eventval_match ev ty v.
Proof.
  intros. subst ty. destruct ev; simpl in *.
  exists (Vint i); constructor.
  exists (Vfloat f0); constructor.
  destruct H as [b A]. exists (Vptr b i0); constructor; auto.
Qed.

Lemma eventval_match_valid:
  forall ev ty v,
  eventval_match ev ty v -> eventval_valid ev /\ eventval_type ev = ty.
Proof.
  induction 1; simpl; auto. split; auto. exists b; auto.
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor. rewrite symbols_preserved; auto. 
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  unfold eventval_valid; destruct ev; auto. 
  intros [b A]. exists b; rewrite symbols_preserved; auto.
Qed.

End EVENTVAL_INV.

(** * Matching traces. *)

Section MATCH_TRACES.

Variables F V: Type.
Variable ge: Genv.t F V.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variables F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventval_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  end.
  
Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

Section WITHMEM.
Context `{Hmem: Mem.MemoryStates}.

Definition block_is_volatile (F V: Type) (ge: Genv.t F V) (b: block) : bool :=
  match Genv.find_var_info ge b with
  | None => false
  | Some gv => gv.(gvar_volatile)
  end.

Inductive volatile_load (F V: Type) (ge: Genv.t F V):
                   memory_chunk -> mem -> block -> int -> trace -> val -> Prop :=
  | volatile_load_vol: forall chunk m b ofs id ev v,
      block_is_volatile ge b = true ->
      Genv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge chunk m b ofs
                      (Event_vload chunk id ofs ev :: nil)
                      (Val.load_result chunk v)
  | volatile_load_nonvol: forall chunk m b ofs v,
      block_is_volatile ge b = false ->
      Mem.load chunk m b (Int.unsigned ofs) = Some v ->
      volatile_load ge chunk m b ofs E0 v.

Inductive volatile_store (F V: Type) (ge: Genv.t F V):
                  memory_chunk -> mem -> block -> int -> val -> trace -> mem -> Prop :=
  | volatile_store_vol: forall chunk m b ofs id ev v,
      block_is_volatile ge b = true ->
      Genv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_store ge chunk m b ofs v
                      (Event_vstore chunk id ofs ev :: nil)
                      m
  | volatile_store_nonvol: forall chunk m b ofs v m',
      block_is_volatile ge b = false ->
      Mem.store chunk m b (Int.unsigned ofs) v = Some m' ->
      volatile_store ge chunk m b ofs v E0 m'.

(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem `{mem_ops: Mem.MemoryOps mem}: Type :=
  forall (F V: Type), Genv.t F V -> list val -> mem -> trace -> val -> mem -> Prop.

(** We now specify the expected properties of this predicate. *)

Definition mem_unchanged_on (P: block -> Z -> Prop) (m_before m_after: mem): Prop :=
  (forall b ofs k p,
   P b ofs -> Mem.perm m_before b ofs k p -> Mem.perm m_after b ofs k p)
/\(forall chunk b ofs v,
   (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
   Mem.load chunk m_before b ofs = Some v ->
   Mem.load chunk m_after b ofs = Some v).

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Record extcall_properties (sem: extcall_sem)
                          (sg: signature) : Prop := mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    Val.has_type vres (proj_sig_res sg);

(** The number of arguments of an external call must agree with its signature. *)
  ec_arity:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    List.length vargs = List.length sg.(sig_args);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) vargs m1 t vres m2,
    (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
    (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b) ->
    sem F1 V1 ge1 vargs m1 t vres m2 ->
    sem F2 V2 ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 b,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 b ofs p,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 chunk b ofs,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b ->
    (forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
                          ~(Mem.perm m1 b ofs' Max Writable)) ->
    Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 m1' vargs',
    sem F V ge vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem F V ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ mem_unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs',
    meminj_preserves_globals ge f ->
    sem F V ge vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    val_list_inject f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem F V ge vargs' m1' t vres' m2'
    /\ val_inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ mem_unchanged_on (loc_unmapped f) m1 m2
    /\ mem_unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

(** External calls produce at most one event. *)
  ec_trace_length:
    forall F V ge vargs m t vres m',
    sem F V ge vargs m t vres m' -> (length t <= 1)%nat;

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive:
    forall F V ge vargs m t1 vres1 m1 t2,
    sem F V ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem F V ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ:
    forall F V ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem F V ge vargs m t1 vres1 m1 -> sem F V ge vargs m t2 vres2 m2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2)
}.

(** [extcall_sem] and [extcall_properties] are wrapped into type classes *)

Class ExtCallOps `{ef_ops: ExtFunOps} := {
  external_call (ef: external_function):
    extcall_sem
}.

Class ExternalCalls `{ec_ops: ExtCallOps} := {
  ec_mem_spec :> Mem.MemoryStates mem;
  ec_ef_spec :> ExternalFunctions external_function;
  external_call_spec (ef: external_function):
    extcall_properties (external_call ef) (ef_sig ef)
}.

End WITHMEM.

Arguments ExtCallOps mem {mem_ops} external_function {ef_ops}.
Arguments ExternalCalls mem {mem_ops} external_function {ef_ops ec_ops}.

(** Some shorthand accessors for the properties of ExternalCalls. *)
Section WITHEC.
Context `{Hef: ExternalCalls}.

Definition external_call_well_typed ef := ec_well_typed (external_call_spec ef).
Definition external_call_arity ef := ec_arity (external_call_spec ef).
Definition external_call_symbols_preserved_gen ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_spec ef).
Definition external_call_mem_extends ef := ec_mem_extends (external_call_spec ef).
Definition external_call_mem_inject ef := ec_mem_inject (external_call_spec ef).
Definition external_call_trace_length ef := ec_trace_length (external_call_spec ef).
Definition external_call_receptive ef := ec_receptive (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).

(** Special cases of [external_call_symbols_preserved_gen]. *)

Lemma external_call_symbols_preserved:
  forall ef F1 F2 V (ge1: Genv.t F1 V) (ge2: Genv.t F2 V) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b, Genv.find_var_info ge2 b = Genv.find_var_info ge1 b) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. eapply external_call_symbols_preserved_gen; eauto.
  intros. unfold block_is_volatile. rewrite H1. auto.
Qed.

Require Import Errors.

Lemma external_call_symbols_preserved_2:
  forall ef F1 V1 F2 V2 (tvar: V1 -> res V2)
         (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b gv1, Genv.find_var_info ge1 b = Some gv1 ->
     exists gv2, Genv.find_var_info ge2 b = Some gv2 /\ transf_globvar tvar gv1 = OK gv2) ->
  (forall b gv2, Genv.find_var_info ge2 b = Some gv2 ->
     exists gv1, Genv.find_var_info ge1 b = Some gv1 /\ transf_globvar tvar gv1 = OK gv2) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. eapply external_call_symbols_preserved_gen; eauto.
  intros. unfold block_is_volatile.
  case_eq (Genv.find_var_info ge1 b); intros.
  exploit H1; eauto. intros [g2 [A B]]. rewrite A. monadInv B. destruct g; auto.
  case_eq (Genv.find_var_info ge2 b); intros.
  exploit H2; eauto. intros [g1 [A B]]. congruence.
  auto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Mem.nextblock m1 <= Mem.nextblock m2.
Proof.
  intros. 
  exploit external_call_valid_block; eauto. 
  instantiate (1 := Mem.nextblock m1 - 1). red; omega.
  unfold Mem.valid_block. omega.
Qed.

(** Corollaries of [external_call_determ]. *)

Lemma external_call_match_traces:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t1 vres1 m1 t2 vres2 m2,
  external_call ef ge vargs m t1 vres1 m1 ->
  external_call ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. tauto.
Qed.

Lemma external_call_deterministic:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m t vres1 m1 vres2 m2,
  external_call ef ge vargs m t vres1 m1 ->
  external_call ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. intuition.
Qed.

End WITHEC.
