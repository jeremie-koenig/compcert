
(** This file defines an instance of [ExternalCalls] for the
  [ExternalFunctions] instance defined in [ExtFunImpl]. *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Export ExtFunImpl.

Set Implicit Arguments.

Section WITHMEM.
Context `{Hmem: Mem.MemoryModel}.

(** ** Semantics of system calls. *)

Inductive extcall_io_sem (name: ident) (sg: signature) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_io_sem_intro: forall vargs m args res vres,
      eventval_list_match ge args (sig_args sg) vargs ->
      eventval_match ge res (proj_sig_res sg) vres ->
      extcall_io_sem name sg ge vargs m (Event_syscall name args res :: E0) vres m.

Lemma extcall_io_ok:
  forall name sg,
  extcall_properties (extcall_io_sem name sg) sg.
Proof.
  intros; constructor; intros.
(* well typed *)
  inv H. eapply eventval_match_type; eauto.
(* arity *)
  inv H. eapply eventval_list_match_length; eauto.
(* symbols preserved *)
  inv H1. econstructor; eauto. 
  eapply eventval_list_match_preserved; eauto.
  eapply eventval_match_preserved; eauto. 
(* valid block *)
  inv H; auto.
(* perms *)
  inv H; auto.
(* readonly *)
  inv H; auto.
(* mem extends *)
  inv H.
  exists vres; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
  red; auto.
(* mem injects *)
  inv H0.
  exists f; exists vres; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  eapply eventval_match_inject_2; eauto.
  red; auto.
  red; auto.
  red; intros; congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  inv H; inv H0.
  exploit eventval_match_valid; eauto. intros [A B]. 
  exploit eventval_valid_match. eexact H7. rewrite <- H8; eauto. 
  intros [v' EVM]. exists v'; exists m1. econstructor; eauto. 
(* determ *)
  inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  exploit eventval_match_valid. eexact H2. intros [V1 T1].
  exploit eventval_match_valid. eexact H3. intros [V2 T2].
  split. constructor; auto. congruence.
  intros EQ; inv EQ. split; auto. eapply eventval_match_determ_1; eauto.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall n m m' b m'',
      Mem.alloc m (-4) (Int.unsigned n) = (m', b) ->
      Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
      extcall_malloc_sem ge (Vint n :: nil) m E0 (Vptr b Int.zero) m''.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem 
                     (mksignature (Tint :: nil) (Some Tint)).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m n m' b m'',
    Mem.alloc m (-4) (Int.unsigned n) = (m', b) ->
    Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
    mem_unchanged_on P m m'').
  intros; split; intros.
  eauto with mem.
  transitivity (Mem.load chunk m' b0 ofs). 
  eapply Mem.load_store_other; eauto. left. 
  apply Mem.valid_not_valid_diff with m; eauto with mem.
  eapply Mem.load_alloc_other; eauto. 

  constructor; intros.
(* well typed *)
  inv H. unfold proj_sig_res; simpl. auto.
(* arity *)
  inv H. auto.
(* symbols preserved *)
  inv H1; econstructor; eauto.
(* valid block *)
  inv H. eauto with mem.
(* perms *)
  inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
  rewrite zeq_false. auto. 
  apply Mem.valid_not_valid_diff with m1; eauto with mem.
(* readonly *)
  inv H. transitivity (Mem.load chunk m' b ofs).
  eapply Mem.load_store_other; eauto. 
  left. apply Mem.valid_not_valid_diff with m1; eauto with mem.
  eapply Mem.load_alloc_unchanged; eauto.
(* mem extends *)
  inv H. inv H1. inv H5. inv H7. 
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [C D]].
  exists (Vptr b Int.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.
(* mem injects *)
  inv H0. inv H2. inv H6. inv H8.
  exploit Mem.alloc_parallel_inject; eauto. apply Zle_refl. apply Zle_refl. 
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [E G]].
  exists f'; exists (Vptr b' Int.zero); exists m2'; intuition.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b). 
  subst b1. rewrite C in H2. inv H2. eauto with mem. 
  rewrite D in H2. congruence. auto. 
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0. split. constructor. intuition congruence. 
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem  (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_intro: forall b lo sz m m',
      Mem.load Mint32 m b (Int.unsigned lo - 4) = Some (Vint sz) ->
      Int.unsigned sz > 0 ->
      Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) = Some m' ->
      extcall_free_sem ge (Vptr b lo :: nil) m E0 Vundef m'.

Lemma extcall_free_ok:
  extcall_properties extcall_free_sem 
                     (mksignature (Tint :: nil) None).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    lo < hi ->
    (forall b' ofs, P b' ofs -> b' <> b \/ ofs < lo \/ hi <= ofs) ->
    mem_unchanged_on P m m').
  intros; split; intros.
  eapply Mem.perm_free_1; eauto.
  rewrite <- H3. eapply Mem.load_free; eauto. 
  destruct (eq_block b0 b); auto. right. right. 
  apply (Intv.range_disjoint' (ofs, ofs + size_chunk chunk) (lo, hi)).
  red; intros. apply Intv.notin_range. simpl. exploit H1; eauto. intuition. 
  simpl; generalize (size_chunk_pos chunk); omega.
  simpl; omega.

  constructor; intros.
(* well typed *)
  inv H. unfold proj_sig_res. simpl. auto.
(* arity *)
  inv H. auto.
(* symbols preserved *)
  inv H1; econstructor; eauto.
(* valid block *)
  inv H. eauto with mem.
(* perms *)
  inv H. eapply Mem.perm_free_3; eauto. 
(* readonly *)
  inv H. eapply Mem.load_free; eauto.
  destruct (eq_block b b0); auto.
  subst b0. right; right. 
  apply (Intv.range_disjoint'
           (ofs, ofs + size_chunk chunk)
           (Int.unsigned lo - 4, Int.unsigned lo + Int.unsigned sz)).
  red; intros; red; intros.
  elim (H1 x). auto. apply Mem.perm_cur_max. 
  apply Mem.perm_implies with Freeable; auto with mem.
  exploit Mem.free_range_perm; eauto. 
  simpl. generalize (size_chunk_pos chunk); omega.
  simpl. omega.
(* mem extends *)
  inv H. inv H1. inv H8. inv H6. 
  exploit Mem.load_extends; eauto. intros [vsz [A B]]. inv B. 
  exploit Mem.free_parallel_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto. omega. 
  intros. destruct (eq_block b' b); auto. subst b; right.
  assert (~(Int.unsigned lo - 4 <= ofs < Int.unsigned lo + Int.unsigned sz)).
    red; intros; elim H. apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply Mem.free_range_perm. eexact H4. auto. 
  omega.
(* mem inject *)
  inv H0. inv H2. inv H7. inv H9.
  exploit Mem.load_inject; eauto. intros [vsz [A B]]. inv B. 
  assert (Mem.range_perm m1 b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto. 
    apply Mem.perm_implies with Freeable; auto with mem.
    apply H0. instantiate (1 := lo). omega. 
  intro EQ.
  assert (Mem.range_perm m1' b2 (Int.unsigned lo + delta - 4) (Int.unsigned lo + delta + Int.unsigned sz) Cur Freeable).
    red; intros. 
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply Mem.perm_inject; eauto. apply H0. omega. 
  destruct (Mem.range_perm_free _ _ _ _ H2) as [m2' FREE].
  exists f; exists Vundef; exists m2'; intuition.

  econstructor.
  rewrite EQ. replace (Int.unsigned lo + delta - 4) with (Int.unsigned lo - 4 + delta) by omega.
  eauto. auto. 
  rewrite EQ. auto.
  
  assert (Mem.free_list m1 ((b, Int.unsigned lo - 4, Int.unsigned lo + Int.unsigned sz) :: nil) = Some m2).
    simpl. rewrite H5. auto.
  eapply Mem.free_inject; eauto. 
  intros. destruct (eq_block b b1).
  subst b. assert (delta0 = delta) by congruence. subst delta0. 
  exists (Int.unsigned lo - 4); exists (Int.unsigned lo + Int.unsigned sz); split.
  simpl; auto. omega.
  elimtype False. exploit Mem.inject_no_overlap. eauto. eauto. eauto. eauto. 
  instantiate (1 := ofs + delta0 - delta).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  apply H0. omega.
  eapply Mem.perm_max. eauto with mem.
  unfold block; omega.

  eapply UNCHANGED; eauto. omega. intros.  
  red in H7. left. congruence. 

  eapply UNCHANGED; eauto. omega. intros.
  destruct (eq_block b' b2); auto. subst b'. right.
  assert (~(Int.unsigned lo + delta - 4 <= ofs < Int.unsigned lo + delta + Int.unsigned sz)).
    red; intros. elim (H7 _ _ H6). 
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    apply H0. omega.
  omega.

  red; intros. congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0. split. constructor. intuition congruence.
Qed.

(** ** Combined semantics of external calls *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Definition external_call (ef: external_function): extcall_sem :=
  match ef with
  | EF_external name sg  => extcall_io_sem name sg
  | EF_malloc            => extcall_malloc_sem 
  | EF_free              => extcall_free_sem
  end.

Theorem external_call_spec:
  forall ef, 
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig. destruct ef.
  apply extcall_io_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
Qed.

Local Existing Instances ef_spec ef_proof ef_ops sc_ops.

Local Instance ec_ops: ExtCallOps mem external_function := {
  external_call := external_call
}.

Local Instance ec_proof: ExternalCalls mem external_function := {
  external_call_spec := external_call_spec
}.

Local Instance cc_ops: CompilerConfigOps := {}.

Local Instance ec_spec: CompilerConfiguration := {}.

End WITHMEM.

