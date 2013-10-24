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

Require Import Coqlib.
Require Import Integers.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Inductive builtin_function: Type :=
  | EF_vload (chunk: memory_chunk)
     (** A volatile read operation.  If the adress given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (chunk: memory_chunk)
     (** A volatile store operation.   If the adress given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | EF_vload_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile load operation from a global variable. 
         Specialized version of [EF_vload]. *)
  | EF_vstore_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile store operation in a global variable. 
         Specialized version of [EF_vstore]. *)
  | EF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | EF_annot (text: ident) (targs: list annot_arg)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (text: ident) (targ: typ)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | EF_inline_asm (text: ident).
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)

Definition bf_sig (bf: builtin_function): signature :=
  match bf with
  | EF_vload chunk => mksignature (Tint :: nil) (Some (type_of_chunk chunk))
  | EF_vstore chunk => mksignature (Tint :: type_of_chunk chunk :: nil) None
  | EF_vload_global chunk _ _ => mksignature nil (Some (type_of_chunk chunk))
  | EF_vstore_global chunk _ _ => mksignature (type_of_chunk chunk :: nil) None
  | EF_memcpy sz al => mksignature (Tint :: Tint :: nil) None
  | EF_annot text targs => mksignature (annot_args_typ targs) None
  | EF_annot_val text targ => mksignature (targ :: nil) (Some targ)
  | EF_inline_asm text => mksignature nil None
  end.

Definition bf_reloads (bf: builtin_function) : bool :=
  match bf with
  | EF_annot text targs => false
  | _ => true
  end.

Global Instance bf_ops: ExtFunOps builtin_function := {
  ef_sig := bf_sig;
  ef_reloads := bf_reloads
}.

Global Instance bf_proof: ExternalFunctions builtin_function := {
}.

(** ** Semantics of volatile loads *)

Section WITHMEM.
Context `{Hcc: CompilerConfiguration}.

Set Implicit Arguments.

Inductive volatile_load_sem (chunk: memory_chunk) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_sem_intro: forall b ofs m t v,
      volatile_load ge chunk m b ofs t v ->
      volatile_load_sem chunk ge (Vptr b ofs :: nil) m t v m.

Lemma volatile_load_preserved:
  forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) chunk m b ofs t v,
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b) ->
  volatile_load ge1 chunk m b ofs t v ->
  volatile_load ge2 chunk m b ofs t v.
Proof.
  intros. inv H1; constructor; auto.
  rewrite H0; auto.
  rewrite H; auto.
  eapply eventval_match_preserved; eauto.
  rewrite H0; auto.
Qed.

Lemma volatile_load_extends:
  forall F V (ge: Genv.t F V) chunk m b ofs t v m',
  volatile_load ge chunk m b ofs t v ->
  Mem.extends m m' ->
  exists v', volatile_load ge chunk m' b ofs t v' /\ Val.lessdef v v'.
Proof.
  intros. inv H.
  econstructor; split; eauto. econstructor; eauto.
  exploit Mem.load_extends; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
Qed.

Remark meminj_preserves_block_is_volatile:
  forall F V (ge: Genv.t F V) f b1 b2 delta,
  meminj_preserves_globals ge f ->
  f b1 = Some (b2, delta) ->
  block_is_volatile ge b2 = block_is_volatile ge b1.
Proof.
  intros. destruct H as [A [B C]]. unfold block_is_volatile. 
  case_eq (Genv.find_var_info ge b1); intros.
  exploit B; eauto. intro EQ; rewrite H0 in EQ; inv EQ. rewrite H; auto.
  case_eq (Genv.find_var_info ge b2); intros.
  exploit C; eauto. intro EQ. congruence.
  auto.
Qed.

Lemma volatile_load_inject:
  forall F V (ge: Genv.t F V) f chunk m b ofs t v b' ofs' m',
  meminj_preserves_globals ge f ->
  volatile_load ge chunk m b ofs t v ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.inject f m m' ->
  exists v', volatile_load ge chunk m' b' ofs' t v' /\ val_inject f v v'.
Proof.
  intros. inv H0.
  inv H1. exploit (proj1 H); eauto. intros EQ; rewrite H8 in EQ; inv EQ.
  rewrite Int.add_zero. exists (Val.load_result chunk v0); split.
  constructor; auto. 
  apply val_load_result_inject. eapply eventval_match_inject_2; eauto.
  exploit Mem.loadv_inject; eauto. simpl; eauto. simpl; intros [v' [A B]]. exists v'; split; auto. 
  constructor; auto. rewrite <- H3. inv H1. eapply meminj_preserves_block_is_volatile; eauto. 
Qed.

Lemma volatile_load_receptive:
  forall F V (ge: Genv.t F V) chunk m b ofs t1 t2 v1,
  volatile_load ge chunk m b ofs t1 v1 -> match_traces ge t1 t2 ->
  exists v2, volatile_load ge chunk m b ofs t2 v2.
Proof.
  intros. inv H; inv H0.
  exploit eventval_match_valid; eauto. intros [A B]. 
  exploit eventval_valid_match. eexact H9. rewrite <- H10; eauto. 
  intros [v' EVM]. exists (Val.load_result chunk v'). constructor; auto.
  exists v1; constructor; auto.
Qed.

Lemma volatile_load_ok:
  forall chunk,
  extcall_properties (volatile_load_sem chunk) 
                     (mksignature (Tint :: nil) (Some (type_of_chunk chunk))).
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H. inv H0.
  destruct chunk; destruct v; simpl; constructor.
  eapply Mem.load_type; eauto. 
(* arity *)
  inv H; inv H0; auto.
(* symbols *)
  inv H1. constructor. eapply volatile_load_preserved; eauto. 
(* valid blocks *)
  inv H; auto.
(* max perms *)
  inv H; auto.
(* readonly *)
  inv H; auto.
(* mem extends *)
  inv H. inv H1. inv H6. inv H4. 
  exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. constructor; auto. red; auto.
(* mem injects *)
  inv H0. inv H2. inv H7. inversion H5; subst. 
  exploit volatile_load_inject; eauto. intros [v' [A B]]. 
  exists f; exists v'; exists m1'; intuition. constructor; auto.
  red; auto. red; auto. red; intros. congruence.
(* trace length *)
  inv H; inv H0; simpl; omega.
(* receptive *)
  inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; constructor; auto.
(* determ *)
  inv H; inv H0. inv H1; inv H7; try congruence.
  assert (id = id0) by (eapply Genv.genv_vars_inj; eauto). subst id0.
  exploit eventval_match_valid. eexact H2. intros [V1 T1].
  exploit eventval_match_valid. eexact H4. intros [V2 T2].
  split. constructor; auto. congruence.
  intros EQ; inv EQ. 
  assert (v = v0) by (eapply eventval_match_determ_1; eauto). subst v0.
  auto.
  split. constructor. intuition congruence.
Qed.

Inductive volatile_load_global_sem (chunk: memory_chunk) (id: ident) (ofs: int)
                                   (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_global_sem_intro: forall b t v m,
      Genv.find_symbol ge id = Some b ->
      volatile_load ge chunk m b ofs t v ->
      volatile_load_global_sem chunk id ofs ge nil m t v m.

Remark volatile_load_global_charact:
  forall chunk id ofs (F V: Type) (ge: Genv.t F V) vargs m t vres m',
  volatile_load_global_sem chunk id ofs ge vargs m t vres m' <->
  exists b, Genv.find_symbol ge id = Some b /\ volatile_load_sem chunk ge (Vptr b ofs :: vargs) m t vres m'.
Proof.
  intros; split.
  intros. inv H. exists b; split; auto. constructor; auto. 
  intros [b [P Q]]. inv Q. econstructor; eauto.
Qed.

Lemma volatile_load_global_ok:
  forall chunk id ofs,
  extcall_properties (volatile_load_global_sem chunk id ofs) 
                     (mksignature nil (Some (type_of_chunk chunk))).
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H. inv H1.
  destruct chunk; destruct v; simpl; constructor.
  eapply Mem.load_type; eauto. 
(* arity *)
  inv H; inv H1; auto.
(* symbols *)
  inv H1. econstructor. rewrite H; eauto. eapply volatile_load_preserved; eauto. 
(* valid blocks *)
  inv H; auto.
(* max perm *)
  inv H; auto.
(* readonly *)
  inv H; auto.
(* extends *)
  inv H. inv H1. exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. econstructor; eauto. red; auto.
(* inject *)
  inv H0. inv H2.
  assert (val_inject f (Vptr b ofs) (Vptr b ofs)). 
    exploit (proj1 H); eauto. intros EQ. econstructor. eauto. rewrite Int.add_zero; auto.
  exploit volatile_load_inject; eauto. intros [v' [A B]].
  exists f; exists v'; exists m1'; intuition. econstructor; eauto. 
  red; auto. red; auto. red; intros; congruence. 
(* trace length *)
  inv H; inv H1; simpl; omega.
(* receptive *)
  inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; econstructor; eauto.
(* determ *)
  rewrite volatile_load_global_charact in *. 
  destruct H as [b1 [A1 B1]]. destruct H0 as [b2 [A2 B2]].
  rewrite A1 in A2; inv A2.
  eapply ec_determ. eapply volatile_load_ok. eauto. eauto. 
Qed.

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_intro: forall b ofs m1 v t m2,
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_sem chunk ge (Vptr b ofs :: v :: nil) m1 t Vundef m2.

Lemma volatile_store_preserved:
  forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) chunk m1 b ofs v t m2,
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b) ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  volatile_store ge2 chunk m1 b ofs v t m2.
Proof.
  intros. inv H1; constructor; auto.
  rewrite H0; auto.
  rewrite H; auto.
  eapply eventval_match_preserved; eauto.
  rewrite H0; auto.
Qed.

Lemma volatile_store_readonly:
  forall F V (ge: Genv.t F V) chunk1 m1 b1 ofs1 v t m2 chunk ofs b,
  volatile_store ge chunk1 m1 b1 ofs1 v t m2 ->
  Mem.valid_block m1 b ->
  (forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
                        ~(Mem.perm m1 b ofs' Max Writable)) ->
  Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs.
Proof.
  intros. inv H.
  auto.
  eapply Mem.load_store_other; eauto.
  destruct (eq_block b b1); auto. subst b1. right.
  apply (Intv.range_disjoint' (ofs, ofs + size_chunk chunk)
                              (Int.unsigned ofs1, Int.unsigned ofs1 + size_chunk chunk1)).
  red; intros; red; intros. 
  elim (H1 x); auto. 
  exploit Mem.store_valid_access_3; eauto. intros [A B].
  apply Mem.perm_cur_max. apply A. auto.
  simpl. generalize (size_chunk_pos chunk); omega.
  simpl. generalize (size_chunk_pos chunk1); omega.
Qed.

Lemma volatile_store_extends:
  forall F V (ge: Genv.t F V) chunk m1 b ofs v t m2 m1' v',
  volatile_store ge chunk m1 b ofs v t m2 ->
  Mem.extends m1 m1' ->
  Val.lessdef v v' ->
  exists m2', 
     volatile_store ge chunk m1' b ofs v' t m2'
  /\ Mem.extends m2 m2'
  /\ mem_unchanged_on (loc_out_of_bounds m1) m1' m2'.
Proof.
  intros. inv H.
  econstructor; split. econstructor; eauto. eapply eventval_match_lessdef; eauto.
  split. auto. red; auto.
  exploit Mem.store_within_extends; eauto. intros [m2' [A B]].
  exists m2'; intuition. econstructor; eauto. 
  red; split; intros.
  eapply Mem.perm_store_1; eauto.
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  destruct (eq_block b0 b); auto. subst b0; right. 
  apply (Intv.range_disjoint' (ofs0, ofs0 + size_chunk chunk0)
                              (Int.unsigned ofs, Int.unsigned ofs + size_chunk chunk)).
  red; intros; red; intros.
  exploit (H x H5). exploit Mem.store_valid_access_3. eexact H3. intros [E G].
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  auto.
  simpl. generalize (size_chunk_pos chunk0). omega.
  simpl. generalize (size_chunk_pos chunk). omega.
Qed.

Lemma volatile_store_inject:
  forall F V (ge: Genv.t F V) f chunk m1 b ofs v t m2 m1' b' ofs' v',
  meminj_preserves_globals ge f ->
  volatile_store ge chunk m1 b ofs v t m2 ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  val_inject f v v' ->
  Mem.inject f m1 m1' ->
  exists m2',
       volatile_store ge chunk m1' b' ofs' v' t m2'
    /\ Mem.inject f m2 m2'
    /\ mem_unchanged_on (loc_unmapped f) m1 m2
    /\ mem_unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros. inv H0.
  inv H1. exploit (proj1 H); eauto. intros EQ; rewrite H9 in EQ; inv EQ.
  rewrite Int.add_zero. exists m1'.
  split. constructor; auto.  eapply eventval_match_inject; eauto.
  split. auto. split. red; auto. red; auto. 
  assert (Mem.storev chunk m1 (Vptr b ofs) v = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  inv H1. exists m2'; intuition. 
  constructor; auto. rewrite <- H4. eapply meminj_preserves_block_is_volatile; eauto.  
  split; intros. eapply Mem.perm_store_1; eauto.
  rewrite <- H6. eapply Mem.load_store_other; eauto. 
  left. exploit (H1 ofs0). generalize (size_chunk_pos chunk0). omega. 
  unfold loc_unmapped. congruence.
  split; intros. eapply Mem.perm_store_1; eauto.
  rewrite <- H6. eapply Mem.load_store_other; eauto.
  destruct (eq_block b0 b'); auto. subst b0; right.
  assert (EQ: Int.unsigned (Int.add ofs (Int.repr delta)) = Int.unsigned ofs + delta).
    eapply Mem.address_inject; eauto with mem.
  unfold Mem.storev in A. rewrite EQ in A. rewrite EQ.
  apply (Intv.range_disjoint' (ofs0, ofs0 + size_chunk chunk0)
                              (Int.unsigned ofs + delta, Int.unsigned ofs + delta + size_chunk chunk)).
  red; intros; red; intros. exploit (H1 x H7). eauto.
  exploit Mem.store_valid_access_3. eexact H0. intros [C D].
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  apply C. red in H8; simpl in H8. omega. 
  auto.
  simpl. generalize (size_chunk_pos chunk0). omega.
  simpl. generalize (size_chunk_pos chunk). omega.
Qed.

Lemma volatile_store_receptive:
  forall F V (ge: Genv.t F V) chunk m b ofs v t1 m1 t2,
  volatile_store ge chunk m b ofs v t1 m1 -> match_traces ge t1 t2 -> t1 = t2.
Proof.
  intros. inv H; inv H0; auto.  
Qed.

Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk) 
                     (mksignature (Tint :: type_of_chunk chunk :: nil) None).
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H; constructor.
(* arity *)
  inv H; simpl; auto.
(* symbols preserved *)
  inv H1. constructor. eapply volatile_store_preserved; eauto. 
(* valid block *)
  inv H. inv H1. auto. eauto with mem.
(* perms *)
  inv H. inv H2. auto. eauto with mem. 
(* readonly *)
  inv H. eapply volatile_store_readonly; eauto.
(* mem extends*)
  inv H. inv H1. inv H6. inv H7. inv H4.
  exploit volatile_store_extends; eauto. intros [m2' [A [B C]]]. 
  exists Vundef; exists m2'; intuition. constructor; auto. 
(* mem inject *)
  inv H0. inv H2. inv H7. inv H8. inversion H5; subst.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; intuition. constructor; auto. red; intros; congruence.
(* trace length *)
  inv H; inv H0; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0. inv H1; inv H8; try congruence.
  assert (id = id0) by (eapply Genv.genv_vars_inj; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  split. constructor. auto.
  split. constructor. intuition congruence.
Qed.

Inductive volatile_store_global_sem (chunk: memory_chunk) (id: ident) (ofs: int)
                                   (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_global_sem_intro: forall b m1 v t m2,
      Genv.find_symbol ge id = Some b ->
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_global_sem chunk id ofs ge (v :: nil) m1 t Vundef m2.

Remark volatile_store_global_charact:
  forall chunk id ofs (F V: Type) (ge: Genv.t F V) vargs m t vres m',
  volatile_store_global_sem chunk id ofs ge vargs m t vres m' <->
  exists b, Genv.find_symbol ge id = Some b /\ volatile_store_sem chunk ge (Vptr b ofs :: vargs) m t vres m'.
Proof.
  intros; split. 
  intros. inv H; exists b; split; auto; econstructor; eauto.
  intros [b [P Q]]. inv Q. econstructor; eauto. 
Qed.

Lemma volatile_store_global_ok:
  forall chunk id ofs,
  extcall_properties (volatile_store_global_sem chunk id ofs) 
                     (mksignature (type_of_chunk chunk :: nil) None).
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H; constructor.
(* arity *)
  inv H; simpl; auto.
(* symbols preserved *)
  inv H1. econstructor. rewrite H; eauto. eapply volatile_store_preserved; eauto. 
(* valid block *)
  inv H. inv H2. auto. eauto with mem.
(* perms *)
  inv H. inv H3. auto. eauto with mem. 
(* readonly *)
  inv H. eapply volatile_store_readonly; eauto.
(* mem extends*)
  rewrite volatile_store_global_charact in H. destruct H as [b [P Q]]. 
  exploit ec_mem_extends. eapply volatile_store_ok. eexact Q. eauto. eauto. 
  intros [vres' [m2' [A [B [C D]]]]]. 
  exists vres'; exists m2'; intuition. rewrite volatile_store_global_charact. exists b; auto. 
(* mem inject *)
  rewrite volatile_store_global_charact in H0. destruct H0 as [b [P Q]]. 
  exploit (proj1 H). eauto. intros EQ. 
  assert (val_inject f (Vptr b ofs) (Vptr b ofs)). econstructor; eauto. rewrite Int.add_zero; auto.
  exploit ec_mem_inject. eapply volatile_store_ok. eauto. eexact Q. eauto. eauto. 
  intros [f' [vres' [m2' [A [B [C [D [E G]]]]]]]].
  exists f'; exists vres'; exists m2'; intuition.
  rewrite volatile_store_global_charact. exists b; auto. 
(* trace length *)
  inv H. inv H1; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto. subst t2. 
  exists vres1; exists m1; congruence.
(* determ *)
  rewrite volatile_store_global_charact in *. 
  destruct H as [b1 [A1 B1]]. destruct H0 as [b2 [A2 B2]]. rewrite A1 in A2; inv A2. 
  eapply ec_determ. eapply volatile_store_ok. eauto. eauto. 
Qed.

(** ** Semantics of annotations. *)

Fixpoint annot_eventvals (targs: list annot_arg) (vargs: list eventval) : list eventval :=
  match targs, vargs with
  | AA_arg ty :: targs', varg :: vargs' => varg :: annot_eventvals targs' vargs'
  | AA_int n :: targs', _ => EVint n :: annot_eventvals targs' vargs
  | AA_float n :: targs', _ => EVfloat n :: annot_eventvals targs' vargs
  | _, _ => vargs
  end.

Inductive extcall_annot_sem (text: ident) (targs: list annot_arg) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args (annot_args_typ targs) vargs ->
      extcall_annot_sem text targs ge vargs m
           (Event_annot text (annot_eventvals targs args) :: E0) Vundef m.

Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs) (mksignature (annot_args_typ targs) None).
Proof.
  intros; constructor; intros.
(* well typed *)
  inv H. simpl. auto.
(* arity *)
  inv H. simpl. eapply eventval_list_match_length; eauto.
(* symbols *)
  inv H1. econstructor; eauto. 
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
  inv H; auto.
(* perms *)
  inv H; auto.
(* readonly *)
  inv H; auto.
(* mem extends *)
  inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
  red; auto.
(* mem injects *)
  inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; auto.
  red; auto.
  red; intros; congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. 
  exists vres1; exists m1; congruence.
(* determ *)
  inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
Qed.

Inductive extcall_annot_val_sem (text: ident) (targ: typ) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem text targ ge (varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall text targ,
  extcall_properties (extcall_annot_val_sem text targ) (mksignature (targ :: nil) (Some targ)).
Proof.
  intros; constructor; intros.

  inv H. unfold proj_sig_res; simpl. eapply eventval_match_type; eauto.

  inv H. auto.

  inv H1. econstructor; eauto. 
  eapply eventval_match_preserved; eauto.

  inv H; auto.

  inv H; auto.

  inv H; auto.

  inv H. inv H1. inv H6. 
  exists v2; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_lessdef; eauto.
  red; auto.

  inv H0. inv H2. inv H7.
  exists f; exists v'; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; auto.
  red; auto.
  red; intros; congruence.

  inv H; simpl; omega.

  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.

  inv H; inv H0.
  assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
  split. constructor. auto.
Qed.

(** ** Semantics of [memcpy] operations. *)

Inductive extcall_memcpy_sem (sz al: Z) (F V: Type) (ge: Genv.t F V): list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall bdst odst bsrc osrc m bytes m',
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
      (al | sz) -> (al | Int.unsigned osrc) -> (al | Int.unsigned odst) ->
      bsrc <> bdst \/ Int.unsigned osrc = Int.unsigned odst
                   \/ Int.unsigned osrc + sz <= Int.unsigned odst
                   \/ Int.unsigned odst + sz <= Int.unsigned osrc ->
      Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes ->
      Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m' ->
      extcall_memcpy_sem sz al ge (Vptr bdst odst :: Vptr bsrc osrc :: nil) m E0 Vundef m'.

Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al) (mksignature (Tint :: Tint :: nil) None).
Proof.
  intros. constructor.
(* return type *)
  intros. inv H. constructor. 
(* arity *)
  intros. inv H. auto.
(* change of globalenv *)
  intros. inv H1. econstructor; eauto.
(* valid blocks *)
  intros. inv H. eauto with mem. 
(* perms *)
  intros. inv H. eapply Mem.perm_storebytes_2; eauto. 
(* readonly *)
  intros. inv H. eapply Mem.load_storebytes_other; eauto.
  destruct (eq_block b bdst); auto.   subst b. right.
  apply (Intv.range_disjoint'
          (ofs, ofs + size_chunk chunk)
          (Int.unsigned odst, Int.unsigned odst + Z_of_nat (length bytes))).
  red; intros; red; intros. elim (H1 x); auto.
  apply Mem.perm_cur_max. 
  eapply Mem.storebytes_range_perm; eauto. 
  simpl. generalize (size_chunk_pos chunk); omega.
  simpl. rewrite (Mem.loadbytes_length _ _ _ _ _ H8). rewrite nat_of_Z_eq.
  omega. omega.
(* extensions *)
  intros. inv H. 
  inv H1. inv H13. inv H14. inv H10. inv H11.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  exploit Mem.loadbytes_extends; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_within_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'.
  split. econstructor; eauto.
  split. constructor.
  split. auto.
  red; split; intros.
  eauto with mem.  
  exploit Mem.loadbytes_length. eexact H8. intros.
  rewrite <- H1. eapply Mem.load_storebytes_other; eauto. 
  destruct (eq_block b bdst); auto. subst b; right.
  exploit list_forall2_length; eauto. intros R. 
  apply (Intv.range_disjoint' (ofs, ofs + size_chunk chunk)
                              (Int.unsigned odst, Int.unsigned odst + Z_of_nat (length bytes2))); simpl.
  red; unfold Intv.In; simpl; intros; red; intros.
  eapply (H x H11).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm. eexact H9.
  rewrite R. auto. 
  generalize (size_chunk_pos chunk). omega.
  rewrite <- R. rewrite H10. rewrite nat_of_Z_eq. omega. omega.
(* injections *)
  intros. inv H0. inv H2. inv H14. inv H15. inv H11. inv H12.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Int.unsigned odst) (Int.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m1 bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m1 bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto. 
  eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. constructor.
  split. auto.
  split. red; split; intros. eauto with mem. 
  rewrite <- H2. eapply Mem.load_storebytes_other; eauto. 
  destruct (eq_block b bdst); auto. subst b. 
  assert (loc_unmapped f bdst ofs). apply H0. generalize (size_chunk_pos chunk); omega. 
  red in H12. congruence.
  split. red; split; intros. eauto with mem.
  rewrite <- H2. eapply Mem.load_storebytes_other; eauto. 
  destruct (eq_block b b0); auto. subst b0; right.
  rewrite <- (list_forall2_length B). rewrite LEN. rewrite nat_of_Z_eq; try omega.
  apply (Intv.range_disjoint' (ofs, ofs + size_chunk chunk)
                              (Int.unsigned odst + delta0, Int.unsigned odst + delta0 + sz)); simpl.
  red; unfold Intv.In; simpl; intros; red; intros.
  eapply (H0 x H12). eauto. apply Mem.perm_cur_max. apply RPDST. omega. 
  generalize (size_chunk_pos chunk); omega.
  omega.
  split. apply inject_incr_refl.
  red; intros; congruence.
(* trace length *)
  intros; inv H. simpl; omega.
(* receptive *)
  intros. 
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
  intros; inv H; inv H0. split. constructor. intros; split; congruence.
Qed.


Definition builtin_call (bf: builtin_function): extcall_sem :=
  match bf with
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_vload_global chunk id ofs => volatile_load_global_sem chunk id ofs
  | EF_vstore_global chunk id ofs => volatile_store_global_sem chunk id ofs
  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot txt targs   => extcall_annot_sem txt targs
  | EF_annot_val txt targ=> extcall_annot_val_sem txt targ
  | EF_inline_asm txt    => extcall_annot_sem txt nil
  end.

Theorem builtin_call_ok:
  forall ef, 
  extcall_properties (builtin_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig. destruct ef.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply volatile_load_global_ok.
  apply volatile_store_global_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply extcall_annot_ok.
Qed.

Global Instance bc_ops: ExtCallOps mem builtin_function := {
  external_call := builtin_call
}.

Global Instance bc_proof: ExternalCalls mem builtin_function := {
  external_call_spec := builtin_call_ok
}.

End WITHMEM.
