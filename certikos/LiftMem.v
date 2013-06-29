Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Import Functor.
Require Import Monad.
Require Import Comonad.
Require Import Lens.

(** * Prerequisites *)

Class LiftMemoryOps (mem bmem: Type) := {
  liftmem_bops :> Mem.MemoryOps bmem;
  liftmem_get :> Getter mem bmem;
  liftmem_set :> Setter mem bmem;
  liftmem_empty: mem
}.

Class LiftMem (mem bmem: Type) `{mem_liftops: LiftMemoryOps mem bmem} := {
  liftmem_bspec :> Mem.MemoryStates bmem;
  liftmem_lens :> Lens mem bmem;
  liftmem_get_empty: get liftmem_empty = Mem.empty
}.

(** * Lifting memory operations *)

Class Lift A B := { lift: A -> B }.

Section LIFT.
  Context {mem bmem} `{getb: Getter mem bmem} `{setb: Setter mem bmem}.
  Context `{HF: Functor}.

  (** Because [Mem.MemoryStates] contains so many theorems, we need some
    systematic way to lift the memory operations on [W mem], so that
    the lifting of the theorems is convenient to automate.

    The signature of most of the memory operations are variations on
    the theme [mem -> F mem], where [F] is a functor such as [option]
    or [- * Z]. We need to lift them to [W mem -> F (W mem)]. Note
    that using the comonad's [fmap] is not possible because that would
    yield a function of type [W mem -> W (F mem)]. Instead, we use
    the following: *)

  Global Instance lens_lift: Lift (bmem -> F bmem) (mem -> F mem) := {
    lift f m := fmap (fun bm => set bm m) (f (get m))
  }.

  (** Here are some basic theorems about [lift] with any functor. *)

  Theorem lift_mor (f g: bmem -> F bmem) (m: mem):
    f (get m) = g (get m) ->
    lift f m = lift g m.
  Proof.
    intros Hfg.
    simpl.
    apply f_equal.
    assumption.
  Qed.
End LIFT.

Section LIFTINSTANCES.
  Context {mem bmem} `{getb: Getter mem bmem} `{setb: Setter mem bmem}.

  Global Instance lift_const A: Lift (bmem -> A) (mem -> A) :=
    lens_lift (F := (fun _ => A)).
  Global Instance lift_prod A: Lift (bmem -> bmem * A) (mem -> mem * A) :=
    lens_lift.
End LIFTINSTANCES.

Section LIFTOPS.
  Context mem `{mem_liftops: LiftMemoryOps mem}.

  (** We can now use [lift] to define the operations of the comonadic
    memory states. *)

  Global Instance liftmem_ops: Mem.MemoryOps mem := {
    empty :=
      liftmem_empty;
    nextblock wm :=
      lift Mem.nextblock wm;
    alloc wm lo hi :=
      lift (fun m => Mem.alloc m lo hi) wm;
    free wm b lo hi :=
      lift (fun m => Mem.free m b lo hi) wm;
    load chunk wm b ofs :=
      lift (fun m => Mem.load chunk m b ofs) wm;
    store chunk wm b ofs v :=
      lift (fun m => Mem.store chunk m b ofs v) wm;
    loadbytes wm b ofs n :=
      lift (fun m => Mem.loadbytes m b ofs n) wm;
    storebytes wm b ofs vs :=
      lift (fun m => Mem.storebytes m b ofs vs) wm;
    perm wm b ofs k p :=
      lift (fun m => Mem.perm m b ofs k p) wm;
    valid_pointer wm b ofs :=
      lift (fun m => Mem.valid_pointer m b ofs) wm;
    drop_perm wm b lo hi p :=
      lift (fun m => Mem.drop_perm m b lo hi p) wm;
    extends wm1 wm2 :=
      Mem.extends (get wm1) (get wm2);
    inject i wm1 wm2 :=
      Mem.inject i (get wm1) (get wm2);
    inject_neutral thr wm :=
      Mem.inject_neutral thr (get wm)
  }.
End LIFTOPS.

(** * Lifting the properties *)

(** Now we lift the properties listed in [Mem.MemoryStates]: given a theorem
  about [mem], we need to prove the equivalent theorem about [W mem]
  and the corresponding lifted operations it involves. To do this,
  we need some theorems about lift to help us rewrite our lifted goals
  to use the original theorems. *)

(** ** Properties of [lift (F:=option)] *)

Section LIFTOPTION.
  Context {mem bmem} `{Hgs: LensGetSet mem bmem}.

  Lemma lift_option_eq (f: bmem -> option bmem):
    forall (wa wb: mem),
      lift f wa = Some wb ->
      f (get wa) = Some (get wb).
  Proof.
    unfold lift; simpl; intros.
    destruct (f (get wa)); try discriminate.
    inversion H.
    autorewrite with lens.
    reflexivity.
  Qed.

  Lemma lift_option_eq_set_iff (f: bmem -> option bmem):
    forall (wm: mem) (w': bmem),
      lift f wm = Some (set w' wm) <->
      f (get wm) = Some w'.
  Proof.
    simpl; intros.
    split; destruct (f (get wm)); try discriminate;
    intro H; inversion H.
    - apply f_equal.
      apply lens_eq_set in H1.
      assumption.
    - reflexivity.
  Qed.

  Lemma lift_option_eq_set (f: bmem -> option bmem):
    forall (wm: mem) (m': bmem),
      f (get wm) = Some m' ->
      lift f wm = Some (set m' wm).
  Proof.
    apply lift_option_eq_set_iff.
  Qed.

  Theorem lift_option_eq_preserves_context (f g: bmem -> option bmem):
    forall (wm: mem) (wm': mem),
      g (get wm) = Some (get wm') ->
      lift f wm = Some wm' ->
      lift g wm = Some wm'.
  Proof.
    intros wa wb Hg Hlf.
    rewrite <- Hlf.
    apply lift_mor.
    rewrite Hg.
    symmetry.
    apply lift_option_eq.
    assumption.
  Qed.
End LIFTOPTION.

(** ** Properties of [lift (F := fun X => A * X)] *)

Section LIFTPROD.
  Context {mem bmem} `{Hgs: LensGetSet mem bmem} {A: Type}.

  Theorem lift_prod_eq (f: bmem -> bmem * A) (wm wm': mem) (a: A):
    lift f wm = (wm', a) ->
    f (get wm) = (get wm', a).
  Proof.
    simpl.
    destruct (f (get wm)) as [m' a'].
    intros H.
    inversion H.
    autorewrite with lens in *.
    reflexivity.
  Qed.

  Theorem lift_prod_eq_set (f: bmem -> bmem * A) wm m' a:
    f (get wm) = (m', a) ->
    lift f wm = (set m' wm, a).
  Proof.
    intro H; simpl.
    rewrite H; clear H; simpl.
    reflexivity.
  Qed.
End LIFTPROD.

(** ** Lifting [Mem.MemoryStates] *)

Section LIFTDERIVED.
  Context `{HW: LiftMem}.

  (** Now we must come up with a suitable leaf tactic.
    The first step for proving a lifted theorem involving an
    operation applied to a term [wm: W mem] is to rewrite it in
    terms of [lift] applied to the underlying operation. *)

  (** However for the derived operations we first need to show that
    the [W mem] versions are indeed equivalent to lifting the [mem]
    versions. *)

  Theorem lift_loadv chunk wm addr:
    Mem.loadv chunk wm addr =
    lift (fun m => Mem.loadv chunk m addr) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_storev chunk a v wm:
    Mem.storev chunk wm a v =
    lift (fun m => Mem.storev chunk m a v) wm.
  Proof.
    unfold Mem.storev.
    destruct a; reflexivity.
  Qed.

  Theorem lift_free_list l wm:
    Mem.free_list wm l =
    lift (fun m => Mem.free_list m l) wm.
  Proof.
    revert wm.
    induction l as [ | [[b lo] hi] l IHl];
    intros; simpl in *.
    * rewrite lens_set_get.
      reflexivity.
    * destruct (Mem.free (get wm) b lo hi); [| reflexivity].
      rewrite IHl.
      rewrite lens_get_set.
      destruct (Mem.free_list b0 l); [| reflexivity].
      rewrite lens_set_set.
      reflexivity.
  Qed.

  Theorem lift_valid_block (wm: mem) (b: block):
    Mem.valid_block wm b <->
    lift (fun m => Mem.valid_block m b) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_range_perm (wm: mem) b lo hi k p:
    Mem.range_perm wm b lo hi k p <->
    lift (fun m => Mem.range_perm m b lo hi k p) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_valid_access (wm: mem) chunk b ofs p:
    Mem.valid_access wm chunk b ofs p <->
    lift (fun m => Mem.valid_access m chunk b ofs p) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_weak_valid_pointer (wm: mem) b ofs:
    Mem.weak_valid_pointer wm b ofs =
    lift (fun m => Mem.weak_valid_pointer m b ofs) wm.
  Proof.
    reflexivity.
  Qed.
End LIFTDERIVED.

Hint Rewrite
  @lift_loadv
  @lift_storev
  @lift_free_list
  @lift_valid_block
  @lift_range_perm
  @lift_valid_access
  @lift_weak_valid_pointer
  using typeclasses eauto : lift.

(** For the fields of [Mem.MemoryOps], which are defined in terms
  of [lift] to begin with, we can use [simpl], making sure that
  we stop once we reach [lift]: *)

Arguments lift _ _ _ _ : simpl never.

(** Once we've rewritten everything in terms of [lift], we can apply
  some of the generic theorems we proved earlier. For the goal we
  just add them as hints to the lift database. *)

Hint Resolve
  @lift_mor
  @lift_option_eq
  @lift_option_eq_set
  @lift_prod_eq
  @lift_prod_eq_set
  : lift.

(* Post-process lift_?_eq_set *)
Hint Extern 10 => rewrite !lens_get_set in *: lift.

(** For the premises we need to apply them explicitely. *)

Ltac lift_premise :=
  match goal with
    | [ H: lift ?f ?wm = Some ?b |- _ ] =>
      eapply lift_option_eq in H
    | [ H: lift ?f ?wm = Some (set ?m' ?wm) |- _ ] =>
      eapply lift_option_eq_set in H
    | [ H: lift ?f ?wm = (?m, ?x) |- _ ] =>
      eapply lift_prod_eq in H
    | [ H: lift ?f ?wm = (set ?m' ?wm, ?a) |- _ ] =>
      eapply lift_prod_eq_set in H
  end.

Hint Extern 10 => progress (repeat lift_premise): lift.

(** Next, we need to use the original theorem in order to prove the
  lifted one. To do this we must reduce [lift] to obtain a goal
  which is stated in terms of the original operations applied to
  [(extract wm)]. This hint makes sure [eauto] can do that. *)

Hint Extern 10 => progress (unfold lift in *; simpl in * ): lift. 

(** Replace [(extract Mem.empty)] by the underlying [Mem.empty]. *)
Hint Rewrite @liftmem_get_empty using typeclasses eauto: lift.

(** Hook the rewrite rules into the lift database. *)
Hint Extern 10 => progress (autorewrite with lift in * ): lift.

  (** This is the main tactic we use: it lifts a theorem [Hf] of
    the underlying memory model by "peeling off" its structure
    recursively to prove the lifted goal. The leaf goals are
    handled with the caller-provided tactic [leaftac]. *)

  (* FIXME: we could probably do away with the mem parameter to the
    tactics below (just try both possibilities and see what works) *)

  (* Premises are "translated" and used to specialize Hf *)
  Ltac peel_intro mem recurse Hf x :=
    intro x;
    let T := type of x in
    lazymatch type of Hf with
      (* No transformation required, just pass it along. *)
      | forall (y: T), _ =>
	specialize (Hf x)

      (* [mem] argument, use [extract] *)
      | forall (m: mem), _ =>
	specialize (Hf (get x))

      (* Otherwise, recurse. *)
      | forall (H: ?T'), _ =>
	let H' := fresh H in
	assert (H': T') by recurse x;
	specialize (Hf H');
	clear H'
    end;
    (*try clear x;*)
    recurse Hf.

  (* Existential: we must use [set] to augment any memory state
    provided by Hf, but we can otherwise just pass everything along *)
  Ltac peel_exists mem recurse Hf x :=
    let Hf' := fresh Hf in
    destruct Hf as [x Hf'];
    let T := type of x in
    match T with
      | mem => eexists (set x _)
      | _ => exists x
    end;
    recurse Hf'.

  (* Conjunction: split and peel each side independently *)
  Ltac peel_conj recurse Hf :=
    let Hl := fresh Hf "l" in
    let Hr := fresh Hf "r" in
    destruct Hf as [Hl Hr];
    try (split; [recurse Hl | recurse Hr]).

  Ltac peel Hf leaftac :=
    let recurse Hf := peel Hf leaftac in
    try lazymatch goal with
      | _: LiftMem ?mem ?bmem |- forall (x: _), _ =>
        let x := fresh x in peel_intro bmem recurse Hf x
      | _: LiftMem ?mem ?bmem |- exists (x: _), _ =>
        let x := fresh x in peel_exists bmem recurse Hf x
      | _: LiftMem ?mem ?bmem |- { x: _ | _ } =>
        let x := fresh x in peel_exists bmem recurse Hf x
      | |- _ /\ _ =>
        peel_conj recurse Hf
      | |- ?T =>
        leaftac tt
    end.

  (** We're now ready to define our leaf tactic, and use it in
    conjunction with [peel] to solve the goals automatically. *)

  Ltac lift_leaf f :=
    eauto 10 using f with lift typeclass_instances.

  Ltac lift_partial f :=
    pose proof f as Hf;
    peel Hf lift_leaf.

  Ltac lift f :=
    now lift_partial f.

Section LIFTMEM.
  Context mem bmem `{Hmem: LiftMem mem bmem}.

  Hint Extern 10 (lift _ _ = Some _) =>
    eapply lift_option_eq_preserves_context; eassumption
    : lift.
(*
  Hint Immediate
    lift_option_eq_preserves_context
    : lift.
*)

  Global Instance liftmem_spec: Mem.MemoryStates mem.
  Proof.
    esplit.
    lift Mem.nextblock_pos.
    lift Mem.valid_not_valid_diff.
    lift Mem.perm_implies.
    lift Mem.perm_cur_max.
    lift Mem.perm_cur.
    lift Mem.perm_max.
    lift Mem.perm_valid_block.
    lift Mem.perm_dec.
    lift Mem.range_perm_implies.
    lift Mem.range_perm_cur.
    lift Mem.range_perm_max.
    lift Mem.valid_access_implies.
    lift Mem.valid_access_valid_block.
    lift Mem.valid_access_perm.
    lift Mem.valid_pointer_nonempty_perm.
    lift Mem.valid_pointer_valid_access.
    lift Mem.weak_valid_pointer_spec.
    lift Mem.valid_pointer_implies.
    lift Mem.nextblock_empty.
    lift Mem.perm_empty.
    lift Mem.valid_access_empty.
    lift Mem.valid_access_load.
    lift Mem.load_valid_access.
    lift Mem.load_type.
    lift Mem.load_cast.
    lift Mem.load_int8_signed_unsigned.
    lift Mem.load_int16_signed_unsigned.
    lift Mem.load_float64al32.
    lift Mem.loadv_float64al32.
    lift Mem.range_perm_loadbytes.
    lift Mem.loadbytes_range_perm.
    lift Mem.loadbytes_load.
    lift Mem.load_loadbytes.
    lift Mem.loadbytes_length.
    lift Mem.loadbytes_empty.
    lift Mem.loadbytes_concat.
    lift Mem.loadbytes_split.
    lift Mem.nextblock_store.
    lift Mem.store_valid_block_1.
    lift Mem.store_valid_block_2.
    lift Mem.perm_store_1.
    lift Mem.perm_store_2.
    lift Mem.valid_access_store.
    lift Mem.store_valid_access_1.
    lift Mem.store_valid_access_2.
    lift Mem.store_valid_access_3.
    lift Mem.load_store_similar.
    lift Mem.load_store_same.
    lift Mem.load_store_other.
    lift Mem.load_store_pointer_overlap.
    lift Mem.load_store_pointer_mismatch.
    lift Mem.load_pointer_store.
    lift Mem.loadbytes_store_same.
    lift Mem.loadbytes_store_other.
    lift Mem.store_signed_unsigned_8.
    lift Mem.store_signed_unsigned_16.
    lift Mem.store_int8_zero_ext.
    lift Mem.store_int8_sign_ext.
    lift Mem.store_int16_zero_ext.
    lift Mem.store_int16_sign_ext.
    lift Mem.store_float32_truncate.
    lift Mem.store_float64al32.
    lift Mem.storev_float64al32.
    lift Mem.range_perm_storebytes.
    lift Mem.storebytes_range_perm.
    lift Mem.perm_storebytes_1.
    lift Mem.perm_storebytes_2.
    lift Mem.storebytes_valid_access_1.
    lift Mem.storebytes_valid_access_2.
    lift Mem.nextblock_storebytes.
    lift Mem.storebytes_valid_block_1.
    lift Mem.storebytes_valid_block_2.
    lift Mem.storebytes_store.
    lift Mem.store_storebytes.
    lift Mem.loadbytes_storebytes_same.
    lift Mem.loadbytes_storebytes_other.
    lift Mem.load_storebytes_other.
    lift_partial Mem.storebytes_concat.
      simpl in *; unfold lift in *; simpl in *.
      destruct (Mem.storebytes (get m) b ofs (bytes1 ++ bytes2));
      destruct (Mem.storebytes (get m) b ofs bytes1);
      destruct (Mem.storebytes (get m1) b (ofs + Z.of_nat (length bytes1)));
      try discriminate.
      inversion Hf;
      inversion x;
      inversion x0;
      subst.
      autorewrite with lens.
      reflexivity.
    lift_partial Mem.storebytes_split.
      autorewrite with lift in *.
      simpl in *.
      debug eauto with lift.
      unfold lift; simpl.
      autorewrite with lens.
      rewrite Hf0r.
      autorewrite with lens.
      unfold lift in *; simpl in *.
      destruct (Mem.storebytes (get m) b ofs (bytes1 ++ bytes2));
        try discriminate.
      inversion x.
      autorewrite with lens.
      reflexivity.
    lift Mem.alloc_result.
    lift Mem.nextblock_alloc.
    lift Mem.valid_block_alloc.
    lift Mem.fresh_block_alloc.
    lift Mem.valid_new_block.
    lift Mem.valid_block_alloc_inv.
    lift Mem.perm_alloc_1.
    lift Mem.perm_alloc_2.
    lift Mem.perm_alloc_3.
    lift Mem.perm_alloc_4.
    lift Mem.perm_alloc_inv.
    lift Mem.valid_access_alloc_other.
    lift Mem.valid_access_alloc_same.
    lift Mem.valid_access_alloc_inv.
    lift Mem.load_alloc_unchanged.
    lift Mem.load_alloc_other.
    lift Mem.load_alloc_same.
    lift Mem.load_alloc_same'.
    lift Mem.range_perm_free.
    lift Mem.free_range_perm.
    lift Mem.nextblock_free.
    lift Mem.valid_block_free_1.
    lift Mem.valid_block_free_2.
    lift Mem.perm_free_1.
    lift Mem.perm_free_2.
    lift Mem.perm_free_3.
    lift Mem.valid_access_free_1.
    lift Mem.valid_access_free_2.
    lift Mem.valid_access_free_inv_1.
    lift Mem.valid_access_free_inv_2.
    lift Mem.load_free.
    lift Mem.nextblock_drop.
    lift Mem.drop_perm_valid_block_1.
    lift Mem.drop_perm_valid_block_2.
    lift Mem.range_perm_drop_1.
    lift Mem.range_perm_drop_2.
    lift Mem.perm_drop_1.
    lift Mem.perm_drop_2.
    lift Mem.perm_drop_3.
    lift Mem.perm_drop_4.
    lift Mem.load_drop.
    lift Mem.extends_refl.
    lift Mem.load_extends.
    lift Mem.loadv_extends.
    lift Mem.loadbytes_extends.
    lift Mem.store_within_extends.
    lift Mem.store_outside_extends.
    lift Mem.storev_extends.
    lift Mem.storebytes_within_extends.
    lift Mem.storebytes_outside_extends.
    lift Mem.alloc_extends.
    lift Mem.free_left_extends.
    lift Mem.free_right_extends.
    lift Mem.free_parallel_extends.
    lift Mem.valid_block_extends.
    lift Mem.perm_extends.
    lift Mem.valid_access_extends.
    lift Mem.valid_pointer_extends.
    lift Mem.weak_valid_pointer_extends.
    lift Mem.mi_freeblocks.
    lift Mem.valid_block_inject_1.
    lift Mem.valid_block_inject_2.
    lift Mem.perm_inject.
    lift Mem.range_perm_inject.
    lift Mem.valid_access_inject.
    lift Mem.valid_pointer_inject.
    lift Mem.weak_valid_pointer_inject.
    lift Mem.address_inject.
    lift Mem.valid_pointer_inject_no_overflow.
    lift Mem.weak_valid_pointer_inject_no_overflow.
    lift Mem.valid_pointer_inject_val.
    lift Mem.weak_valid_pointer_inject_val.
    lift Mem.inject_no_overlap.
    lift Mem.different_pointers_inject.
    lift Mem.disjoint_or_equal_inject.
    lift Mem.aligned_area_inject.
    lift Mem.load_inject.
    lift Mem.loadv_inject.
    lift Mem.loadbytes_inject.
    lift Mem.store_mapped_inject.
    lift Mem.store_unmapped_inject.
    lift Mem.store_outside_inject.
    lift Mem.storev_mapped_inject.
    lift Mem.storebytes_mapped_inject.
    lift Mem.storebytes_unmapped_inject.
    lift Mem.storebytes_outside_inject.
    lift Mem.alloc_right_inject.
    lift Mem.alloc_left_unmapped_inject.
    lift Mem.alloc_left_mapped_inject.
    lift Mem.alloc_parallel_inject.
    lift Mem.free_left_inject.
    lift Mem.free_list_left_inject.
    lift Mem.free_right_inject.
    lift Mem.perm_free_list.
    lift Mem.free_inject.
    lift Mem.drop_outside_inject.
    lift Mem.neutral_inject.
    lift Mem.empty_inject_neutral.
    lift Mem.alloc_inject_neutral.
    lift Mem.store_inject_neutral.
    lift Mem.drop_inject_neutral.
    exact tt.
  Defined.
End LIFTMEM.
