Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Import Monad.

(** * Prerequisites *)

Class LiftMemOps (W: Type -> Type) := {
  liftmem_comonad_ops :> ComonadOps W;
  lift_empty {mem}: mem -> W mem
}.

Class LiftMem (W: Type -> Type) `{Wmemops: LiftMemOps W}: Prop := {
  liftmem_comonad :> Comonad W;
  lift_empty_extract {mem} (m: mem):
    extract (lift_empty m) = m
}.

(** * Lifting memory operations *)

Section LIFT.
  Context `{HW: ComonadOps} `{HF: Functor} {mem: Type}.

  (** Because [Mem.MemSpec] contains so many theorems, we need some
    systematic way to lift the memory operations on [W mem], so that
    the lifting of the theorems is convenient to automate.

    The signature of most of the memory operations are variations on
    the theme [mem -> F mem], where [F] is a functor such as [option]
    or [- * Z]. We need to lift them to [W mem -> F (W mem)]. Note
    that using the comonad's [fmap] is not possible because that would
    yield a function of type [W mem -> W (F mem)]. Instead, we use
    the following: *)

  Definition lift (f: mem -> F mem) (wm: W mem) :=
    fmap (fun m' => set m' wm) (f (extract wm)).

  (** Here are some basic theorems about [lift] with any functor. *)

  Theorem lift_mor (f g: mem -> F mem) (wa: W mem):
    f (extract wa) = g (extract wa) ->
    lift f wa = lift g wa.
  Proof.
    intros Hfg.
    unfold lift.
    apply f_equal.
    assumption.
  Qed.
End LIFT.

Section LIFTOPS.
  Context W `{Wmemops: LiftMemOps W}.
  Context mem `{mem_ops: Mem.MemOps mem}.

  (** We can now use [lift] to define the operations of the comonadic
    memory states. *)

  Global Instance liftmem_ops: Mem.MemOps (W mem) := {
    empty :=
      lift_empty Mem.empty;
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
      Mem.extends (extract wm1) (extract wm2);
    inject i wm1 wm2 :=
      Mem.inject i (extract wm1) (extract wm2);
    inject_neutral thr wm :=
      Mem.inject_neutral thr (extract wm)
  }.
End LIFTOPS.

(** * Lifting the properties *)

(** Now we lift the properties listed in [Mem.MemSpec]: given a theorem
  about [mem], we need to prove the equivalent theorem about [W mem]
  and the corresponding lifted operations it involves. To do this,
  we need some theorems about lift to help us rewrite our lifted goals
  to use the original theorems. *)

(** ** Properties of [lift (F:=option)] *)

Section LIFTOPTION.
  Context `{HW: Comonad} {mem: Type}.

  Lemma lift_option_eq (f: mem -> option mem):
    forall (wa wb: W mem),
      lift f wa = Some wb ->
      f (extract wa) = Some (extract wb).
  Proof.
    unfold lift; simpl; intros.
    destruct (f (extract wa)); try discriminate.
    inversion H.
    autorewrite with comonad.
    reflexivity.
  Qed.

  Lemma lift_option_eq_set_iff (f: mem -> option mem):
    forall (wm: W mem) (w': mem),
      lift f wm = Some (set w' wm) <->
      f (extract wm) = Some w'.
  Proof.
    simpl; intros.
    split; destruct (f (extract wm)); try discriminate;
    intro H; inversion H.
    - apply f_equal.
      eapply comonad_set_eq.
      eassumption.
    - reflexivity.
  Qed.

  Lemma lift_option_eq_set (f: mem -> option mem):
    forall (wm: W mem) (m': mem),
      f (extract wm) = Some m' ->
      lift f wm = Some (set m' wm).
  Proof.
    apply lift_option_eq_set_iff.
  Qed.

  Theorem lift_option_eq_preserves_context (f g: mem -> option mem):
    forall (wm: W mem) (wm': W mem),
      g (extract wm) = Some (extract wm') ->
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
  Context `{HW: Comonad} {mem: Type} {A: Type}.
  Open Scope type_scope.

  Theorem lift_prod_eq (f: mem -> (fun X => X * A) mem) wm wm' a:
    lift f wm = (wm', a) ->
    f (extract wm) = (extract wm', a).
  Proof.
    simpl.
    destruct (f (extract wm)) as [m' a'].
    intros H.
    inversion H.
    autorewrite with comonad in *.
    reflexivity.
  Qed.

  Theorem lift_prod_eq_set (f: mem -> (fun X => X * A) mem) wm m' a:
    f (extract wm) = (m', a) ->
    lift f wm = (set m' wm, a).
  Proof.
    intro H; simpl.
    rewrite H; clear H; simpl.
    reflexivity.
  Qed.
End LIFTPROD.

(** ** Lifting [Mem.MemSpec] *)

Section LIFTDERIVED.
  Context `{HW: LiftMem} `{Hmem: Mem.MemSpec}.

  (** Now we must come up with a suitable leaf tactic.
    The first step for proving a lifted theorem involving an
    operation applied to a term [wm: W mem] is to rewrite it in
    terms of [lift] applied to the underlying operation. *)

  (** However for the derived operations we first need to show that
    the [W mem] versions are indeed equivalent to lifting the [mem]
    versions. *)

  Theorem lift_loadv chunk (wm: W mem) addr:
    Mem.loadv chunk wm addr =
    lift (fun m: mem => Mem.loadv chunk m addr) wm.
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

  Theorem lift_free_list (l: list (block * Z * Z)):
    forall (wm wm': W mem),
      Mem.free_list wm l = Some wm' ->
      lift (fun m => Mem.free_list m l) wm = Some (extract wm').
  Proof.
    induction l as [ | [[b lo] hi] l IHl];
    intros; simpl in *.
    - inversion H; congruence.
    - destruct (Mem.free (extract wm) b lo hi); try discriminate.
      rewrite <- (IHl (set m wm) wm').
      * autorewrite with comonad.
        reflexivity.
      * assumption.
  Qed.

  Theorem lift_valid_block (wm: W mem) (b: block):
    Mem.valid_block wm b <->
    lift (fun m => Mem.valid_block m b) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_range_perm (wm: W mem) b lo hi k p:
    Mem.range_perm wm b lo hi k p <->
    lift (fun m => Mem.range_perm m b lo hi k p) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_valid_access (wm: W mem) chunk b ofs p:
    Mem.valid_access wm chunk b ofs p <->
    lift (fun m => Mem.valid_access m chunk b ofs p) wm.
  Proof.
    reflexivity.
  Qed.

  Theorem lift_weak_valid_pointer (wm: W mem) b ofs:
    Mem.weak_valid_pointer wm b ofs =
    lift (fun m => Mem.weak_valid_pointer m b ofs) wm.
  Proof.
    reflexivity.
  Qed.
End LIFTDERIVED.

  Hint Rewrite
    @lift_loadv
    @lift_storev
    @lift_valid_block
    @lift_range_perm
    @lift_valid_access
    @lift_weak_valid_pointer
    using typeclasses eauto : lift.

  Hint Resolve
    lift_free_list
    : lift.

  (** For the fields of [Mem.MemOps], which are defined in terms
    of [lift] to begin with, we can use [simpl], making sure that
    we stop once we reach [lift]: *)

  Arguments lift _ _ _ _ _ _ _ : simpl never.

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
  Hint Extern 10 => rewrite !comonad_extract_set in *: lift.

  (** For the premises we need to apply them explicitely. *)

  Ltac lift_premise :=
    match goal with
      | [ H: Mem.free_list _ _ = _ |- _ ] =>
        eapply lift_free_list in H
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
  Hint Extern 10 => rewrite !lift_empty_extract in *: lift.


Section LIFTMEM.
  Context W `{HW: LiftMem W} `{Hmem: Mem.MemSpec}.

  (** This is the main tactic we use: it lifts a theorem [Hf] of
    the underlying memory model by "peeling off" its structure
    recursively to prove the lifted goal. The leaf goals are
    handled with the caller-provided tactic [leaftac]. *)

  (* Premises are "translated" and used to specialize Hf *)
  Ltac peel_intro recurse Hf x :=
    intro x;
    let T := type of x in
    lazymatch type of Hf with
      (* No transformation required, just pass it along. *)
      | forall (y: T), _ =>
	specialize (Hf x)

      (* [mem] argument, use [extract] *)
      | forall (m: mem), _ =>
	specialize (Hf (extract x))

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
  Ltac peel_exists recurse Hf x :=
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
      | |- forall (x: _), _ =>
        let x := fresh x in peel_intro recurse Hf x
      | |- exists (x: _), _ =>
        let x := fresh x in peel_exists recurse Hf x
      | |- { x: _ | _ } =>
        let x := fresh x in peel_exists recurse Hf x
      | |- _ /\ _ =>
        peel_conj recurse Hf
      | |- ?T =>
        leaftac tt
    end.

  (** We're now ready to define our leaf tactic, and use it in
    conjunction with [peel] to solve the goals automatically. *)

  Ltac lift_leaf f :=
    autorewrite with lift in *; simpl in *;
    eauto 10 using f with lift typeclass_instances.

  Ltac lift_partial f :=
    pose proof f as Hf;
    peel Hf lift_leaf.

  Ltac lift f :=
    now lift_partial f.

  Hint Immediate
    (lift_option_eq_preserves_context (W:=W))
    : lift.

  Global Instance liftmem_spec: Mem.MemSpec (W mem).
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
      unfold lift in *; simpl in *.
      destruct (Mem.storebytes (extract m) b ofs (bytes1 ++ bytes2));
      destruct (Mem.storebytes (extract m) b ofs bytes1);
      destruct (Mem.storebytes (extract m1) b (ofs + Z.of_nat (length bytes1)));
      try discriminate.
      inversion Hf;
      inversion x;
      inversion x0;
      subst.
      autorewrite with comonad.
      reflexivity.
    intros m b ofs bytes1 bytes2 m2.
      pose proof (Mem.storebytes_split (extract m) b ofs bytes1 bytes2 (extract m2)) as Hf.
      (*FIXME: *) admit.
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
  Defined.
End LIFTMEM.
