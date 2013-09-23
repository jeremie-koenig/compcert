Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Import Functor.
Require Import Monad.
Require Import Lens.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.

(** * Prerequisites *)

(** We're going to lift the memory operations and theorems from a base
  type [bmem] to a "richer" type [mem], which contains [bmem] as a
  component. Formally, this means that we have a [Lens mem bmem] which
  provides us with well-behaved accessors to the [bmem] component
  inside of [mem]. While this is enough to lift most of the memory
  operations and theorems, we do have additional prerequisites. *)

(** First, in order to lift [MemoryOps], we need to know the value of
  the empty memory state of the richer type [mem]; indeed there's no
  way we would be able to construct that just from [empty : bmem].
  However, the simpler memory state contained within this empty [mem]
  should correspond to the empty [bmem] from the base memory states. *)

Class LiftMemoryOps (mem bmem: Type)
  `{bmem_ops: Mem.MemoryOps bmem}
  `{bmem_get: Getter mem bmem}
  `{bmem_set: Setter mem bmem} :=
{
  liftmem_empty: mem
}.

Class LiftMemoryStates (mem bmem: Type)
  `{mem_liftops: LiftMemoryOps mem bmem} :=
{
  liftmem_lens :> Lens mem bmem;
  liftmem_get_empty: get liftmem_empty = Mem.empty
}.

(** Furthermore, we need to know how the extra information fits with
  memory injections. Indeed, we could decide that, if the smaller
  [bmem] contained inside two [mem]'s inject into one another, then
  the larger memory states also inject into one another (that is,
  ignore the extra information for the purposes of memory injections),
  but then we would have no guarantee at all regarding the way in
  which this extra information evolves with program execution.
  The other extreme would be to simply make use of the powerset
  functor to lift [inject], so that two large memory states would
  inject into one another only if they contain exactly the same
  extra information. But this means it would be impossible for
  this extra information to evolve with program execution.

  Instead, we simply let the user specify how the extra information
  affects injection by giving a relation on the larger structures
  which is independent of the original memory states which are
  contained within. This is expressed by the
  [liftmem_inject_same_context] hypothesis below. Relations which
  respect this requirement are equivalent to relations on the quotient
  sets [mem / same_context], where [same_context] relates two larger
  memory states which differ only by the base memory state they
  contain. *)

Class LiftInjectOps (smem bsmem tmem btmem: Type)
  `{smem_lift_ops: LiftMemoryOps smem bsmem}
  `{tmem_lift_ops: LiftMemoryOps tmem btmem}
  `{stinj_ops: !Mem.InjectOps bsmem btmem} :=
{
  liftmem_context_inject: smem -> tmem -> Prop
}.

Class LiftInjections smem bsmem tmem btmem
  `{inj_lift_ops: LiftInjectOps smem bsmem tmem btmem} :=
{
  liftinj_sspec :> LiftMemoryStates smem bsmem;
  liftinj_tspec :> LiftMemoryStates tmem btmem;
  liftmem_inject_same_context :>
    Proper (same_context ==> same_context ==> impl) liftmem_context_inject
}.

(** For homogenous injections, we must also require that [context_inject]
  be reflexive, so as to prove [neutral_inject]. If that proves to be too
  restrictive, we could introduce the equivalent [inject_neutral] for the
  context, and weaken the following to require only that [inject_neutral]
  elements be proper. *)

Class LiftModelOps mem bmem
  `{liftmem_ops: LiftMemoryOps mem bmem}
  `{inj_ops: !Mem.InjectOps bmem bmem}
  `{liftinj_ops: !LiftInjectOps mem bmem mem bmem}
  `{mm_ops: !Mem.ModelOps bmem} :=
{
}.

Class LiftModel mem bmem `{liftmm_ops: LiftModelOps mem bmem} :=
{
  lifthinj_liftinj :> LiftInjections mem bmem mem bmem;
  lifthinj_context_inject_refl :> Reflexive liftmem_context_inject
}.


(** * Lifting memory operations *)

Class Lift A B := { lift: A -> B }.

Section LIFT.
  Context {mem bmem} `{getb: Getter mem bmem} `{setb: Setter mem bmem}.
  Context `{HF: Functor}.

  (** Because [Mem.MemoryModel] contains so many theorems, we need some
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
  (** We can now use [lift] to define the operations of the comonadic
    memory states. *)

  Global Instance liftmem_ops `{mem_liftops: LiftMemoryOps}:
    Mem.MemoryOps mem :=
  {
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
      Mem.extends (get wm1) (get wm2)
  }.
End LIFTOPS.

(** * Lifting the properties *)

(** Now we lift the properties listed in [Mem.MemoryModel]: given a theorem
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

  Theorem lift_option_eq_same_context `{Hlss: !LensSetSet mem bmem}:
    forall (f: bmem -> option bmem) (wm wm': mem),
      lift f wm = Some wm' ->
      same_context wm wm'.
  Proof.
    intros f wm wm'.
    unfold lift; simpl.
    case (f (get wm)).
    * intros ? H; inversion H; subst.
      symmetry.
      apply lens_set_same_context.
    * discriminate.
  Qed.

  Theorem lift_option_same_context_eq `{Hlsg: !LensSetGet mem bmem}:
    forall (f: bmem -> option bmem) (wm wm': mem),
      f (get wm) = Some (get wm') ->
      same_context wm wm' ->
      lift f wm = Some wm'.
  Proof.
    intros f wm wm' Hc Hv.
    simpl.
    rewrite Hc; clear Hc.
    f_equal.
    rewrite Hv.
    apply lens_set_get.
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

  Context `{Hlss: !LensSetSet mem bmem}.

  Theorem lift_prod_eq_same_context (f: bmem -> bmem * A) (wm wm': mem) (a: A):
    lift f wm = (wm', a) ->
    same_context wm wm'.
  Proof.
    simpl.
    destruct (f (get wm)).
    intro H; inversion H; subst.
    symmetry.
    apply lens_set_same_context.
  Qed.
End LIFTPROD.

(** ** Lifting [Mem.MemoryModel] *)

Section LIFTDERIVED.
  Context `{HW: LiftMemoryStates}.

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

Ltac lift_reduce :=
  unfold lift in *; simpl in *;
  autorewrite with lens in *.

(** Replace [(extract Mem.empty)] by the underlying [Mem.empty]. *)
Hint Rewrite @liftmem_get_empty using typeclasses eauto: lens.

Hint Extern 10 => progress lift_reduce; now eauto: lift. 

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
    match type of Hf with
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
    split; [recurse Hl | recurse Hr].

  Ltac peel Hf leaftac :=
    let recurse Hf := peel Hf leaftac in
    try match goal with
      | _: LiftMemoryOps ?mem ?bmem |- forall (x: _), _ =>
        let x := fresh x in peel_intro bmem recurse Hf x
      | _: LiftMemoryOps ?mem ?bmem |- exists (x: _), _ =>
        let x := fresh x in peel_exists bmem recurse Hf x
      | _: LiftMemoryOps ?mem ?bmem |- { x: _ | _ } =>
        let x := fresh x in peel_exists bmem recurse Hf x
      | |- _ /\ _ =>
        peel_conj recurse Hf
      | |- ?T =>
        leaftac
    end.

  (** We're now ready to define our leaf tactic, and use it in
    conjunction with [peel] to solve the goals automatically. *)

  Ltac lift_leaf :=
    autorewrite with lift in *;
    simpl in *;
    eauto 10 with lift typeclass_instances.

  Ltac lift_partial f :=
    pose proof f as Hf;
    peel Hf lift_leaf.

  Ltac lift f :=
    now lift_partial f.

Section LIFTMEM.
  Context mem bmem `{Hmem: LiftMemoryStates mem bmem}.

  Hint Immediate lift_option_eq_preserves_context : lift.

  Global Instance liftmem_spec:
    Mem.MemoryStates bmem -> Mem.MemoryStates mem.
  Proof.
    intro Hbmem; esplit.
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
    lift Mem.perm_free_list.
    exact tt.
  Qed.
End LIFTMEM.

Section LIFTINJOPS.
  Context `{Hinj: LiftInjections}.

  Global Instance liftmem_inj `{inj_liftops: LiftInjectOps}:
    Mem.InjectOps smem tmem :=
  {
    inject i wm1 wm2 :=
      Mem.inject i (get wm1) (get wm2) /\
      liftmem_context_inject wm1 wm2
  }.

  (* Injection in the larger structure implies injection for the
    underlying original memory states. *)
  Theorem lift_inject_unlift ι (m1: smem) (m2: tmem):
    Mem.inject ι m1 m2 ->
    Mem.inject ι (get m1) (get m2).
  Proof.
    intros [H1 _].
    assumption.
  Qed.

  (* Triangle diagrams evolving on the left *)
  Theorem lift_inject_triangle_left ι1 m1 ι2 m1' m2:
    same_context m1 m1' ->
    Mem.inject ι1 m1 m2 ->
    Mem.inject ι2 (get m1') (get m2) ->
    Mem.inject ι2 m1' m2.
  Proof.
    intros Hsc [_ Hic] Him'.
    split.
    - assumption.
    - rewrite <- Hsc.
      assumption.
  Qed.

  (* Triangle diagrams evolving on the right *)
  Theorem lift_inject_triangle_right ι1 m2 ι2 m1 m2':
    same_context m2 m2' ->
    Mem.inject ι1 m1 m2 ->
    Mem.inject ι2 (get m1) (get m2') ->
    Mem.inject ι2 m1 m2'.
  Proof.
    intros Hsc [_ Hic] Him'.
    split.
    - assumption.
    - rewrite <- Hsc.
      assumption.
  Qed.

  (* Square diagrams *)
  Theorem lift_inject_square ι1 m1 m2 ι2 m1' m2':
    same_context m1 m1' ->
    same_context m2 m2' ->
    Mem.inject ι1 m1 m2 ->
    Mem.inject ι2 (get m1') (get m2') ->
    Mem.inject ι2 m1' m2'.
  Proof.
    intros Hsc1 Hsc2 [_ Hic] Him'.
    split; try assumption.
    rewrite <- Hsc1.
    rewrite <- Hsc2.
    assumption.
  Qed.
End LIFTINJOPS.

(* Do not simplify [Mem.inject] to solve our goals;
  we use the tactics below instead. *)
Arguments Mem.inject _ _ _ _ _ _ _ _ : simpl never.

Hint Resolve lift_inject_unlift : lift.

Ltac prove_premises :=
  autorewrite with lens;
  match goal with
    | [ |- same_context _ _] =>
      (eapply lift_option_eq_same_context; eassumption) ||
      (eapply lift_prod_eq_same_context; eassumption) ||
      reflexivity
      (*eapply lift_same_context_set_r*)
    | [ |- Mem.inject ?ι ?m1 ?m2] =>
      eassumption 
  end.

Ltac lift_injection :=
  (eapply lift_inject_triangle_left; prove_premises) ||
  (eapply lift_inject_triangle_right; prove_premises) ||
  (eapply lift_inject_square; prove_premises).

Hint Extern 10 (Mem.inject _ _ _) => lift_injection : lift.

Section LIFTINJ.
  Context `{Hinj: LiftInjections}.

  Global Instance liftinj_spec:
    Mem.MemoryInjections bsmem btmem -> Mem.MemoryInjections smem tmem.
  Proof.
    split.
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
    lift Mem.free_inject.
    lift Mem.drop_outside_inject.
  Qed.
End LIFTINJ.

Section LIFTMS.
  Context `{Hinj: LiftModel}.

  Global Instance lift_mm_ops: Mem.ModelOps mem := {
    inject_neutral thr wm :=
      Mem.inject_neutral thr (get wm)
  }.

  Global Instance lift_mem:
    Mem.MemoryModel bmem -> Mem.MemoryModel mem := {}.
  Proof.
    lift Mem.empty_inject_neutral.
    lift Mem.alloc_inject_neutral.
    lift Mem.store_inject_neutral.
    lift Mem.drop_inject_neutral.
    lift_partial Mem.neutral_inject.
      split; now eauto with lift.
  Qed.
End LIFTMS.
