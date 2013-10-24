Require Import Coq.Program.Basics.
Require Import Coq.Classes.Morphisms.
Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Import Functor.
Require Import Monad.
Require Import Lens.
Require Export Lift.

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

Class LiftMemoryOps {mem bmem: Type} (π: mem -> bmem)
  `{bmem_ops: Mem.MemoryOps bmem}
  `{bmem_set: !LensOps π} :=
{
  liftmem_empty: mem
}.

Class LiftMemoryStates {mem bmem: Type} (π: mem -> bmem)
  `{mem_liftops: LiftMemoryOps _ _ π}: Prop :=
{
  liftmem_lens :> Lens π;
  liftmem_get_empty: get π liftmem_empty = Mem.empty
}.

(** Furthermore, we need to know how the extra information fits with
  memory injections. Indeed, we could decide that, if the smaller
  [bmem]s contained inside two [mem]s inject into one another, then
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

Class LiftInjectOps {smem bsmem tmem btmem} (σ: smem -> bsmem) (τ: tmem -> btmem)
  `{smem_lift_ops: LiftMemoryOps smem bsmem σ}
  `{tmem_lift_ops: LiftMemoryOps tmem btmem τ}
  `{stinj_ops: !Mem.InjectOps bsmem btmem} :=
{
  liftmem_context_inject: smem -> tmem -> Prop
}.

Class LiftInjections {smem bsmem tmem btmem} σ τ
  `{inj_lift_ops: LiftInjectOps smem bsmem tmem btmem σ τ}: Prop :=
{
  liftinj_sspec :> LiftMemoryStates σ;
  liftinj_tspec :> LiftMemoryStates τ;
  liftmem_inject_same_context :>
    Proper (same_context σ ==> same_context τ ==> impl) liftmem_context_inject
}.

(** For homogenous injections, we must also require that [context_inject]
  be reflexive, so as to prove [neutral_inject]. If that proves to be too
  restrictive, we could introduce the equivalent [inject_neutral] for the
  context, and weaken the following to require only that [inject_neutral]
  elements be proper. *)

Class LiftModelOps {mem bmem} (π: mem -> bmem)
  `{liftmem_ops: LiftMemoryOps mem bmem π}
  `{inj_ops: !Mem.InjectOps bmem bmem}
  `{liftinj_ops: !LiftInjectOps π π}
  `{mm_ops: !Mem.ModelOps bmem} :=
{
}.

Class LiftModel {mem bmem} (π: mem -> bmem)
  `{liftmm_ops: LiftModelOps mem bmem π}: Prop :=
{
  lifthinj_liftinj :> LiftInjections π π;
  lifthinj_context_inject_refl :> Reflexive liftmem_context_inject
}.

(** Using all of this, we can build a set of memory operations on the
  source type [mem] from the operations on the view type [bmem]. *)

Section LIFTOPS.
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
      lift Mem.extends wm1 wm2
  }.
End LIFTOPS.

(** * Lifting the properties *)

Section LIFTDERIVED.
  Context `{HW: LiftMemoryStates}.

  (** Show that the operations derived from the [Mem.MemoryOps]
    instance above are equivalent to lifting the operations derived
    from the original [Mem.MemoryOps]. *)

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
    intros; lift_simpl; lift_unfold.
    * reflexivity.
    * destruct (Mem.free (get π wm) b lo hi); [| reflexivity].
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

(** Replace [(get Mem.empty)] by the underlying [Mem.empty]. *)
Hint Rewrite
  @liftmem_get_empty
  using typeclasses eauto: lens.

Section LIFTMEM.
  Context mem bmem `{Hmem: LiftMemoryStates mem bmem}.

  Local Arguments fmap : simpl never.

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
    lift Mem.storebytes_concat.
    lift Mem.storebytes_split.
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

Section LIFTINJ.
  Context `{Hinj: LiftInjections}.

  Global Instance liftmem_inj: Mem.InjectOps smem tmem :=
  {
    inject i wm1 wm2 :=
      Mem.inject i (get σ wm1) (get τ wm2) /\
      liftmem_context_inject wm1 wm2
  }.

  (** A version of [liftmem_inject_same_context] fine-tuned
    for use with eauto *)
  Lemma liftmem_inject_same_context_2 m1 n1 m2 n2:
    liftmem_context_inject m1 m2 ->
    same_context σ m1 n1 ->
    same_context τ m2 n2 ->
    liftmem_context_inject n1 n2.
  Proof.
    intros H H1 H2.
    eapply liftmem_inject_same_context;
    eassumption.
  Qed.

  Hint Immediate liftmem_inject_same_context_2 : lift.

  Global Instance liftinj_spec:
    Mem.MemoryInjections bsmem btmem -> Mem.MemoryInjections smem tmem.
  Proof.
    split; try typeclasses eauto.
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
      Mem.inject_neutral thr (get π wm)
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
