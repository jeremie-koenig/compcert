Require Import Coqlib.
Require Import Values.
Require Import Memdata.
Require Import Memtype.
Require Import MemWithTags.
Require Import Lens.
Require Import LiftMem.
Require Import AbstractData.

Class MemTagOps (tag: Type) := {
  tag_default: tag
}.

Class MemTags tag `{tag_ops: MemTagOps tag}: Prop := {
}.

Section WITHMEM.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Htag: MemTags}.

  Global Instance tagmap_data_ops: AbstractDataOps (block -> tag) := {
    empty_data := (fun _ => tag_default)
  }.

  Definition mwt `{tag_ops: MemTagOps tag} := (mem × (block -> tag)).

  Definition mwt_tget (m: mwt) (b: block) :=
    if zlt b (Mem.nextblock m) then
      Some (snd m b)
    else
      None.

  Definition mwt_settag (b: block) (t: tag) (tm: block -> tag) :=
    fun (b': block) => if zeq b b' then t else tm b'.

  Definition mwt_alloc (t: tag) (m: mwt) (lo hi: block): mwt * block :=
    match Memtype.Mem.alloc (fst m) lo hi with
     | (m', b) => ((m', mwt_settag b t (snd m)), b)
    end.

  Global Instance mwt_tag_ops: Mem.WithTagsOps tag mwt := {
    tget := mwt_tget;
    alloc := mwt_alloc
  }.

  Global Instance mwt_per_tag_spec (t: tag):
    Mem.MemoryStates mwt (mem_ops := Mem.replace_alloc_ops (mwt_alloc t) _) | 10.
  Proof.
    econstructor.
    exact (Mem.nextblock_pos (mem_ops := liftmem_ops)).
    exact (Mem.valid_not_valid_diff (mem_ops := liftmem_ops)).
    exact (Mem.perm_implies (mem_ops := liftmem_ops)).
    exact (Mem.perm_cur_max (mem_ops := liftmem_ops)).
    exact (Mem.perm_cur (mem_ops := liftmem_ops)).
    exact (Mem.perm_max (mem_ops := liftmem_ops)).
    exact (Mem.perm_valid_block (mem_ops := liftmem_ops)).
    exact (Mem.perm_dec (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_implies (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_cur (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_max (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_implies (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_valid_block (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_perm (mem_ops := liftmem_ops)).
    exact (Mem.valid_pointer_nonempty_perm (mem_ops := liftmem_ops)).
    exact (Mem.valid_pointer_valid_access (mem_ops := liftmem_ops)).
    exact (Mem.weak_valid_pointer_spec (mem_ops := liftmem_ops)).
    exact (Mem.valid_pointer_implies (mem_ops := liftmem_ops)).
    exact (Mem.nextblock_empty (mem_ops := liftmem_ops)).
    exact (Mem.perm_empty (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_empty (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_load (mem_ops := liftmem_ops)).
    exact (Mem.load_valid_access (mem_ops := liftmem_ops)).
    exact (Mem.load_type (mem_ops := liftmem_ops)).
    exact (Mem.load_cast (mem_ops := liftmem_ops)).
    exact (Mem.load_int8_signed_unsigned (mem_ops := liftmem_ops)).
    exact (Mem.load_int16_signed_unsigned (mem_ops := liftmem_ops)).
    exact (Mem.load_float64al32 (mem_ops := liftmem_ops)).
    exact (Mem.loadv_float64al32 (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_loadbytes (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_range_perm (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_load (mem_ops := liftmem_ops)).
    exact (Mem.load_loadbytes (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_length (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_empty (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_concat (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_split (mem_ops := liftmem_ops)).
    exact (Mem.nextblock_store (mem_ops := liftmem_ops)).
    exact (Mem.store_valid_block_1 (mem_ops := liftmem_ops)).
    exact (Mem.store_valid_block_2 (mem_ops := liftmem_ops)).
    exact (Mem.perm_store_1 (mem_ops := liftmem_ops)).
    exact (Mem.perm_store_2 (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_store (mem_ops := liftmem_ops)).
    exact (Mem.store_valid_access_1 (mem_ops := liftmem_ops)).
    exact (Mem.store_valid_access_2 (mem_ops := liftmem_ops)).
    exact (Mem.store_valid_access_3 (mem_ops := liftmem_ops)).
    exact (Mem.load_store_similar (mem_ops := liftmem_ops)).
    exact (Mem.load_store_same (mem_ops := liftmem_ops)).
    exact (Mem.load_store_other (mem_ops := liftmem_ops)).
    exact (Mem.load_store_pointer_overlap (mem_ops := liftmem_ops)).
    exact (Mem.load_store_pointer_mismatch (mem_ops := liftmem_ops)).
    exact (Mem.load_pointer_store (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_store_same (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_store_other (mem_ops := liftmem_ops)).
    exact (Mem.store_signed_unsigned_8 (mem_ops := liftmem_ops)).
    exact (Mem.store_signed_unsigned_16 (mem_ops := liftmem_ops)).
    exact (Mem.store_int8_zero_ext (mem_ops := liftmem_ops)).
    exact (Mem.store_int8_sign_ext (mem_ops := liftmem_ops)).
    exact (Mem.store_int16_zero_ext (mem_ops := liftmem_ops)).
    exact (Mem.store_int16_sign_ext (mem_ops := liftmem_ops)).
    exact (Mem.store_float32_truncate (mem_ops := liftmem_ops)).
    exact (Mem.store_float64al32 (mem_ops := liftmem_ops)).
    exact (Mem.storev_float64al32 (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_storebytes (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_range_perm (mem_ops := liftmem_ops)).
    exact (Mem.perm_storebytes_1 (mem_ops := liftmem_ops)).
    exact (Mem.perm_storebytes_2 (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_valid_access_1 (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_valid_access_2 (mem_ops := liftmem_ops)).
    exact (Mem.nextblock_storebytes (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_valid_block_1 (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_valid_block_2 (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_store (mem_ops := liftmem_ops)).
    exact (Mem.store_storebytes (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_storebytes_same (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_storebytes_other (mem_ops := liftmem_ops)).
    exact (Mem.load_storebytes_other (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_concat (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_split (mem_ops := liftmem_ops)).
    admit. (* exact (Mem.alloc_result (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.nextblock_alloc (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.valid_block_alloc (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.fresh_block_alloc (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.valid_new_block (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.valid_block_alloc_inv (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.perm_alloc_1 (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.perm_alloc_2 (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.perm_alloc_3 (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.perm_alloc_4 (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.perm_alloc_inv (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.valid_access_alloc_other (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.valid_access_alloc_same (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.valid_access_alloc_inv (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.load_alloc_unchanged (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.load_alloc_other (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.load_alloc_same (mem_ops := liftmem_ops)). *)
    admit. (* exact (Mem.load_alloc_same' (mem_ops := liftmem_ops)). *)
    exact (Mem.range_perm_free (mem_ops := liftmem_ops)).
    exact (Mem.free_range_perm (mem_ops := liftmem_ops)).
    exact (Mem.nextblock_free (mem_ops := liftmem_ops)).
    exact (Mem.valid_block_free_1 (mem_ops := liftmem_ops)).
    exact (Mem.valid_block_free_2 (mem_ops := liftmem_ops)).
    exact (Mem.perm_free_1 (mem_ops := liftmem_ops)).
    exact (Mem.perm_free_2 (mem_ops := liftmem_ops)).
    exact (Mem.perm_free_3 (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_free_1 (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_free_2 (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_free_inv_1 (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_free_inv_2 (mem_ops := liftmem_ops)).
    exact (Mem.load_free (mem_ops := liftmem_ops)).
    exact (Mem.nextblock_drop (mem_ops := liftmem_ops)).
    exact (Mem.drop_perm_valid_block_1 (mem_ops := liftmem_ops)).
    exact (Mem.drop_perm_valid_block_2 (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_drop_1 (mem_ops := liftmem_ops)).
    exact (Mem.range_perm_drop_2 (mem_ops := liftmem_ops)).
    exact (Mem.perm_drop_1 (mem_ops := liftmem_ops)).
    exact (Mem.perm_drop_2 (mem_ops := liftmem_ops)).
    exact (Mem.perm_drop_3 (mem_ops := liftmem_ops)).
    exact (Mem.perm_drop_4 (mem_ops := liftmem_ops)).
    exact (Mem.load_drop (mem_ops := liftmem_ops)).
    exact (Mem.extends_refl (mem_ops := liftmem_ops)).
    exact (Mem.load_extends (mem_ops := liftmem_ops)).
    exact (Mem.loadv_extends (mem_ops := liftmem_ops)).
    exact (Mem.loadbytes_extends (mem_ops := liftmem_ops)).
    exact (Mem.store_within_extends (mem_ops := liftmem_ops)).
    exact (Mem.store_outside_extends (mem_ops := liftmem_ops)).
    exact (Mem.storev_extends (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_within_extends (mem_ops := liftmem_ops)).
    exact (Mem.storebytes_outside_extends (mem_ops := liftmem_ops)).
    admit. (* exact (Mem.alloc_extends (mem_ops := liftmem_ops)). *)
    exact (Mem.free_left_extends (mem_ops := liftmem_ops)).
    exact (Mem.free_right_extends (mem_ops := liftmem_ops)).
    exact (Mem.free_parallel_extends (mem_ops := liftmem_ops)).
    exact (Mem.valid_block_extends (mem_ops := liftmem_ops)).
    exact (Mem.perm_extends (mem_ops := liftmem_ops)).
    exact (Mem.valid_access_extends (mem_ops := liftmem_ops)).
    exact (Mem.valid_pointer_extends (mem_ops := liftmem_ops)).
    exact (Mem.weak_valid_pointer_extends (mem_ops := liftmem_ops)).
    exact (Mem.perm_free_list (mem_ops := liftmem_ops)).
    exact tt.
  Qed.

  Lemma same_context_same_tag (m1 m2: mem) (t1 t2: block -> tag):
    same_context fst (m1, t1) (m2, t2) -> t1 = t2.
  Proof.
    intros H.
    unfold same_context in H.
    specialize (H m1).
    inv H.
    reflexivity.
  Qed.

  Global Instance mwt_tag_spec: Mem.WithTags tag mwt := {}.
  Proof.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  Qed.
End WITHMEM.
