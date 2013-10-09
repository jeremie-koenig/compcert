Require Import Coqlib.
Require Import Values.
Require Import Memtype.

Module Mem.
  Export Memtype.Mem.

  Class WithTagsOps tag mem
    `{mm_ops: Mem.ModelOps mem} :=
  {
    tget: mem -> block -> option tag;
    alloc (t: tag) (m: mem) (lo hi: Z): mem * block 
  }.

  Global Instance replace_alloc_ops {mem} alloc (ops: MemoryOps mem): MemoryOps mem | 10 := {
    empty := Mem.empty;
    nextblock := Mem.nextblock;
    alloc := alloc;
    free := Mem.free;
    load := Mem.load;
    store := Mem.store;
    loadbytes := Mem.loadbytes;
    storebytes := Mem.storebytes;
    perm := Mem.perm;
    valid_pointer := Mem.valid_pointer;
    drop_perm := Mem.drop_perm;
    extends := Mem.extends
  }.

  Class WithTags tag mem
    `{mwt_ops: WithTagsOps tag mem} :=
  {
    withtags_base_model :> MemoryModel mem;

    withtags_per_tag_states (t: tag) :>
      MemoryStates mem (mem_ops := replace_alloc_ops (alloc t) _);

    tget_valid m b:
      valid_block m b <-> (tget m b <> None);

    tget_store chunk m1 b ofs v m2:
      store chunk m1 b ofs v = Some m2 ->
      forall b', tget m2 b' = tget m1 b';

    tget_storebytes m1 b ofs bytes m2:
      storebytes m1 b ofs bytes = Some m2 ->
      forall b', tget m2 b' = tget m1 b';

    tget_free m1 bf lo hi m2:
      free m1 bf lo hi = Some m2 ->
      forall b, tget m2 b = tget m1 b;

    tget_drop m b lo hi p m':
      drop_perm m b lo hi p = Some m' ->
      forall b', tget m' b' = tget m b';

    tget_alloc_same m lo hi t m' b':
      alloc t m lo hi = (m', b') ->
      tget m' b' = Some t;

    tget_alloc_other m lo hi t m' b':
      alloc t m lo hi = (m', b') ->
      forall b, b <> b' -> tget m' b = tget m b
  }.
End Mem.
