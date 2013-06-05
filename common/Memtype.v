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

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.

(** Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is associated to permissions, also known as access rights.
  The following permissions are expressible:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
*)

Inductive permission: Type :=
  | Freeable: permission
  | Writable: permission
  | Readable: permission
  | Nonempty: permission.

(** In the list, each permission implies the other permissions further down the
    list.  We reflect this fact by the following order over permissions. *)

Inductive perm_order: permission -> permission -> Prop :=
  | perm_refl:  forall p, perm_order p p
  | perm_F_any: forall p, perm_order Freeable p
  | perm_W_R:   perm_order Writable Readable
  | perm_any_N: forall p, perm_order p Nonempty.

Hint Constructors perm_order: mem.

Lemma perm_order_trans:
  forall p1 p2 p3, perm_order p1 p2 -> perm_order p2 p3 -> perm_order p1 p3.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

(** Each address has not one, but two permissions associated
  with it.  The first is the current permission.  It governs whether
  operations (load, store, free, etc) over this address succeed or
  not.  The other is the maximal permission.  It is always at least as
  strong as the current permission.  Once a block is allocated, the
  maximal permission of an address within this block can only
  decrease, as a result of [free] or [drop_perm] operations, or of
  external calls.  In contrast, the current permission of an address
  can be temporarily lowered by an external call, then raised again by
  another external call. *)

Inductive perm_kind: Type :=
  | Max: perm_kind
  | Cur: perm_kind.

Module Mem.

Class MemOps (mem: Type) := {

nullptr: block := 0;

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
empty: mem;

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation. *)
nextblock: mem -> block;

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
alloc: forall (m: mem) (lo hi: Z), mem * block;

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
free: forall (m: mem) (b: block) (lo hi: Z), option mem;

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val;

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem;

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Int.unsigned ofs)
  | _ => None
  end;

storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Int.unsigned ofs) v
  | _ => None
  end;

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval);

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem;

(** [free_list] frees all the given (block, lo, hi) triples. *)
free_list := fix free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end;

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop;

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool;

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)
drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem;

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)
extends: mem -> mem -> Prop;

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
  - if [f b = None], the block [b] of [m1] has no equivalent in [m2];
  - if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
    a sub-block at offset [ofs] of the block [b'] in [m2].

  A memory injection [f] defines a relation [val_inject] between values
  that is the identity for integer and float values, and relocates pointer 
  values as prescribed by [f].  (See module [Values].)

  Likewise, a memory injection [f] defines a relation between memory states 
  that we axiomatize below. *)
inject: meminj -> mem -> mem -> Prop;

(** Memory states that inject into themselves. *)
inject_neutral: forall (thr: block) (m: mem), Prop

}.

Section MEMOPS_DEFS.

Context `{mem_ops: MemOps}.

(** Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)
Definition valid_block (m: mem) (b: block) :=
  b < nextblock m.

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)
Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

End MEMOPS_DEFS.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if zlt b thr then Some(b, 0) else None.

Class MemSpec (mem: Type) `{mem_ops: MemOps mem} := {

(** * Permissions, block validity, access validity, and bounds *)

nextblock_pos m:
  nextblock m > 0;

valid_not_valid_diff m b b':
  valid_block m b -> ~(valid_block m b') -> b <> b';

(** Logical implications between permissions *)

perm_implies m b ofs k p1 p2:
  perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2;

(** The current permission is always less than or equal to the maximal permission. *)

perm_cur_max m b ofs p:
  perm m b ofs Cur p -> perm m b ofs Max p;
perm_cur m b ofs k p:
  perm m b ofs Cur p -> perm m b ofs k p;
perm_max m b ofs k p:
  perm m b ofs k p -> perm m b ofs Max p;

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
perm_valid_block m b ofs k p:
  perm m b ofs k p -> valid_block m b;

(** The [Mem.perm] predicate is decidable. *)
perm_dec m b ofs k p:
  {perm m b ofs k p} + {~ perm m b ofs k p};

range_perm_implies m b lo hi k p1 p2:
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2;
range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p;
range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p;

valid_access_implies m chunk b ofs p1 p2:
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2;

valid_access_valid_block m chunk b ofs:
  valid_access m chunk b ofs Nonempty ->
  valid_block m b;

valid_access_perm m chunk b ofs k p:
  valid_access m chunk b ofs p ->
  perm m b ofs k p;

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

valid_pointer_nonempty_perm m b ofs:
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty;
valid_pointer_valid_access m b ofs:
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty;

weak_valid_pointer_spec m b ofs:
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true;
valid_pointer_implies m b ofs:
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true;

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

nextblock_empty:
  nextblock empty = 1;
perm_empty:
  forall b ofs k p, ~perm empty b ofs k p;
valid_access_empty chunk b ofs p:
  ~valid_access empty chunk b ofs p;

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
valid_access_load m chunk b ofs:
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v;
load_valid_access m chunk b ofs v:
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable;

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
load_type m chunk b ofs v:
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk);

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
load_cast m chunk b ofs v:
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end;

load_int8_signed_unsigned m b ofs:
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs);

load_int16_signed_unsigned m b ofs:
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs);

load_float64al32:
  forall m b ofs v,
  load Mfloat64 m b ofs = Some v -> load Mfloat64al32 m b ofs = Some v;

loadv_float64al32:
  forall m a v,
  loadv Mfloat64 m a = Some v -> loadv Mfloat64al32 m a = Some v;


(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

range_perm_loadbytes m b ofs len:
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes;
loadbytes_range_perm m b ofs len bytes:
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable;

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
loadbytes_load chunk m b ofs bytes:
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes);

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
load_loadbytes chunk m b ofs v:
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes;

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
loadbytes_length m b ofs n bytes:
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n;

loadbytes_empty m b ofs n:
  n <= 0 -> loadbytes m b ofs n = Some nil;

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
loadbytes_concat m b ofs n1 n2 bytes1 bytes2:
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2);
loadbytes_split m b ofs n1 n2 bytes:
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1 
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2;

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)

nextblock_store chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1;
store_valid_block_1 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
store_valid_block_2 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

perm_store_1 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
perm_store_2 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;

valid_access_store m1 chunk b ofs v:
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 };
store_valid_access_1 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
store_valid_access_2 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
store_valid_access_3 chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable;

(** Load-store properties. *)

load_store_similar chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v';

load_store_same chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  load chunk m2 b ofs = Some (Val.load_result chunk v);

load_store_other chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs';

(** Integrity of pointer values. *)

load_store_pointer_overlap chunk m1 b ofs v_b v_o m2 chunk' ofs' v:
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef;
load_store_pointer_mismatch chunk m1 b ofs v_b v_o m2 chunk' v:
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  chunk <> Mint32 \/ chunk' <> Mint32 ->
  v = Vundef;
load_pointer_store chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' v_b v_o,
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (chunk = Mint32 /\ v = Vptr v_b v_o /\ chunk' = Mint32 /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs');

(** Load-store properties for [loadbytes]. *)

loadbytes_store_same chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v);
loadbytes_store_other chunk m1 b ofs v m2:
  store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n;

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

store_signed_unsigned_8 m b ofs v:
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v;
store_signed_unsigned_16 m b ofs v:
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v;
store_int8_zero_ext m b ofs n:
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n);
store_int8_sign_ext m b ofs n:
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n);
store_int16_zero_ext m b ofs n:
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n);
store_int16_sign_ext m b ofs n:
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n);
store_float32_truncate m b ofs n:
  store Mfloat32 m b ofs (Vfloat (Float.singleoffloat n)) =
  store Mfloat32 m b ofs (Vfloat n);
store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m';
storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m';

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

range_perm_storebytes m1 b ofs bytes:
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 };
storebytes_range_perm m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable;
perm_storebytes_1 m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
perm_storebytes_2 m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;
storebytes_valid_access_1 m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
storebytes_valid_access_2 m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
nextblock_storebytes m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  nextblock m2 = nextblock m1;
storebytes_valid_block_1 m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
storebytes_valid_block_2 m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

(** Connections between [store] and [storebytes]. *)

storebytes_store m1 b ofs chunk v m2:
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2;

store_storebytes m1 b ofs chunk v m2:
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2;

(** Load-store properties. *)

loadbytes_storebytes_same m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes;
loadbytes_storebytes_other m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
load_storebytes_other m1 b ofs bytes m2:
  storebytes m1 b ofs bytes = Some m2 ->
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs';

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

storebytes_concat m b ofs bytes1 m1 bytes2 m2:
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2;
storebytes_split m b ofs bytes1 bytes2 m2:
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2;

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

alloc_result m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  b = nextblock m1;

(** Effect of [alloc] on block validity. *)

nextblock_alloc m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  nextblock m2 = Zsucc (nextblock m1);

valid_block_alloc m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b';
fresh_block_alloc m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  ~(valid_block m1 b);
valid_new_block m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  valid_block m2 b;
valid_block_alloc_inv m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b';

(** Effect of [alloc] on permissions. *)

perm_alloc_1 m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p;
perm_alloc_2 m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable;
perm_alloc_3 m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi;
perm_alloc_4 m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p;
perm_alloc_inv m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, 
  perm m2 b' ofs k p ->
  if zeq b' b then lo <= ofs < hi else perm m1 b' ofs k p;

(** Effect of [alloc] on access validity. *)

valid_access_alloc_other m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p;
valid_access_alloc_same m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable;
valid_access_alloc_inv m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p;

(** Load-alloc properties. *)

load_alloc_unchanged m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs;
load_alloc_other m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v;
load_alloc_same m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef;
load_alloc_same' m1 lo hi m2 b:
  alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef;

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

range_perm_free m1 b lo hi:
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 };
free_range_perm m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  range_perm m1 bf lo hi Cur Freeable;

(** Block validity is preserved by [free]. *)

nextblock_free m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1;
valid_block_free_1 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b;
valid_block_free_2 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b;

(** Effect of [free] on permissions. *)

perm_free_1 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p;
perm_free_2 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p;
perm_free_3 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p;

(** Effect of [free] on access validity. *)

valid_access_free_1 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p -> 
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p;
valid_access_free_2 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p);
valid_access_free_inv_1 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p;
valid_access_free_inv_2 m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs;

(** Load-free properties *)

load_free m1 bf lo hi m2:
  free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs;

(** ** Properties of [drop_perm]. *)

nextblock_drop m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m;
drop_perm_valid_block_1 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m b' -> valid_block m' b';
drop_perm_valid_block_2 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m' b' -> valid_block m b';

range_perm_drop_1 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi Cur Freeable;
range_perm_drop_2 m b lo hi p:
  range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' };

perm_drop_1 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p;
perm_drop_2 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p';
perm_drop_3 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p';
perm_drop_4 m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p';

load_drop m b lo hi p m':
  drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs, 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs;

(** * Relating two memory states. *)

(** ** Memory extensions *)

extends_refl m:
  extends m m;

load_extends chunk m1 m2 b ofs v1:
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2;

loadv_extends chunk m1 m2 addr1 addr2 v1:
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2;

loadbytes_extends m1 m2 b ofs len bytes1:
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2;

store_within_extends chunk m1 m2 b ofs v1 m1' v2:
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2';

store_outside_extends chunk m1 m2 b ofs v m2':
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2';

storev_extends chunk m1 m2 addr1 v1 m1' addr2 v2:
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2';

storebytes_within_extends m1 m2 b ofs bytes1 m1' bytes2:
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2';

storebytes_outside_extends m1 m2 b ofs bytes2 m2':
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2';

alloc_extends m1 m2 lo1 hi1 b m1' lo2 hi2:
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2';

free_left_extends m1 m2 b lo hi m1':
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2;

free_right_extends m1 m2 b lo hi m2':
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2';

free_parallel_extends m1 m2 b lo hi m1':
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2';

valid_block_extends m1 m2 b:
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b);
perm_extends m1 m2 b ofs k p:
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p;
valid_access_extends m1 m2 chunk b ofs p:
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p;
valid_pointer_extends m1 m2 b ofs:
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true;
weak_valid_pointer_extends m1 m2 b ofs:
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true;

(** * Memory injections *)

mi_freeblocks f m1 m2:
  inject f m1 m2 ->
  forall b, ~(valid_block m1 b) -> f b = None;

valid_block_inject_1 f m1 m2 b1 b2 delta:
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1;

valid_block_inject_2 f m1 m2 b1 b2 delta:
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2;

perm_inject f m1 m2 b1 b2 delta ofs k p:
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p;

range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p;

valid_access_inject f m1 m2 chunk b1 ofs b2 delta p:
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p;

valid_pointer_inject f m1 m2 b1 ofs b2 delta:
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true;

weak_valid_pointer_inject f m1 m2 b1 ofs b2 delta:
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true;

address_inject f m1 m2 b1 ofs1 b2 delta p:
  inject f m1 m2 ->
  perm m1 b1 (Int.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Int.unsigned (Int.add ofs1 (Int.repr delta)) = Int.unsigned ofs1 + delta;

valid_pointer_inject_no_overflow f m1 m2 b ofs b' delta:
  inject f m1 m2 ->
  valid_pointer m1 b (Int.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned;

weak_valid_pointer_inject_no_overflow f m1 m2 b ofs b' delta:
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Int.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned;

valid_pointer_inject_val f m1 m2 b ofs b' ofs':
  inject f m1 m2 ->
  valid_pointer m1 b (Int.unsigned ofs) = true ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Int.unsigned ofs') = true;

weak_valid_pointer_inject_val f m1 m2 b ofs b' ofs':
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Int.unsigned ofs) = true ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Int.unsigned ofs') = true;

inject_no_overlap f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2:
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2;

different_pointers_inject f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2:
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Int.unsigned ofs1) = true ->
  valid_pointer m b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <>
  Int.unsigned (Int.add ofs2 (Int.repr delta2));

disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2 
             \/ ofs2 + delta2 + sz <= ofs1 + delta1;

aligned_area_inject:
  forall f m m' b ofs al sz b' delta,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta);

load_inject f m1 m2 chunk b1 ofs b2 delta v1:
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2;

loadv_inject f m1 m2 chunk a1 a2 v1:
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_inject f v1 v2;

loadbytes_inject f m1 m2 b1 ofs len b2 delta bytes1:
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2;

store_mapped_inject f chunk m1 b1 ofs v1 n1 m2 b2 delta v2:
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2;

store_unmapped_inject f chunk m1 b1 ofs v1 n1 m2:
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2;

store_outside_inject f m1 m2 chunk b ofs v m2':
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2';

storev_mapped_inject f chunk m1 a1 v1 n1 m2 a2 v2:
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2;

storebytes_mapped_inject f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2:
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2;

storebytes_unmapped_inject f m1 b1 ofs bytes1 n1 m2:
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2;

storebytes_outside_inject f m1 m2 b ofs bytes2 m2':
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2';

alloc_right_inject f m1 m2 lo hi b2 m2':
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2';

alloc_left_unmapped_inject f m1 m2 lo hi m1' b1:
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b);

alloc_left_mapped_inject f m1 m2 lo hi m1' b1 b2 delta:
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Int.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Int.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') -> 
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b);

alloc_parallel_inject f m1 m2 lo1 hi1 m1' b1 lo2 hi2:
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b);

free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2;

free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2;

free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2';

perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\ 
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False);

free_inject f m1 l m1' m2 b lo hi m2':
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2';

drop_outside_inject f m1 m2 b lo hi p m2':
  inject f m1 m2 -> 
  drop_perm m2 b lo hi p = Some m2' -> 
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2';

(** Memory states that inject into themselves. *)

neutral_inject m:
  inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) m m;

empty_inject_neutral thr:
  inject_neutral thr empty;

alloc_inject_neutral thr m lo hi b m':
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  nextblock m < thr ->
  inject_neutral thr m';

store_inject_neutral chunk m b ofs v m' thr:
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  val_inject (flat_inj thr) v v ->
  inject_neutral thr m';

drop_inject_neutral m b lo hi p m' thr:
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  inject_neutral thr m';

(** This ugly workaround is to prevent the [intuition] tactic from
  destructing instances of MEM which are in the context. *)
ugly_workaround_dependee: Type;
ugly_workaround_depender: ugly_workaround_dependee

}.

End Mem.

Generalizable Variables mem.
