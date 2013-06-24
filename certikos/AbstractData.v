Require Import Memory.
Require Export Comonad.
Require Import LiftMem.

(** * Types of abstract data *)

(** To equip memory states with abstract data of a given type,
  we need only to provide an initial value for the abstract data
  in question. *)

Class AbstractDataOps (data: Type) := {
  empty_data: data
(* TODO: possibly,
  data_invariant: data -> Prop *)
}.

Class AbstractData (data: Type) `{data_ops: AbstractDataOps data} := {
(* TODO: possibly,
  empty_data_invariant_holds: data_invariant empty_data *)
}.

(** * Using instrumented memory states *)

(** Ultimately, we're shooting for the interface below,
  which we will implement using the product [mem × data]. *)

Class MemWithDataOps (mem: Type -> Type) := {
  mwd_memops (data: Type) `{AbstractDataOps data} :>
    Mem.MemoryOps (mem data);
  get_abstract_data `{data_ops: AbstractDataOps}:
    mem data -> data;
  put_abstract_data {data1 data2}:
    forall `{AbstractDataOps data1} `{AbstractDataOps data2},
    mem data1 -> data2 -> mem data2
}.

Class MemWithData (mem: Type -> Type) `{mem_ops: MemWithDataOps mem} := {
  mwd_mem :>
    forall data `{AbstractData data},
    Mem.MemoryStates (mem data);
  (** XXX: traditionaly for lenses, get_put and put_get are named
    the other way around. *)
  get_put_abstract_data {data1 data2}:
    forall `{AbstractData data1} `{AbstractData data2},
    forall (m: mem data1) (d: data2),
    get_abstract_data (put_abstract_data m d) = d;
  put_get_abstract_data {data}:
    forall `{AbstractData data},
    forall (m: mem data),
    put_abstract_data m (get_abstract_data m) = m
}.


(** * [mem × data] can be used as memory states *)

Notation "( A  ×)" := (prod A).
Infix "×" := prod (at level 40).
Notation "(×  A )" := (fun X => X × A).

Section WITHDATA.
  Context mem `{Hmem: Mem.MemoryStates mem}.
  Context data `{data_ops: AbstractData data}.

  Global Instance data_liftmem_ops: LiftMemoryOps (× data) := {
    lift_empty mem m := (m, empty_data)
  }.

  Global Instance mwd_MEMOPS: Mem.MemoryOps (mem × data) :=
    liftmem_ops (× data) mem.

  Global Instance data_liftmem: LiftMem (× data) := {}.
  Proof.
    reflexivity.
  Qed.

  Global Instance mwd_MEM: Mem.MemoryStates (mem × data) :=
    liftmem_spec (× data) mem.
End WITHDATA.

(** * The functor [(mem ×)] can be used for [MemWithData] *)

Section OPERATIONS.
  Context `{Hmem: Mem.MemoryStates}.

  Global Instance prod_mwdops: MemWithDataOps (mem ×) := {
    mwd_memops data data_ops :=
      mwd_MEMOPS mem data;
    get_abstract_data data data_ops :=
      snd;
    put_abstract_data data1 data2 data1_ops data2_ops :=
      fun m b => set b m
  }.
End OPERATIONS.

(** Theorems *)

Section PROPERTIES.
  Context `{Hmem: Mem.MemoryStates}.
  Context {A} `{Aops: AbstractData A} {B} `{Bops: AbstractData B}.

  Theorem prod_get_put_abstract_data (m: mem × A) (b: B):
    get_abstract_data (put_abstract_data m b) = b.
  Proof.
    reflexivity.
  Qed.

  Theorem prod_put_get_abstract_data (m: mem × A):
    put_abstract_data m (get_abstract_data m) = m.
  Proof.
    destruct m.
    reflexivity.
  Qed.
End PROPERTIES.

Global Instance prod_mwd `{Mem.MemoryStates}: MemWithData (mem ×) := {
  mwd_mem data data_ops Hdata :=
    mwd_MEM mem data;
  get_put_abstract_data data1 data2 data1_ops Hdata1 data2_ops Hdata2 :=
    prod_get_put_abstract_data;
  put_get_abstract_data data data_ops Hdata :=
    prod_put_get_abstract_data
}.

(** * Additional properties about global environments *)

Require Import Globalenvs.

Section GLOBALENVS.
  Context `{Hmem: Mem.MemoryStates} `{data_ops: AbstractData}.

  Lemma lift_option_abstract_data:
    forall (f: mem -> option mem) (m m': mem × data),
    lift f m = Some m' ->
    extract (A := data) m' = extract (A := data) m.
  Proof.
    intros.
    destruct m as [m d], m' as [m' d'].
    unfold lift in *; simpl in *.
    destruct (f m); try discriminate.
    inversion H.
    now trivial.
  Qed.

  Context (F V: Type) (ge: Genv.t F V).

  Lemma lift_store_init_data (m: mem × data) b p id:
    Genv.store_init_data ge m b p id =
    lift (W := (× data)) (fun m => Genv.store_init_data ge m b p id) m.
  Proof.
    destruct id;
      simpl;
    try destruct (Mem.store AST.Mint8unsigned (fst m) b p (Values.Vint i));
      simpl;
    try destruct m;
      simpl;
    try destruct (Genv.find_symbol ge i);
      simpl;
    try reflexivity.
  Qed.
End GLOBALENVS.

Section GLOBALENVS_HET.
  Context `{Hmem: Mem.MemoryStates} F V (ge: Genv.t F V).

  Hint Resolve lift_option_abstract_data: lift.
  Hint Rewrite @lift_store_init_data using typeclasses eauto: lift.

(*
  Lemma store_init_data_get_abstract_data:
    forall {data1} {data1_ops: AbstractData data1},
    forall {data2} {data1_ops: AbstractData data2},
    forall b p id (m m': mem × data1) (d: data2),
    Genv.store_init_data ge m b p id = Some m' ->
    Genv.store_init_data ge (set d m) b p id = Some (set d m').
  Proof.
    intros.
    rewrite lift_store_init_data.
    About lift_option_eq.
    apply lift_option_eq.
About comonad_set_eq.
    rewrite comonad_set_eq.
    simpl in *;
    autorewrite with lift comonad in *.
    apply comonad_set
    eauto using comonad_set_eq with lift.
    exact H.
    lift .


  Qed.

  Lemma store_init_data_put_abstract_data:
    forall (m: mem × data) b p id (m': mem × data),
    Genv.store_init_state ge m b p id = Some 
*)
End GLOBALENVS_HET.
