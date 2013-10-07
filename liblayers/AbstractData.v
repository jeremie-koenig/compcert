Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Program.Basics.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Export Functor.
Require Export Lens.
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

Class AbstractDataInjectOps (sdata tdata: Type)
  `{sdata_ops: AbstractDataOps sdata}
  `{tdata_ops: AbstractDataOps tdata} :=
{
  data_inject: sdata -> tdata -> Prop
}.

Class AbstractDataInjections (sdata tdata: Type)
  `{data_inj_ops: AbstractDataInjectOps sdata tdata} :=
{
}.

Class AbstractDataModelOps data
  `{data_ops: AbstractDataOps data}
  `{data_inj_ops: !AbstractDataInjectOps data data} :=
{
}.

Class AbstractDataModel data `{data_mm_ops: AbstractDataModelOps data} :=
{
  data_inject_reflexive :> Reflexive data_inject
}.


(** * Default instances for homogenous injections *)

(* Homogenous injections are used when compiling. In this case,
  we want the abstract data for the source and target to be identical.
  Therefore we should simply use [eq] for [data_inject]. *)

Section DEFAULTHINJ.
  Context `{Hdata: AbstractData}.

  Global Instance data_eq_inj_ops: AbstractDataInjectOps data data | 10 :=
  {
    data_inject := eq
  }.

  Global Instance data_eq_inj_spec:
    AbstractDataInjections data data | 10 := {}.

  Global Instance data_eq_mm_ops:
    AbstractDataModelOps data | 10 := {}.

  Global Instance data_eq_mm_spec:
    AbstractDataModel data | 10 := {}.
End DEFAULTHINJ.

(** * [mem × data] can be used as memory states *)

Section LIFTMEM.
  Context mem `{Hmem: Mem.MemoryModel mem}.
  Context data `{data_ops: AbstractData data}.

  Global Instance data_liftmem_ops: LiftMemoryOps (@fst mem data) := {
    liftmem_empty := (Mem.empty, empty_data)
  }.

  Global Instance data_liftmem_spec: LiftMemoryStates (@fst mem data) := {}.
  Proof.
    reflexivity.
  Qed.
End LIFTMEM.

Section LIFTINJ.
  Context `{Hmem_inj: Mem.MemoryInjections}.
  Context `{Hdata_inj: AbstractDataInjections}.

  Global Instance data_liftinj_ops:
    LiftInjectOps (@fst smem sdata) (@fst tmem tdata) :=
  {
    liftmem_context_inject s t := data_inject (get snd s) (get snd t)
  }.

  Global Instance data_liftinj_spec:
    LiftInjections (@fst smem sdata) (@fst tmem tdata) := {}.
  Proof.
    intros [sm1 sd1] [sm2 sd2] Hs [tm1 td1] [tm2 td2] Ht H.
    unfold same_context in *.
    simpl in *.
    specialize (Hs sm1); inversion Hs.
    specialize (Ht tm1); inversion Ht.
    unfold get in *; simpl in *.
    congruence.
  Qed.
End LIFTINJ.

Section LIFTHINJ.
  Context `{Hmm: Mem.MemoryModel}.
  Context `{Hdata_mm: AbstractDataModel}.

  Global Instance data_liftmm_ops:
    LiftModelOps (@fst mem data) := {}.

  Global Instance data_liftmm_spec:
    LiftModel (@fst mem data) := {}.
End LIFTHINJ.

(** This should be enough to ensure that instances of [Mem.MemoryModel]
  can be combined with instances of [AbstractDataHomogenousInjections]
  to derive [Mem.MemoryModel] instances on the product (mem × data).
  Below we just make sure that it is indeed the case. *)

Section TEST.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hdata: AbstractDataModel}.

  Instance: Mem.MemoryModel (mem × data) := _.
End TEST.
