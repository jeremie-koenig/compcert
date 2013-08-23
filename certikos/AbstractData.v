Require Import AST.
Require Import Memory.
Require Import Globalenvs.
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


(** * [mem × data] can be used as memory states *)

Notation "( A  ×)" := (prod A).
Infix "×" := prod (at level 40).
Notation "(×  A )" := (fun X => X × A).

Section WITHDATA.
  Context mem `{Hmem: Mem.MemoryStates mem}.
  Context data `{data_ops: AbstractData data}.

  Global Instance data_liftmem_ops: LiftMemoryOps (mem × data) mem := {
    liftmem_empty := (Mem.empty, empty_data)
  }.

  Global Instance data_liftmem: LiftMem (mem × data) mem := {}.
  Proof.
    reflexivity.
  Qed.
End WITHDATA.
