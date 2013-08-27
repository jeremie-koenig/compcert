(** * Interface of functors *)

(** As in Haskell, by "functor" we mean an endofunctor in the category
  of types. Which is to say, a map [F: Type -> Type], equipped with
  an operation [fmap] which transport functions of type [A -> B] to
  functions of type [F A -> F B]. *)

Class FunctorOps (F: Type -> Type) := {
  fmap: forall {A B: Type}, (A -> B) -> F A -> F B
}.

Class Functor (F: Type -> Type) `{Fmap: FunctorOps F} := {
  functor_id {A} (x: F A):
    fmap (@id A) x = x;
  functor_compose {A B C} (f: B -> C) (g: A -> B) (x: F A):
    fmap (fun y => f (g y)) x = fmap f (fmap g x)
}.

(** * Simple instances *)

Notation "( A  ×)" := (prod A).
Infix "×" := prod (at level 40).
Notation "(×  A )" := (fun X => X × A).

Section INSTANCES.

  (** ** Constant *)

  (** The constant functor [A] maps everything to [@id A]. *)
  Global Instance const_fmap A: FunctorOps (fun X => A) := {
    fmap X Y f a := a
  }.

  Global Instance const_functor A: Functor (fun X => A).
  Proof.
    tauto.
  Qed.

  (** ** Identity *)

  (** The identity functor maps [f] to itself. *)
  Global Instance id_fmap: FunctorOps (fun X => X) := {
    fmap X Y f := f
  }.

  Global Instance id_functor: Functor (fun X => X).
  Proof.
    tauto.
  Qed.

  (** ** Product *)

  Global Instance prodl_fmap A: FunctorOps (A ×) := {
    fmap X Y f ax := match ax with (a, x) => (a, f x) end
  }.

  Global Instance prodr_fmap A: FunctorOps (× A) := {
    fmap X Y f xa := match xa with (x, a) => (f x, a) end
  }.

  Global Instance prodl_functor A: Functor (A ×).
  Proof.
    tauto.
  Qed.

  Global Instance prodr_functor A: Functor (× A).
  Proof.
    tauto.
  Qed.

  (** ** Option *)

  Global Instance option_fmap: FunctorOps option := {
    fmap X Y f oa :=
      match oa with
        | Some a => Some (f a)
        | None => None
      end
  }.

  Global Instance option_functor: Functor option.
  Proof.
    constructor.
    * intros A [a|]; reflexivity.
    * intros A B C f g [a|]; reflexivity.
  Qed.
End INSTANCES.


(** * Some helper instances *)

(** Here are some "instance" versions of some of the [Axioms], for
  use by the setoid rewrite system. They should be somewhere else,
  but since in practice we need them in [Monad] and [Comonad], I'll
  put them here for now. *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Axioms.

Instance funext_subrel {X Y}:
  subrelation (pointwise_relation X eq) (@eq (X -> Y)).
Proof.
  compute.
  apply functional_extensionality.
Qed.

Instance funext_mor2 {X Y A B} (f: (X -> Y) -> A -> B):
  Proper (pointwise_relation X eq ==> eq ==> eq) f.
Proof.
  intros.
  intros x1 x2 Hx y1 y2 Hy.
  apply funext_subrel in Hx.
  apply f_equal2;
  now assumption.
Qed.

Instance funext_mor4 {X Y A B C D} (f: (X -> Y) -> A -> B -> C -> D):
  Proper (pointwise_relation X eq ==> eq ==> eq ==> eq ==> eq) f.
Proof.
  intros.
  intros x1 x2 Hx y1 y2 Hy z1 z2 Hz t1 t2 Ht.
  apply funext_subrel in Hx.
  apply f_equal4;
  now assumption.
Qed.
