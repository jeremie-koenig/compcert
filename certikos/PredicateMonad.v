Require Import Axioms.
Require Import Functor.
Require Import Monad.

(** * Predicates (ie. "sets") are a monad *)

(** The operation [ret a] constructs the singleton {[a]} and is simply
  the predicate [eq a]. On the other hand, [bind R pA] constructs the
  image of the set [pA] by the relation [R: A -> B -> Prop]. *)

Inductive pred_bind {A B} (R: A -> B -> Prop) (pA: A -> Prop) (b: B): Prop :=
  | pred_bind_intro a: pA a -> R a b -> pred_bind R pA b.

Arguments pred_bind_intro {A B R pA b} a _ _.

Instance pred_monad_ops: MonadOps (fun X => X -> Prop) := {
  ret A := eq;
  bind A B := pred_bind
}.

Instance pred_monad: Monad (fun X => X -> Prop).
Proof.
  split; simpl; intros.
  * apply functional_extensionality; intro y.
    apply prop_ext; split; intro H.
    - inversion H; congruence.
    - apply (pred_bind_intro x); now auto.
  * apply functional_extensionality; intro x.
    apply prop_ext; split; intro H.
    - inversion H; congruence.
    - apply (pred_bind_intro x); now auto.
  * apply functional_extensionality; intro z.
    apply prop_ext; split; intro H.
    - destruct H as [y [x Hx Hxy] Hyz].
      apply (pred_bind_intro x).
      + assumption.
      + apply (pred_bind_intro y); now auto.
    - destruct H as [x Hx [y Hxy Hyz]].
      apply (pred_bind_intro y).
      + apply (pred_bind_intro x); now auto.
      + assumption.
Qed.

(** The resulting [fmap] computes the image of a set by a function. *)

Inductive pred_lift {A B} (f: A -> B) (pA: A -> Prop): B -> Prop :=
  pred_lift_intro a: pA a -> pred_lift f pA (f a).

Arguments pred_lift_intro {A B f pA} a _.

Remark pred_fmap_lift {A B} (f: A -> B) (pA: A -> Prop):
  fmap f pA = pred_lift f pA.
Proof.
  simpl.
  apply functional_extensionality; intro y.
  apply prop_ext; split; intro H.
  * destruct H as [x Hx Hxy]; subst.
    apply (pred_lift_intro x).
    assumption.
  * destruct H as [x Hx].
    apply (pred_bind_intro x).
    - assumption.
    - reflexivity.
Qed.
