Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Classes.Morphisms.

Require Import Lens.
Require Import Functor.
Require Import PowersetMonad.


(** * Lifting operations *)

(** Because [Mem.MemoryModel] contains so many theorems, we need some
  systematic way to lift the memory operations along a lens, so that
  the lifting of the theorems is convenient to automate.

  The signature of most of the memory operations are variations on
  the theme [mem -> F mem], where [F] is a functor such as [option]
  or [- × Z]. Using the functor's [fmap] and the lens operations,
  we can define a generic lifting operator as in the following. *)

Class Lift A B := { lift: A -> B }.

Section LIFT.
  Context {S V} `{HSV: Lens S V} `{HF: Functor}.

  Global Instance lens_lift: Lift (V -> F V) (S -> F S) := {
    lift f s := fmap (fun v => set π v s) (f (get π s))
  }.
End LIFT.

(** Typeclass resolution needs some help to unify the following. *)

Section LIFTINSTANCES.
  Context {S V} `{HSV: Lens S V}.

  Global Instance lift_const A: Lift (V -> A) (S -> A) :=
    lens_lift (F := (fun _ => A)).
  Global Instance lift_prod A: Lift (V -> V * A) (S -> S * A) :=
    lens_lift.
  Global Instance lift_powerset: Lift (V -> V -> Prop) (S -> S -> Prop) :=
    lens_lift (F := (fun X => X -> Prop)).
End LIFTINSTANCES.


(** ** Lifting theorems *)

(** This is the main tactic we use: it lifts a theorem [Hf] of
  the underlying memory model by "peeling off" its structure
  recursively to prove the lifted goal. The leaf goals are
  handled with the caller-provided tactic [leaftac]. *)

(* Premises are "translated" and used to specialize Hf *)
Ltac lift_peel_intro recurse Hf x :=
  intro x;
  (specialize (Hf x) ||
   specialize (Hf (get _ x)) ||
   (match type of Hf with
      forall (H: ?T), _ =>
        let H' := fresh H in
        assert (H': T) by recurse x;
        specialize (Hf H');
        clear H'
    end));
  recurse Hf.

(* Existential: we must use [set] to augment any memory state
  provided by Hf, but we can otherwise just pass everything along *)
Ltac lift_peel_exists recurse Hf x :=
  let Hf' := fresh Hf in
  destruct Hf as [x Hf'];
  (exists x || eexists (set _ x _));
  recurse Hf'.

(* Conjunction: split and peel each side independently *)
Ltac lift_peel_conj recurse Hf :=
  let Hl := fresh Hf "l" in
  let Hr := fresh Hf "r" in
  destruct Hf as [Hl Hr];
  split; [recurse Hl | recurse Hr].

Ltac lift_peel Hf leaftac :=
  let recurse Hf := lift_peel Hf leaftac in
  try match goal with
    | |- forall (x: _), _ =>
      let x := fresh x in
      lift_peel_intro recurse Hf x
    | |- exists (x: _), _ =>
      let x := fresh x in
        lift_peel_exists recurse Hf x
    | |- { x: _ | _ } =>
      let x := fresh x in
        lift_peel_exists recurse Hf x
    | |- _ /\ _ =>
      lift_peel_conj recurse Hf
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
  lift_peel Hf lift_leaf.

Ltac lift f :=
  now lift_partial f.


(** *** Properties of [lift (F:=option)] *)

Section LIFTOPTION.
  Context {S V} `{Hgs: LensGetSet S V}.

  Lemma lift_option_eq (f: V -> option V):
    forall (s s': S),
      lift f s = Some s' ->
      f (get π s) = Some (get π s').
  Proof.
    unfold lift; simpl; intros.
    destruct (f (get π s)); try discriminate.
    inversion H.
    autorewrite with lens.
    reflexivity.
  Qed.

  Lemma lift_option_eq_set_iff (f: V -> option V) (s: S) (v': V):
    lift f s = Some (set π v' s) <->
    f (get π s) = Some v'.
  Proof.
    simpl; intros.
    split; destruct (f (get π s)); try discriminate;
    intro H; inversion H.
    - apply f_equal.
      apply lens_eq_set in H1.
      assumption.
    - reflexivity.
  Qed.

  (* XXX *)
  Lemma lift_option_eq_set (f: V -> option V) (s: S) (v': V):
    f (get π s) = Some v' ->
    lift f s = Some (set π v' s).
  Proof.
    apply lift_option_eq_set_iff.
  Qed.

  Theorem lift_option_eq_same_context `{Hlss: !LensSetSet π}:
    forall (f: V -> option V) (s s': S),
      lift f s = Some s' ->
      same_context π s s'.
  Proof.
    intros f s s'.
    unfold lift; simpl.
    case (f (get π s)).
    * intros ? H; inversion H; subst.
      symmetry.
      apply lens_set_same_context.
    * discriminate.
  Qed.

  Theorem lift_option_same_context_eq `{Hlsg: !LensSetGet π}:
    forall (f: V -> option V) (s s': S),
      f (get π s) = Some (get π s') ->
      same_context π s s' ->
      lift f s = Some s'.
  Proof.
    intros f s s' Hc Hv.
    simpl.
    rewrite Hc; clear Hc.
    f_equal.
    rewrite Hv.
    apply lens_set_get.
  Qed.

  (* XXX *)
  Theorem lift_mor `{FunctorOps} (f g: V -> F V) (s: S):
    f (get π s) = g (get π s) ->
    lift f s = lift g s.
  Proof.
    intros Hfg.
    simpl.
    apply f_equal.
    assumption.
  Qed.

  (* XXX *)
  Theorem lift_option_eq_preserves_context (f g: V -> option V) (s s': S):
    g (get π s) = Some (get π s') ->
    lift f s = Some s' ->
    lift g s = Some s'.
  Proof.
    intros Hg Hlf.
    rewrite <- Hlf.
    apply lift_mor.
    rewrite Hg.
    symmetry.
    apply lift_option_eq.
    assumption.
  Qed.
End LIFTOPTION.

(** *** Properties of [lift (F := fun X => A * X)] *)

Section LIFTPROD.
  Context {S V} `{Hgs: LensGetSet S V} {A: Type}.

  Theorem lift_prod_eq (f: V -> V * A) (s s': S) (a: A):
    lift f s = (s', a) ->
    f (get π s) = (get π s', a).
  Proof.
    simpl.
    destruct (f (get π s)) as [v' a'].
    intros H.
    inversion H.
    autorewrite with lens.
    reflexivity.
  Qed.

  (* XXX *)
  Theorem lift_prod_eq_set (f: V -> V * A) s v' a:
    f (get π s) = (v', a) ->
    lift f s = (set π v' s, a).
  Proof.
    intro H; simpl.
    rewrite H; clear H; simpl.
    reflexivity.
  Qed.

  Context `{Hlss: !LensSetSet π}.

  Theorem lift_prod_eq_same_context (f: V -> V * A) (s s': S) (a: A):
    lift f s = (s', a) ->
    same_context π s s'.
  Proof.
    simpl.
    destruct (f (get π s)).
    intro H; inversion H; subst.
    symmetry.
    apply lens_set_same_context.
  Qed.
End LIFTPROD.

(** *** Properties of [lift (F := fun X => X -> Prop)] *)

Section LIFTREL.
  Context {S V} `{Lens S V}.

  (** Relations lifted with the powerset monad only relate memory
    states with the same abstract data. *)
  Global Instance lift_relation_same_context (R: relation V):
    subrelation (lift R) (same_context π).
  Proof.
    unfold lift; simpl.
    intros s1 s2 Hs.
    inversion Hs.
    autorewrite with lens.
    reflexivity.
  Qed.

  (** They also only relate memory states whose underlying components
    are related. *)
  Global Instance lift_relation_unlift (R: relation V):
    subrelation (lift R) (R @@ get π)%signature.
  Proof.
    unfold lift, RelCompFun; simpl.
    intros s1 s2 Hs.
    inversion Hs.
    autorewrite with lens.
    assumption.
  Qed.

  (** In fact, lift R is the conjunction of these two relations. *)
  Lemma lift_relation_intro (R: V -> V -> Prop) (s1 s2: S):
    same_context π s1 s2 ->
    R (get π s1) (get π s2) ->
    lift (Lift := lift_powerset) R s1 s2.
  Proof.
    intros Hc Hv.
    unfold lift; simpl.
    replace s2 with (set π (get π s2) s1).
    * change (set π (get π s2) s1) with ((fun v => set π v s1) (get π s2)).
      eapply powerset_fmap_intro.
      assumption.
    * rewrite Hc.
      autorewrite with lens.
      reflexivity.
  Qed.
End LIFTREL.

(** Decision procedure for [same_context]: use the theorems above to
  extract the [same_context] consequences of every hypothesis, use
  [autorewrite with lens] to eliminate all occurences of [set] then
  use [congruence]. *)

Ltac decide_same_context :=
  repeat match goal with
    | [ H: lift ?f _ = Some _ |- _ ] => apply lift_option_eq_same_context in H
    | [ H: lift ?f _ = (_, _) |- _ ] => apply lift_prod_eq_same_context in H
    | [ H: lift ?R _ _        |- _ ] => apply lift_relation_same_context in H
  end;
  autorewrite with lens in *;
  congruence.

Hint Extern 10 (same_context _ _ _) => decide_same_context : lift.

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
  @lift_relation_intro
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

Hint Extern 10 => progress lift_reduce; now eauto: lift. 
