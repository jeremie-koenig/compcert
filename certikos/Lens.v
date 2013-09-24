Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Classes.RelationPairs.
Require Import Coq.Setoids.Setoid.

(** * Interface *)

(** Lenses are identified by the corresponding projection, which is
  also used to define the [get] operation. Note that because we use
  the letter [S] to denote the source type, which conflicts with the
  successor function on [nat] from the standard library, we need to
  use a verbose style below to avoid arguments being named [S0] or
  something such. (This is an obvious software engineering quirk
  with the way Coq generates identifier.) *)

Class Getter {S V: Type} (π: S -> V) := {
  get: S -> V := π
}.

Class Setter {S V: Type} (π: S -> V) := {
  set: V -> S -> S
}.

Arguments get {S V} π {_} _.
Arguments set {S V} π {_} _ _.

Class LensSetGet {S V} π
  `{lens_get: Getter S V π}
  `{lens_set: Setter S V π} :=
{
  lens_set_get s:
    set π (get π s) s = s
}.

Class LensGetSet {S V} π
  `{lens_get: Getter S V π}
  `{lens_set: Setter S V π} :=
{
  lens_get_set v s:
    get π (set π v s) = v
}.

Class LensSetSet {S V} π
  `{lens_set: Setter S V π} :=
{
  lens_set_set u v s:
    set π u (set π v s) = set π u s
}.

Class Lens {S V} π `{lens_get: Getter S V π} `{lens_set: Setter S V π} := {
  lens_lens_set_get :> LensSetGet π;
  lens_lens_get_set :> LensGetSet π;
  lens_lens_set_set :> LensSetSet π
}.


(** * Theory *)

(** ** Getters are measures, cf. [Coq.Classes.RelationPairs] *)

Instance lens_get_measure {S V} `{Getter S V}:
  Measure (get π).

(** ** The [modify] operation *)

Section MODIFY.
  Context {S V π} `{HSV: Lens S V π}.

  Definition modify (f: V -> V) (s: S) :=
    set π (f (get π s)) s.

  Lemma lens_unfold_modify f s:
    modify f s = set π (f (get π s)) s.
  Proof.
    reflexivity.
  Qed.
End MODIFY.

Arguments modify {S V} π {_ _} _ _.

(** ** The [same_context] relation *)

Section SAMECONTEXT.
  Context {S V π} `{lens_get: Getter S V π} `{HSV: LensSetSet S V π}.

  Definition same_context: relation S :=
    fun s t => forall v, set π v s = set π v t.

  Lemma lens_set_same_context v s:
    same_context (set π v s) s.
  Proof.
    intro u.
    apply lens_set_set.
  Qed.

  Lemma lens_modify_same_context f s:
    same_context (modify π f s) s.
  Proof.
    intro u.
    unfold modify.
    apply lens_set_set.
  Qed.

  Global Instance same_context_equiv: Equivalence same_context.
  Proof.
    split.
    * intros s v.
      reflexivity.
    * intros s t Hst u.
      symmetry; now auto.
    * intros s1 s2 s3 H12 H23 u.
      transitivity (set π u s2); now auto.
  Qed.

  Global Instance same_context_set_mor:
    Proper (eq ==> same_context ==> eq) (set π).
  Proof.
    intros u v Huv s t Hst.
    subst.
    apply Hst.
  Qed.

  Global Instance same_context_modify_mor f:
    Proper (same_context ==> same_context) (modify π f).
  Proof.
    intros s t Hst u.
    unfold modify.
    rewrite !lens_set_set.
    apply Hst.
  Qed.
End SAMECONTEXT.

Arguments same_context {S V} π {_} _ _.

(** ** Consequences of [LensGetSet] *)

Section GETSET.
  Context {S V} `{Hgs: LensGetSet S V}.

  Lemma lens_get_modify f s:
    get π (modify π f s) = f (get π s).
  Proof.
    apply lens_get_set.
  Qed.

  Theorem lens_eq_set (s: S) (u v: V):
    set π u s = set π v s <-> u = v.
  Proof.
    split; intros.
    * rewrite <- (lens_get_set u s).
      rewrite <- (lens_get_set v s).
      apply f_equal.
      assumption.
    * apply (f_equal (fun x => set π x s)).
      assumption.
  Qed.
End GETSET.

Hint Rewrite
    @lens_get_set
    @lens_set_get
    @lens_set_set
    @lens_unfold_modify
    @lens_eq_set
    @lens_set_same_context
    @lens_modify_same_context
  using typeclasses eauto : lens.


(** * Instances *)

(** ** Product *)

Section PROD.
  Global Instance fst_get A B: Getter (@fst A B) := {}.

  Global Instance fst_set A B: Setter (@fst A B) := {
    set a x := (a, snd x)
  }.

  Global Instance fst_lens A B: Lens (@fst A B).
  Proof.
    split; split; intuition.
  Qed.

  Global Instance snd_get A B: Getter (@snd A B) := {}.

  Global Instance snd_set A B: Setter (@snd A B) := {
    set b x := (fst x, b)
  }.

  Global Instance snd_lens A B: Lens (@snd A B).
  Proof.
    split; split; intuition.
  Qed.
End PROD.

(** ** Composing lens *)

Section COMPOSE.
  Context {A B C} (π: A -> B) (ρ: B -> C) `{Hπ: Lens _ _ π} `{Hρ: Lens _ _ ρ}.
  Import Program.Basics.

  Instance compose_get: Getter (compose ρ π) := {}.

  Instance compose_set: Setter (compose ρ π) := {
    set c a := modify π (set ρ c) a
  }.

  (** XXX: should we add this to the rewrite base? *)
  Lemma compose_get_get_get a:
    get (compose ρ π) a = get ρ (get π a).
  Proof.
    reflexivity.
  Qed.

  Instance compose_get_set: LensGetSet (compose ρ π).
  Proof.
    constructor; simpl; intros.
    rewrite compose_get_get_get.
    autorewrite with lens.
    reflexivity.
  Qed.

  Instance lens_compose_set_get: LensSetGet (compose ρ π).
  Proof.
    constructor; simpl; intros.
    rewrite compose_get_get_get.
    autorewrite with lens.
    reflexivity.
  Qed.

  Instance lens_compose_set_set: LensSetSet (compose ρ π).
  Proof.
    constructor; simpl; intros.
    autorewrite with lens.
    reflexivity.
  Qed.

  Instance lens_compose: Lens (compose ρ π) := {}.
End COMPOSE.
