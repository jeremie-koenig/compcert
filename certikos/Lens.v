
(** * Interface *)

Class Getter (S V: Type) := {
  get: S -> V
}.

Class Setter (S V: Type) := {
  set: V -> S -> S
}.

Class LensSetGet S V `{lens_get: Getter S V} `{lens_set: Setter S V} := {
  lens_set_get s:
    set (get s) s = s
}.

Class LensGetSet S V `{lens_get: Getter S V} `{lens_set: Setter S V} := {
  lens_get_set v s:
    get (set v s) = v
}.

Class LensSetSet S V `{lens_set: Setter S V} := {
  lens_set_set u v s:
    set u (set v s) = set u s
}.

Class Lens S V `{lens_get: Getter S V} `{lens_set: Setter S V} := {
  lens_lens_set_get :> LensSetGet S V;
  lens_lens_get_set :> LensGetSet S V;
  lens_lens_set_set :> LensSetSet S V
}.


(** * Theory *)

(** ** The [modify] operation *)

Section MODIFY.
  Context {S V} `{HSV: Lens S V}.

  Definition modify (f: V -> V) (s: S) :=
    set (f (get s)) s.

  Lemma lens_unfold_modify f s:
    modify f s = set (f (get s)) s.
  Proof.
    reflexivity.
  Qed.
End MODIFY.

(** ** Consequences of [LensGetSet] *)

Section GETSET.
  Context {S V} `{Hgs: LensGetSet S V}.

  Lemma lens_get_modify f s:
    get (modify f s) = f (get s).
  Proof.
    apply lens_get_set.
  Qed.

  Theorem lens_eq_set (s: S) (u v: V):
    set u s = set v s <-> u = v.
  Proof.
    split; intros.
    * rewrite <- (lens_get_set u s).
      rewrite <- (lens_get_set v s).
      apply f_equal.
      assumption.
    * apply (f_equal (fun x => set x s)).
      assumption.
  Qed.
End GETSET.

Hint Rewrite
    @lens_get_set
    @lens_set_get
    @lens_set_set
    @lens_unfold_modify
    @lens_eq_set
  using typeclasses eauto : lens.


(** * Instances *)

(** ** Product *)

Section PROD.
  Global Instance prodr_get A B: Getter (A * B) A := {
    get := @fst _ _
  }.

  Global Instance prodr_set A B: Setter (A * B) A := {
    set a x := (a, snd x)
  }.

  Global Instance prodr_lens A B: Lens (A * B) A.
  Proof.
    split; split; intuition.
  Qed.

  Global Instance prodl_get A B: Getter (A * B) B := {
    get := @snd _ _
  }.

  Global Instance prodl_set A B: Setter (A * B) B := {
    set b x := (fst x, b)
  }.

  Global Instance prodl_lens A B: Lens (A * B) B.
  Proof.
    split; split; intuition.
  Qed.
End PROD.

(** ** Composing lens *)

Section COMPOSE.
  Context (A B C: Type).
  Context `{get_AB: Getter A B} `{set_AB: Setter A B} `{Hlens_AB: !Lens A B}.
  Context `{get_BC: Getter B C} `{set_BC: Setter B C} `{Hlens_BC: !Lens B C}.

  Instance lens_compose_get: Getter A C := {
    get a := get (get a)
  }.

  Instance lens_compose_set: Setter A C := {
    set c a := modify (set c) a
  }.

  Instance lens_compose_get_set: LensGetSet A C.
  Proof.
    constructor; simpl; intros.
    autorewrite with lens.
    reflexivity.
  Qed.

  Instance lens_compose_set_get: LensSetGet A C.
  Proof.
    constructor; simpl; intros.
    autorewrite with lens.
    reflexivity.
  Qed.

  Instance lens_compose_set_set: LensSetSet A C.
  Proof.
    constructor; simpl; intros.
    autorewrite with lens.
    reflexivity.
  Qed.

  Instance lens_compose: Lens A C := {}.
End COMPOSE.
