Require Export Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Axioms.

Instance funext_subrel {X Y}:
  subrelation
    (Morphisms.pointwise_relation X eq)
    (@eq (X -> Y)).
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


(** * Interface definitions *)

(** As in Haskell, we defined monads in terms of [ret] and [bind], and
  provide derived definitions for [fmap] and [join]. *)

Class MonadOps (M: Type -> Type) := {
  ret {A}: A -> M A;
  bind {A B}: (A -> M B) -> M A -> M B
}.

Class Monad (M: Type -> Type) `{Mops: MonadOps M}: Prop := {
  monad_ret_bind {A B} (f: A -> M B) (x: A):
    bind f (ret x) = f x;
  monad_bind_ret {A} (m: M A):
    bind ret m = m;
  monad_bind_bind {A B C} (f: B -> M C) (g: A -> M B) (m: M A):
    bind f (bind g m) = bind (fun x => bind f (g x)) m
}.

Hint Rewrite
    @monad_ret_bind
    @monad_bind_ret
    @monad_bind_bind
  using typeclasses eauto : monad.

Notation "'do' x <- M ; N" := (bind (fun x => N) M)
  (at level 200, x ident, M at level 100, N at level 200).

(** Likewise, comonads are defined in terms of [extract] and [extend]. *)

Class ComonadOps (W: Type -> Type) := {
  extract {A}: W A -> A;
  extend {A B}: (W A -> B) -> W A -> W B
}.

Class Comonad (W: Type -> Type) `{Wops: ComonadOps W}: Prop := {
  comonad_extract_extend {A B} (f: W A -> B) (w: W A):
    extract (extend f w) = f w;
  comonad_extend_extract {A} (w: W A):
    extend extract w = w;
  comonad_extend_extend {A B C} (f : W B -> C) (g: W A -> B) (w: W A):
    extend f (extend g w) = extend (fun w => f (extend g w)) w
}.

Hint Rewrite
    @comonad_extract_extend
    @comonad_extend_extract
    @comonad_extend_extend
  using typeclasses eauto : comonad.

(** Both monads and comonads are special cases of functors in Type. *)

Class FunctorOp (F: Type -> Type) := {
  fmap: forall {A B: Type}, (A -> B) -> F A -> F B
}.

Class Functor (F: Type -> Type) `{Fmap: FunctorOp F} := {
  functor_id {A} (x: F A):
    fmap (@id A) x = x;
  functor_compose {A B C} (f: B -> C) (g: A -> B) (x: F A):
    fmap (fun y => f (g y)) x = fmap f (fmap g x)
}.

(** * Functors *)

Section FUNCTORS.
  (** The constant functor [A] maps everything to [@id A]. *)
  Global Instance const_fmap A: FunctorOp (fun X => A) := {
    fmap X Y f a := a
  }.

  Global Instance const_functor A: Functor (fun X => A).
  Proof.
    tauto.
  Qed.

  (** The identity functor maps [f] to itself. *)
  Global Instance id_fmap: FunctorOp (fun X => X) := {
    fmap X Y f := f
  }.

  Global Instance id_functor: Functor (fun X => X).
  Proof.
    tauto.
  Qed.
End FUNCTORS.

(** * Monads *)

Section MONADS.
  Context `{HM: Monad}.

  (** A monad is a functor. *)

  Global Instance monad_fmap: FunctorOp M := {
    fmap A B f :=
      bind (fun x => ret (f x))
  }.

  Global Instance monad_functor: Functor M.
  Proof.
    split; intros; simpl; autorewrite with monad.
    - reflexivity.
    - setoid_rewrite monad_ret_bind.
      reflexivity.
  Qed.

  Theorem monad_return_fmap {A B} (f: A -> B) (x: A):
    fmap f (ret x) = ret (f x).
  Proof.
    simpl.
    autorewrite with monad.
    reflexivity.
  Qed.
End MONADS.

(** * Comonads *)

Section COMONADS.
  Context `{HW: Comonad}.

  Global Instance comonad_fmap: FunctorOp W := {
    fmap A B f :=
      extend (fun w => f (extract w))
  }.

  Global Instance comonad_functor: Functor W.
  Proof.
    split; intros; simpl; autorewrite with comonad.
    - reflexivity.
    - setoid_rewrite comonad_extract_extend.
      reflexivity.
  Qed.

  Theorem comonad_extend_eq {A B} (f g: W A -> B) (w: W A):
    extend f w = extend g w -> f w = g w.
  Proof.
    intros.
    apply (f_equal extract) in H.
    rewrite !comonad_extract_extend in H.
    assumption.
  Qed.

  Definition set {A B} (x: B): W A -> W B :=
    extend (const x).

  Theorem comonad_set_eq {A B} (x y: B) (w: W A):
    set x w = set y w <-> x = y.
  Proof.
    split.
    - apply comonad_extend_eq.
    - intro; apply f_equal2; trivial.
  Qed.

  Theorem comonad_extract_set {A B} (x: A) (w: W B):
    extract (set x w) = x.
  Proof.
    unfold set.
    apply comonad_extract_extend.
  Qed.

  Theorem comonad_set_set {A B C} (x: A) (y: B) (w: W C):
    set x (set y w) = set x w.
  Proof.
    unfold set, const.
    rewrite comonad_extend_extend.
    reflexivity.
  Qed.

  (* This would be useful but proving might require more premises?
  Theorem comonad_set_extract {A} (w: W A):
    set (extract w) w = w.
  Proof.
  Qed.
  *)
End COMONADS.

Hint Rewrite
    @comonad_set_eq
    @comonad_extract_set
    @comonad_set_set
  using typeclasses eauto: comonad.

(** * Well-known instances *)

Section INSTANCES.
  Open Scope type_scope.

  (** ** [option] is a monad *)

  Global Instance option_monad_ops: MonadOps option := {
    bind A B f mx :=
      match mx with
        | Some a => f a
        | None => None
      end;
    ret := Some
  }.

  Global Instance option_monad: Monad option.
  Proof.
    split; intros; try destruct m; now reflexivity.
  Qed.

  (** ** [A * -] is a comonad. *)

  Global Instance prod_comonad_ops {A}: ComonadOps (prod A) := {
    extract := @snd A;
    extend X Y f x := (fst x, f x)
  }.

  Global Instance prod_comonad {A}: Comonad (prod A).
  Proof.
    split; simpl; try destruct w; now reflexivity.
  Qed.

  (** ** [- * A] is a comonad *)

  Global Instance prod_l_comonad_ops {A}: ComonadOps (fun X => X * A) := {
    extract X := @fst X A;
    extend X Y f x := (f x, snd x)
  }.

  Global Instance prod_l_comonad {A}: Comonad (fun X => X * A).
  Proof.
    split; intros; try destruct w; now reflexivity.
  Qed.
End INSTANCES.
