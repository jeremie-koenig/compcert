Require Import Functor.


(** * Interface of monads *)

(** As in Haskell, we define monads in terms of [ret] and [bind].
  However we want to be able to use the corresponding [Functor]
  instances both independently and in the context of monads.
  To permit this, instead of defining a generic [Functor] instance
  for all monads, we require a priori that monads be functors,
  then define the relationship between [fmap], [ret] and [bind]
  as the [monad_fmap] equation in the [Monad] class. This way,
  code need not depend on this module when they use, say, [option]
  as a simple [Functor] rather than a full-blown [Monad].
  In addition, [id] for instance is both a [Monad] and [Comonad],
  but we do not want to derive two separate instances of the
  corresponding [Functor]. *)

Class MonadOps (M: Type -> Type) `{Mfmap: FunctorOps M} := {
  ret {A}: A -> M A;
  bind {A B}: (A -> M B) -> M A -> M B
}.

Notation "'do' x <- M ; N" := (bind (fun x => N) M)
  (at level 200, x ident, M at level 100, N at level 200).

Class Monad (M: Type -> Type) `{Mops: MonadOps M}: Prop := {
  monad_functor :> Functor M;
  monad_fmap {A B} (f: A -> B):
    fmap f = bind (fun x => ret (f x));
  monad_ret_bind {A B} (f: A -> M B) (x: A):
    bind f (ret x) = f x;
  monad_bind_ret {A} (m: M A):
    bind ret m = m;
  monad_bind_bind {A B C} (f: B -> M C) (g: A -> M B) (m: M A):
    bind f (bind g m) = bind (fun x => bind f (g x)) m
}.

(** Using the theorem in [Monad], we can try to normalize monadic
  expressions to the form [x1 <- M1; x2 <- M2; ...; xn <- Mn]. *)
Hint Rewrite
    @monad_ret_bind
    @monad_bind_ret
    @monad_bind_bind
  using typeclasses eauto : monad.

(** Unfortunately, the [MonadOps] instance in [monad_fmap] cannot
  be obtained by unification when matching the left-hand side of
  the rewrite with the current goal. Since the [autorewrite] tactic
  does not do type class resolution, we cannot use [monad_fmap]
  as a rewrite rule. *)
Ltac monadNorm :=
  rewrite !monad_fmap; autorewrite with monad.


(** * Some instances *)

Section INSTANCES.
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
    split; intros; try destruct m; try reflexivity.
    typeclasses eauto.
  Qed.
End INSTANCES.
