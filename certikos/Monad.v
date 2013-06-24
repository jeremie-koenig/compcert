Require Import Functor.


(** * Interface of monads *)

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


(** * Monads are functors *)

Section FUNCTOR.
  Context `{HM: Monad}.

  Global Instance monad_fmap: FunctorOps M := {
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
End FUNCTOR.


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
    split; intros; try destruct m; now reflexivity.
  Qed.
End INSTANCES.
