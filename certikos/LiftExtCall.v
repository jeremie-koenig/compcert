Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Coqlib.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lens.
Require Import LiftMem.
Require Import PowersetMonad.

Section LIFTEXTCALL.
  Context `{Hlm: LiftModel}.
  Context `{ef_ops: ExtFunOps}.
  Context `{ec_ops: !ExtCallOps bmem external_function}.
  Context `{Hec: !ExternalCalls bmem external_function}.

  Global Instance liftmem_ec_ops: ExtCallOps mem external_function := {
    external_call ef F V ge args m tr ret m' :=
      lift (fun m => external_call ef ge args m tr ret) m m'
  }.

  (** Specialize the theorems about lifting relations to [external_call] *)

  Lemma lift_ec_unlift ef {F V} (ge: Genv.t F V) vargs m1 t vres m2:
    external_call ef ge vargs m1 t vres m2 ->
    external_call ef ge vargs (get π m1) t vres (get π m2).
  Proof.
    apply (lift_relation_unlift
            (fun m1 m2 => external_call ef ge vargs m1 t vres m2)).
  Qed.

  Lemma lift_mem_unchanged_on P m1 m2:
    mem_unchanged_on P (get π m1) (get π m2) ->
    mem_unchanged_on P m1 m2.
  Proof.
    tauto.
  Qed.

  Lemma lift_loc_out_of_reach f m1:
    loc_out_of_reach f m1 = loc_out_of_reach f (get π m1).
  Proof.
    reflexivity.
  Qed.

  Lemma lift_loc_out_of_bounds m:
    loc_out_of_bounds m = loc_out_of_bounds (get π m).
  Proof.
    reflexivity.
  Qed.

  Hint Resolve
    @lift_ec_unlift
    @lift_mem_unchanged_on
    : lift.

  Hint Rewrite
      @lift_loc_out_of_reach
      @lift_loc_out_of_bounds
    using typeclasses eauto : lift.

  Global Instance liftmem_ec_spec: ExternalCalls mem external_function := {}.
  Proof.
    intro ef; split.
    lift (ec_well_typed (external_call_spec ef)).
    lift (ec_arity (external_call_spec ef)).
    lift (ec_symbols_preserved (external_call_spec ef)).
    lift (ec_valid_block (external_call_spec ef)).
    lift (ec_max_perm (external_call_spec ef)).
    lift (ec_readonly (external_call_spec ef)).
    lift (ec_mem_extends (external_call_spec ef)).
    lift_partial (ec_mem_inject (external_call_spec ef)).
      unfold Mem.inject; simpl.
      autorewrite with lens.
      split.
      assumption.
      destruct x1 as [x11 x12].
      assert (H: same_context π m1 m2) by decide_same_context.
      rewrite <- H.
      assumption.
    lift (ec_trace_length (external_call_spec ef)).
    lift (ec_receptive (external_call_spec ef)).
    lift_partial (ec_determ (external_call_spec ef)).
      simpl in *; unfold lift in *; simpl in *.
      inversion x.
      inversion x0.
      subst.
      autorewrite with lens in *.
      assumption.
  Qed.
End LIFTEXTCALL.
