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

  Instance lift_powerset : Lift (bmem -> bmem -> Prop) (mem -> mem -> Prop) :=
    lens_lift (F := (fun X => X -> Prop)).

  Global Instance liftmem_ec_ops: ExtCallOps mem external_function := {
    external_call ef F V ge args m tr ret m' :=
      lift (fun m => external_call ef ge args m tr ret) m m'
  }.

  (** Relations lifted with the powerset monad only relate memory
    states with the same abstract data. *)
  Lemma lift_relation_same_context (R: relation bmem):
    subrelation (lift R) (same_context π).
  Proof.
    unfold lift; simpl.
    intros m1 m2 Hm.
    inversion Hm.
    autorewrite with lens.
    reflexivity.
  Qed.

  (** They also only relate memory states whose underlying components
    are related. *)
  Lemma lift_relation_unlift (R: relation bmem):
    subrelation (lift R) (R @@ get π)%signature.
  Proof.
    unfold lift, RelCompFun; simpl.
    intros m1 m2 Hm.
    inversion Hm.
    autorewrite with lens.
    assumption.
  Qed.

  (** In fact, lift R is the conjunction of these two relations. *)
  Lemma lift_relation_intro (R: bmem -> bmem -> Prop) (m1 m2: mem):
    same_context π m1 m2 ->
    R (get π m1) (get π m2) ->
    lift (Lift := lift_powerset) R m1 m2.
  Proof.
    intros Hc Hb.
    unfold lift; simpl.
    replace m2 with (set π (get π m2) m1).
    * change (set π (get π m2) m1) with ((fun bm => set π bm m1) (get π m2)).
      eapply powerset_fmap_intro.
      assumption.
    * rewrite Hc.
      autorewrite with lens.
      reflexivity.
  Qed.

  (** Those are all beautiful and general, but if Coq is to unify anything
    we will have to make them a little bit more specific... *)

  Lemma lift_ec_same_context ef {F V} (ge: Genv.t F V) vargs m1 t vres m2:
    external_call ef ge vargs m1 t vres m2 ->
    same_context π m1 m2.
  Proof.
    apply lift_relation_same_context.
  Qed.

  Lemma lift_ec_unlift ef {F V} (ge: Genv.t F V) vargs m1 t vres m2:
    external_call ef ge vargs m1 t vres m2 ->
    external_call ef ge vargs (get π m1) t vres (get π m2).
  Proof.
    apply lift_relation_unlift.
  Qed.

  Lemma lift_ec_intro ef {F V} (ge: Genv.t F V) vargs m1 t vres m2:
    same_context π m1 m2 ->
    external_call ef ge vargs (get π m1) t vres (get π m2) ->
    external_call ef ge vargs m1 t vres m2.
  Proof.
    change (external_call ef ge vargs (get π m1) t vres)
      with ((fun bm => external_call ef ge vargs bm t vres) (get π m1)).
    apply lift_relation_intro.
  Qed.

  Ltac solve_ec :=
    (apply lift_ec_unlift; assumption) ||
    (apply lift_ec_intro;
       ((eapply lift_ec_same_context; simpl; eassumption) ||
        (eapply lift_ec_unlift; eassumption) ||
        eassumption)).

  Hint Extern 10 => solve_ec : lift.

  Global Instance liftmem_ec_spec: ExternalCalls mem external_function := {}.
  Proof.
    intro ef; split.
    lift (ec_well_typed (external_call_spec ef)).
    lift (ec_arity (external_call_spec ef)).
    lift (ec_symbols_preserved (external_call_spec ef)).
    lift (ec_valid_block (external_call_spec ef)).
    lift (ec_max_perm (external_call_spec ef)).
    lift (ec_readonly (external_call_spec ef)).
    lift_partial (ec_mem_extends (external_call_spec ef)).
      (* Need a theorem about mem_unchanged_on *)
      instantiate (1:=m1').
      admit.
      admit.
    lift_partial (ec_mem_inject (external_call_spec ef)).
      (* ditto *)
      instantiate (1:=m1').
      admit.
      admit.
      admit.
    lift (ec_trace_length (external_call_spec ef)).
    lift_partial (ec_receptive (external_call_spec ef)).
      instantiate (1:=m).
      admit.
    lift_partial (ec_determ (external_call_spec ef)).
      simpl in *; unfold lift in *; simpl in *.
      inversion x.
      inversion x0.
      subst.
      autorewrite with lens in *.
      assumption.
  Qed.
End LIFTEXTCALL.
