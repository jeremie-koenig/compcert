Require Import Coq.Program.Basics.
Require Import Coqlib.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lens.
Require Import LiftMem.
Require Import PredicateMonad.

Section LIFTEXTCALL.
  Context `{Hlm: LiftMem}.
  Context `{ef_ops: ExtFunOps}.
  Context `{ec_ops: !ExtCallOps bmem external_function}.
  Context `{Hec: !ExternalCalls bmem external_function}.

  Instance lift_pred : Lift (bmem -> bmem -> Prop) (mem -> mem -> Prop) :=
    lens_lift (F := (fun X => X -> Prop)).

  Global Instance liftmem_ec_ops: ExtCallOps mem external_function := {
    external_call ef F V ge args m tr ret m' :=
      lift (fun m => external_call ef ge args m tr ret) m m'
  }.

  Lemma lift_external_call ef {F V} (ge: Genv.t F V) vargs m1 t vres m2:
    external_call ef ge vargs m1 t vres m2 ->
    external_call ef ge vargs (get m1) t vres (get m2).
  Proof.
    simpl; unfold lift; simpl.
    intro H.
    inv H.
    autorewrite with lens.
    assumption.
  Qed.

  Hint Resolve lift_external_call: lift.

  Global Instance liftmem_ec_spec: ExternalCalls mem external_function := {}.
  Proof.
    intro ef; split.
    lift (ec_well_typed (external_call_spec ef)).
    lift (ec_arity (external_call_spec ef)).
    lift_partial (ec_symbols_preserved (external_call_spec ef)).
      (* Need [same_context]-related theorems about the predicate monad *)
      admit.
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
