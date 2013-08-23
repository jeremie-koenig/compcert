Require Import Memory.
Require Import AST.
Require Import Events.
Require Export AbstractData.
Require Export AbstractPrimitives.
Require Import LiftMem.
Require Import LiftExtCall.

(** * The [Layer] interface *)

Class Layer mem external_function data prim
  `{mem_ops: !Mem.MemoryOps mem}
  `{inj_ops: !Mem.InjectOps mem mem}
  `{ef_ops: !ExtFunOps external_function}
  `{ec_ops: !ExtCallOps mem external_function}
  `{data_ops: !AbstractDataOps data}
  `{prim_ops: !AbstractPrimOps mem data prim} :=
{
  layer_extfun_spec :> ExternalCalls mem external_function;
  layer_abstract_prim :> AbstractPrimitives mem data prim
}.

(** * Summing [external_function]s *)

(** We can combine two instances of [ExternalCalls] which are based
  on the same memory states to obtain an instances for the sum of
  their types of external functions. *)

Section EFPLUS.
  Context {ef1 ef2 mem: Type}.
  Context `{ef1_ops: !ExtFunOps ef1} `{ef2_ops: !ExtFunOps ef2}.
  Context `{mem_ops: !Mem.MemoryOps mem}.
  Context `{inj_ops: !Mem.InjectOps mem mem}.
  Context `{ec1_ops: !ExtCallOps mem ef1} `{ec2_ops: !ExtCallOps mem ef2}.
(* FIXME: unnecessary?
  Context `{Hmem: !Mem.MemoryStates mem}.
 *)
  Context `{Hec1: !ExternalCalls mem ef1} `{Hec2: !ExternalCalls mem ef2}.

  Instance efplus_ef_ops: ExtFunOps (ef1 + ef2) := {
    ef_sig ef :=
      match ef with
        | inl ef => ef_sig ef
        | inr ef => ef_sig ef
      end;
    ef_inline ef :=
      match ef with
        | inl ef => ef_inline ef
        | inr ef => ef_inline ef
      end;
    ef_reloads ef :=
      match ef with
        | inl ef => ef_reloads ef
        | inr ef => ef_reloads ef
      end
  }.

  Instance efplus_ef_spec: ExternalFunctions (ef1 + ef2).

  Instance efplus_ec_ops: ExtCallOps mem (ef1 + ef2) := {
    external_call ef :=
      match ef with
        | inl ef => external_call ef
        | inr ef => external_call ef
      end
  }.

  Instance efplus_ec_spec: ExternalCalls mem (ef1 + ef2) := {
    external_call_spec ef :=
      match ef with
        | inl ef => external_call_spec ef
        | inr ef => external_call_spec ef
      end
  }.
End EFPLUS.

(** * Deriving the [ExternalCalls] associated with a layer *)

Section LAYER.
  Context `{Hl: Layer}.

  Instance: ExtCallOps (mem × data) external_function :=
    liftmem_ec_ops.

  Instance: ExternalCalls (mem × data) external_function :=
    liftmem_ec_spec.

  Global Instance layer_ef_ops:
    ExtFunOps (external_function + prim) :=
      efplus_ef_ops.

  Global Instance layer_ec_ops:
    ExtCallOps (mem × data) (external_function + prim) :=
      efplus_ec_ops.

  Global Instance layer_ec_spec:
    ExternalCalls (mem × data) (external_function + prim) :=
      efplus_ec_spec.
End LAYER.
