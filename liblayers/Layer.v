Require Import Memory.
Require Import AST.
Require Import Events.
Require Export AbstractData.
Require Export AbstractPrimitives.
Require Import LiftMem.
Require Import LiftExtCall.

(** * The [Layer] interface *)

(** This is the base configuration which a layer can complement to
  obtain a [CompilerConfiguration]. *)

Class BaseConfigOps mem external_function
  `{cc_ops: CompilerConfigOps mem external_function} := {}.

Class BaseConfiguration mem external_function
  `{bc_ops: BaseConfigOps mem external_function} :=
{
  base_config_compiler_config: CompilerConfiguration mem external_function
}.

(** A layer combines a base configuration with a type of abstract
  data and a set of abstract primitives. *)

Class Layer mem external_function data prim
  `{ec_ops: BaseConfigOps mem external_function}
  `{data_ops: !AbstractDataOps data}
  `{prim_ops: !AbstractPrimOps mem data prim} :=
{
  layer_base_config :> BaseConfiguration mem external_function;
  layer_abstract_prim :> AbstractPrimitives mem data prim
}.

(** * Summing [external_function]s *)

(** We can combine two instances of [ExternalCalls] which are based
  on the same memory states to obtain an instances for the sum of
  their types of external functions. *)

Section EFPLUS.
  Context {mem ef1 ef2: Type}.
  Context `{Hmem: Mem.MemoryModel mem}.
  Context `{ef1_ops: !ExtFunOps ef1} `{ef2_ops: !ExtFunOps ef2}.
  Context `{ec1_ops: !ExtCallOps mem ef1} `{ec2_ops: !ExtCallOps mem ef2}.
  Context `{Hec1: !ExternalCalls mem ef1} `{Hec2: !ExternalCalls mem ef2}.

  Instance efplus_ef_ops: ExtFunOps (ef1 + ef2) := {
    ef_sig ef :=
      match ef with
        | inl ef => ef_sig ef
        | inr ef => ef_sig ef
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

(** * Deriving the [CompilerConfiguration] associated with a layer *)

Section LAYER.
  Context `{Hl: Layer}.
  Local Existing Instance base_config_compiler_config.

  Instance: ExtCallOps (mem × data) external_function :=
    liftmem_ec_ops.

  Instance: ExternalCalls (mem × data) external_function :=
    liftmem_ec_spec.

  Instance: CompilerConfigOps (mem × data) external_function := {}.

  Instance: CompilerConfiguration (mem × data) external_function := {}.

  Global Instance layer_ef_ops:
    ExtFunOps (external_function + prim) :=
      efplus_ef_ops.

  Global Instance layer_ec_ops:
    ExtCallOps (mem × data) (external_function + prim) :=
      efplus_ec_ops.

  Global Instance layer_sc_ops:
    SyntaxConfigOps (external_function + prim) := {}.

  Global Instance layer_cc_ops:
    CompilerConfigOps (mem × data) (external_function + prim) := {}.

  Local Instance layer_ec_spec:
    ExternalCalls (mem × data) (external_function + prim) :=
      efplus_ec_spec.

  Local Instance layer_sc_spec:
    SyntaxConfiguration (external_function + prim) := {
      ugly_workaround_depender := tt
    }.

  Global Instance layer_cc_spec:
    CompilerConfiguration (mem × data) (external_function + prim) := {}.
End LAYER.
