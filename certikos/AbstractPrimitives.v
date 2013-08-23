Require Import AST.
Require Import Memory.
Require Import Events.
Require Import LiftExtCall.
Require Import AbstractData.

Class AbstractPrimOps (mem data prim: Type)
  `{mem_ops: Mem.MemoryOps mem}
  `{mem_inj: !Mem.InjectOps mem mem}
  `{data_ops: AbstractDataOps data} :=
{
  prim_sig (p: prim): signature;
  prim_extcall_sem (p: prim): extcall_sem (mem := mem × data)
}.

Class AbstractPrimitives (mem data prim: Type)
  `{prim_ops: AbstractPrimOps mem data prim} :=
{
  prim_mem :> Mem.MemoryStates mem;
  prim_abstract_data :> AbstractData data;
  prim_extcall_properties (p: prim):
    extcall_properties (prim_extcall_sem p) (prim_sig p)
(* TODO: possibly,
  prim_preserves_invariants (p: prim):
    ... *)
}.


(** [AbstractPrimitives] implements [ExternalCalls]. *)
Section EXTCALLS.
  Context `{Hprim: AbstractPrimitives}.

  Global Instance prim_ef_ops: ExtFunOps prim := {
    ef_sig p := prim_sig p;
    ef_inline p := false;
    ef_reloads p := false
  }.

  Global Instance prim_ef_spec: ExternalFunctions prim := {
  }.

  Global Instance prim_ec_ops: ExtCallOps (mem × data) prim := {
    external_call p := prim_extcall_sem p
  }.

  Global Instance prim_ec_spec: ExternalCalls (mem × data) prim := {
    external_call_spec p := prim_extcall_properties p
  }.
End EXTCALLS.
