(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the main instance for the type class
  [AST.SyntaxConfiguration]. *)

Require Import Coqlib.
Require Import Integers.
Require Import AST.

Inductive external_function : Type :=
  | EF_external (name: ident) (sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free.
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)

(** The type signature of an external function. *)

Definition ef_sig (ef: external_function): signature :=
  match ef with
  | EF_external name sg => sg
  | EF_malloc => mksignature (Tint :: nil) (Some Tint)
  | EF_free => mksignature (Tint :: nil) None
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads (ef: external_function) : bool :=
  true.

Local Instance ef_ops: ExtFunOps external_function := {
  ef_sig := ef_sig;
  ef_reloads := ef_reloads
}.

Local Instance sc_ops: SyntaxConfigOps external_function := {
}.

Local Instance ef_proof: ExternalFunctions external_function := {
}.

Local Instance ef_spec: SyntaxConfiguration external_function := {
  ugly_workaround_dependee := unit;
  ugly_workaround_depender := tt
}.
