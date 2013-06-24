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
  [AST.ExternalFunctions]. *)

Require Import Coqlib.
Require Import Integers.
Require Import AST.

Inductive external_function : Type :=
  | EF_external (name: ident) (sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_builtin (name: ident) (sg: signature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | EF_vload (chunk: memory_chunk)
     (** A volatile read operation.  If the adress given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (chunk: memory_chunk)
     (** A volatile store operation.   If the adress given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | EF_vload_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile load operation from a global variable. 
         Specialized version of [EF_vload]. *)
  | EF_vstore_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile store operation in a global variable. 
         Specialized version of [EF_vstore]. *)
  | EF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | EF_annot (text: ident) (targs: list annot_arg)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (text: ident) (targ: typ)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | EF_inline_asm (text: ident).
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)

(** The type signature of an external function. *)

Definition ef_sig (ef: external_function): signature :=
  match ef with
  | EF_external name sg => sg
  | EF_builtin name sg => sg
  | EF_vload chunk => mksignature (Tint :: nil) (Some (type_of_chunk chunk))
  | EF_vstore chunk => mksignature (Tint :: type_of_chunk chunk :: nil) None
  | EF_vload_global chunk _ _ => mksignature nil (Some (type_of_chunk chunk))
  | EF_vstore_global chunk _ _ => mksignature (type_of_chunk chunk :: nil) None
  | EF_malloc => mksignature (Tint :: nil) (Some Tint)
  | EF_free => mksignature (Tint :: nil) None
  | EF_memcpy sz al => mksignature (Tint :: Tint :: nil) None
  | EF_annot text targs => mksignature (annot_args_typ targs) None
  | EF_annot_val text targ => mksignature (targ :: nil) (Some targ)
  | EF_inline_asm text => mksignature nil None
  end.

(** Whether an external function should be inlined by the compiler. *)

Definition ef_inline (ef: external_function) : bool :=
  match ef with
  | EF_external name sg => false
  | EF_builtin name sg => true
  | EF_vload chunk => true
  | EF_vstore chunk => true
  | EF_vload_global chunk id ofs => true
  | EF_vstore_global chunk id ofs => true
  | EF_malloc => false
  | EF_free => false
  | EF_memcpy sz al => true
  | EF_annot text targs => true
  | EF_annot_val text targ => true
  | EF_inline_asm text => true
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads (ef: external_function) : bool :=
  match ef with
  | EF_annot text targs => false
  | _ => true
  end.

Local Instance ef_ops: ExtFunOps external_function := {
  ef_sig := ef_sig;
  ef_inline := ef_inline;
  ef_reloads := ef_reloads
}.

Local Instance ef_spec: ExternalFunctions external_function := {
}.

