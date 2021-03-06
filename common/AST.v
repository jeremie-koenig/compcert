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

(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.

Set Implicit Arguments.

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

Definition ident := positive.

Definition ident_eq := peq.

(** The intermediate languages are weakly typed, using only two types:
  [Tint] for integers and pointers, and [Tfloat] for floating-point
  numbers. *)

Inductive typ : Type :=
  | Tint : typ
  | Tfloat : typ.

Definition typesize (ty: typ) : Z :=
  match ty with Tint => 4 | Tfloat => 8 end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. destruct ty; simpl; omega. Qed.

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque typ_eq.

Lemma opt_typ_eq: forall (t1 t2: option typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. apply typ_eq. Defined.
Global Opaque opt_typ_eq.

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating the number and types of arguments,
  as well as the type of the returned value if any.  These signatures
  are used in particular to determine appropriate calling conventions
  for the function. *)

Record signature : Type := mksignature {
  sig_args: list typ;
  sig_res: option typ
}.

Definition proj_sig_res (s: signature) : typ :=
  match s.(sig_res) with
  | None => Tint
  | Some t => t
  end.

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

Inductive memory_chunk : Type :=
  | Mint8signed : memory_chunk     (**r 8-bit signed integer *)
  | Mint8unsigned : memory_chunk   (**r 8-bit unsigned integer *)
  | Mint16signed : memory_chunk    (**r 16-bit signed integer *)
  | Mint16unsigned : memory_chunk  (**r 16-bit unsigned integer *)
  | Mint32 : memory_chunk          (**r 32-bit integer, or pointer *)
  | Mfloat32 : memory_chunk        (**r 32-bit single-precision float *)
  | Mfloat64 : memory_chunk        (**r 64-bit double-precision float *)
  | Mfloat64al32 : memory_chunk.   (**r 64-bit double-precision float, 4-aligned *)

(** The type (integer/pointer or float) of a chunk. *)

Definition type_of_chunk (c: memory_chunk) : typ :=
  match c with
  | Mint8signed => Tint
  | Mint8unsigned => Tint
  | Mint16signed => Tint
  | Mint16unsigned => Tint
  | Mint32 => Tint
  | Mfloat32 => Tfloat
  | Mfloat64 => Tfloat
  | Mfloat64al32 => Tfloat
  end.

(** Initialization data for global variables. *)

Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_float32: float -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> int -> init_data.  (**r address of symbol + offset *)

(** Information attached to global variables. *)

Record globvar (V: Type) : Type := mkglobvar {
  gvar_info: V;                    (**r language-dependent info, e.g. a type *)
  gvar_init: list init_data;       (**r initialization data *)
  gvar_readonly: bool;             (**r read-only variable? (const) *)
  gvar_volatile: bool              (**r volatile variable? *)
}.

(** Whole programs consist of:
- a collection of global definitions (name and description);
- the name of the ``main'' function that serves as entry point in the program.

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

Inductive globdef (F V: Type) : Type :=
  | Gfun (f: F)
  | Gvar (v: globvar V).

Implicit Arguments Gfun [F V].
Implicit Arguments Gvar [F V].

Record program (F V: Type) : Type := mkprogram {
  prog_defs: list (ident * globdef F V);
  prog_main: ident
}.

Definition prog_defs_names (F V: Type) (p: program F V) : list ident :=
  List.map fst p.(prog_defs).

(** * Generic transformations over programs *)

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.

Definition transform_program_globdef (idg: ident * globdef A V) : ident * globdef B V :=
  match idg with
  | (id, Gfun f) => (id, Gfun (transf f))
  | (id, Gvar v) => (id, Gvar v)
  end.

Definition transform_program (p: program A V) : program B V :=
  mkprogram
    (List.map transform_program_globdef p.(prog_defs))
    p.(prog_main).

Lemma transform_program_function:
  forall p i tf,
  In (i, Gfun tf) (transform_program p).(prog_defs) ->
  exists f, In (i, Gfun f) p.(prog_defs) /\ transf f = tf.
Proof.
  simpl. unfold transform_program. intros.
  exploit list_in_map_inv; eauto. 
  intros [[i' gd] [EQ IN]]. simpl in EQ. destruct gd; inv EQ. 
  exists f; auto.
Qed.

End TRANSF_PROGRAM.

(** The following is a more general presentation of [transform_program] where 
  global variable information can be transformed, in addition to function
  definitions.  Moreover, the transformation functions can fail and
  return an error message. *)

Open Local Scope error_monad_scope.
Open Local Scope string_scope.

Section TRANSF_PROGRAM_GEN.

Variables A B V W: Type.
Variable transf_fun: A -> res B.
Variable transf_var: V -> res W.

Definition transf_globvar (g: globvar V) : res (globvar W) :=
  do info' <- transf_var g.(gvar_info);
  OK (mkglobvar info' g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)).

Fixpoint transf_globdefs (l: list (ident * globdef A V)) : res (list (ident * globdef B W)) :=
  match l with
  | nil => OK nil
  | (id, Gfun f) :: l' =>
      match transf_fun f with
      | Error msg => Error (MSG "In function " :: CTX id :: MSG ": " :: msg)
      | OK tf =>
          do tl' <- transf_globdefs l'; OK ((id, Gfun tf) :: tl')
      end
  | (id, Gvar v) :: l' =>
      match transf_globvar v with
      | Error msg => Error (MSG "In variable " :: CTX id :: MSG ": " :: msg)
      | OK tv =>
          do tl' <- transf_globdefs l'; OK ((id, Gvar tv) :: tl')
      end
  end.

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
  do gl' <- transf_globdefs p.(prog_defs); OK(mkprogram gl' p.(prog_main)).

Lemma transform_partial_program2_function:
  forall p tp i tf,
  transform_partial_program2 p = OK tp ->
  In (i, Gfun tf) tp.(prog_defs) ->
  exists f, In (i, Gfun f) p.(prog_defs) /\ transf_fun f = OK tf.
Proof.
  intros. monadInv H. simpl in H0. 
  revert x EQ H0. induction (prog_defs p); simpl; intros.
  inv EQ. contradiction.
  destruct a as [id [f|v]].
  destruct (transf_fun f) as [tf1|msg] eqn:?; monadInv EQ.
  simpl in H0; destruct H0. inv H. exists f; auto. 
  exploit IHl; eauto. intros [f' [P Q]]; exists f'; auto.
  destruct (transf_globvar v) as [tv1|msg] eqn:?; monadInv EQ.
  simpl in H0; destruct H0. inv H.
  exploit IHl; eauto. intros [f' [P Q]]; exists f'; auto.
Qed.

Lemma transform_partial_program2_variable:
  forall p tp i tv,
  transform_partial_program2 p = OK tp ->
  In (i, Gvar tv) tp.(prog_defs) ->
  exists v,
     In (i, Gvar(mkglobvar v tv.(gvar_init) tv.(gvar_readonly) tv.(gvar_volatile))) p.(prog_defs)
  /\ transf_var v = OK tv.(gvar_info).
Proof.
  intros. monadInv H. simpl in H0. 
  revert x EQ H0. induction (prog_defs p); simpl; intros.
  inv EQ. contradiction.
  destruct a as [id [f|v]].
  destruct (transf_fun f) as [tf1|msg] eqn:?; monadInv EQ.
  simpl in H0; destruct H0. inv H.
  exploit IHl; eauto. intros [v' [P Q]]; exists v'; auto.
  destruct (transf_globvar v) as [tv1|msg] eqn:?; monadInv EQ.
  simpl in H0; destruct H0. inv H.
  monadInv Heqr. simpl. exists (gvar_info v). split. left. destruct v; auto. auto.
  exploit IHl; eauto. intros [v' [P Q]]; exists v'; auto.
Qed.

Lemma transform_partial_program2_main:
  forall p tp,
  transform_partial_program2 p = OK tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  intros. monadInv H. reflexivity.
Qed.

(** Additionally, we can also "augment" the program with new global definitions
  and a different "main" function. *)

Section AUGMENT.

Variable new_globs: list(ident * globdef B W).
Variable new_main: ident.

Definition transform_partial_augment_program (p: program A V) : res (program B W) :=
  do gl' <- transf_globdefs p.(prog_defs);
  OK(mkprogram (gl' ++ new_globs) new_main).

Lemma transform_partial_augment_program_main:
  forall p tp,
  transform_partial_augment_program p = OK tp ->
  tp.(prog_main) = new_main.
Proof.
  intros. monadInv H. reflexivity.
Qed.

End AUGMENT.

Remark transform_partial_program2_augment:
  forall p,
  transform_partial_program2 p =
  transform_partial_augment_program nil p.(prog_main) p.
Proof.
  unfold transform_partial_program2, transform_partial_augment_program; intros.
  destruct (transf_globdefs (prog_defs p)); auto.
  simpl. f_equal. f_equal. rewrite <- app_nil_end. auto.
Qed.

End TRANSF_PROGRAM_GEN.

(** The following is a special case of [transform_partial_program2],
  where only function definitions are transformed, but not variable definitions. *)

Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Type.
Variable transf_partial: A -> res B.

Definition transform_partial_program (p: program A V) : res (program B V) :=
  transform_partial_program2 transf_partial (fun v => OK v) p.

Lemma transform_partial_program_main:
  forall p tp,
  transform_partial_program p = OK tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  apply transform_partial_program2_main.
Qed.

Lemma transform_partial_program_function:
  forall p tp i tf,
  transform_partial_program p = OK tp ->
  In (i, Gfun tf) tp.(prog_defs) ->
  exists f, In (i, Gfun f) p.(prog_defs) /\ transf_partial f = OK tf.
Proof.
  apply transform_partial_program2_function. 
Qed.

End TRANSF_PARTIAL_PROGRAM.

Lemma transform_program_partial_program:
  forall (A B V: Type) (transf: A -> B) (p: program A V),
  transform_partial_program (fun f => OK(transf f)) p = OK(transform_program transf p).
Proof.
  intros.
  unfold transform_partial_program, transform_partial_program2, transform_program; intros.
  replace (transf_globdefs (fun f => OK (transf f)) (fun v => OK v) p.(prog_defs))
     with (OK (map (transform_program_globdef transf) p.(prog_defs))).
  auto. 
  induction (prog_defs p); simpl.
  auto.
  destruct a as [id [f|v]]; rewrite <- IHl.
    auto.
    destruct v; auto.
Qed.

(** The following is a relational presentation of 
  [transform_partial_augment_preogram].  Given relations between function
  definitions and between variable information, it defines a relation
  between programs stating that the two programs have appropriately related
  shapes (global names are preserved and possibly augmented, etc) 
  and that identically-named function definitions
  and variable information are related. *)

Section MATCH_PROGRAM.

Variable A B V W: Type.
Variable match_fundef: A -> B -> Prop.
Variable match_varinfo: V -> W -> Prop.

Inductive match_globdef: ident * globdef A V -> ident * globdef B W -> Prop :=
  | match_glob_fun: forall id f1 f2,
      match_fundef f1 f2 ->
      match_globdef (id, Gfun f1) (id, Gfun f2)
  | match_glob_var: forall id init ro vo info1 info2,
      match_varinfo info1 info2 ->
      match_globdef (id, Gvar (mkglobvar info1 init ro vo)) (id, Gvar (mkglobvar info2 init ro vo)).

Definition match_program (new_globs : list (ident * globdef B W))
                         (new_main : ident)
                         (p1: program A V)  (p2: program B W) : Prop :=
  (exists tglob, list_forall2 match_globdef p1.(prog_defs) tglob /\
                 p2.(prog_defs) = tglob ++ new_globs) /\
  p2.(prog_main) = new_main.

End MATCH_PROGRAM.

Lemma transform_partial_augment_program_match:
  forall (A B V W: Type)
         (transf_fun: A -> res B)
         (transf_var: V -> res W)
         (p: program A V) 
         (new_globs : list (ident * globdef B W))
         (new_main : ident)
         (tp: program B W),
  transform_partial_augment_program transf_fun transf_var new_globs new_main p = OK tp ->
  match_program 
    (fun fd tfd => transf_fun fd = OK tfd)
    (fun info tinfo => transf_var info = OK tinfo)
    new_globs new_main
    p tp.
Proof.
  unfold transform_partial_augment_program; intros. monadInv H. 
  red; simpl. split; auto. exists x; split; auto.
  revert x EQ. generalize (prog_defs p). induction l; simpl; intros.
  monadInv EQ. constructor.
  destruct a as [id [f|v]]. 
  (* function *)
  destruct (transf_fun f) as [tf|?] eqn:?; monadInv EQ. 
  constructor; auto. constructor; auto.
  (* variable *)
  unfold transf_globvar in EQ.
  destruct (transf_var (gvar_info v)) as [tinfo|?] eqn:?; simpl in EQ; monadInv EQ.
  constructor; auto. destruct v; simpl in *. constructor; auto.
Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

Class ExtFunOps (external_function: Type) := {
  ef_sig: external_function -> signature;
  ef_reloads: external_function -> bool
}.

Class ExternalFunctions (external_function: Type)
  `{ef_ops: ExtFunOps external_function} :=
{
}.

Arguments ExternalFunctions external_function {ef_ops}.

Class SyntaxConfigOps external_function
  `{ef_ops: ExtFunOps external_function} :=
{
}.

Class SyntaxConfiguration external_function
  `{sf_ops: SyntaxConfigOps external_function}: Prop :=
{
  syntax_external_functions :> ExternalFunctions external_function;

  (* Prevent [intuition] from destructing instances of [SyntaxConfiguration],
    so that the old proof scripts continue to work. *)
  ugly_workaround_dependee: Type;
  ugly_workaround_depender: ugly_workaround_dependee
}.

Arguments SyntaxConfigOps external_function {ef_ops}.
Arguments SyntaxConfiguration external_function {ef_ops sf_ops}.

Inductive annot_arg : Type :=
  | AA_arg (ty: typ)
  | AA_int (n: int)
  | AA_float (n: float).

Fixpoint annot_args_typ (targs: list annot_arg) : list typ :=
  match targs with
  | nil => nil
  | AA_arg ty :: targs' => ty :: annot_args_typ targs'
  | _ :: targs' => annot_args_typ targs'
  end.

(** Function definitions are the union of internal and external functions. *)

Inductive fundef `{sc_ops: SyntaxConfigOps} (F: Type): Type :=
  | Internal: F -> fundef F
  | External: external_function -> fundef F.

Arguments External {external_function ef_ops sc_ops} [F] _.

Section TRANSF_FUNDEF.

Context `{Hsc: SyntaxConfiguration}.
Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
  match fd with
  | Internal f => Internal (transf f)
  | External ef => External ef
  end.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Context `{Hsc: SyntaxConfiguration}.
Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: fundef A): res (fundef B) :=
  match fd with
  | Internal f => do f' <- transf_partial f; OK (Internal f')
  | External ef => OK (External ef)
  end.

End TRANSF_PARTIAL_FUNDEF.
