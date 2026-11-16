(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core, the functional program extraction produces and the first IR of the
    pipeline: [extraction.ml] builds it, the Core passes ({!Core_phase})
    rewrite it, and lowering (Translation and the Translation_* modules)
    turns it into CppIR.  [grammar.ml] defines the language.

    This module is the namespace's interface.  The grammar module is not
    exported, only its families, each under its final name: so a function
    the grammar provides for a type it keeps private -- making a
    metavariable cell, a global use, a recursive group -- is called only from
    its family's module.  Modules of [src/core/] depend on nothing of the
    compiler but {!Scheme}. *)

(** The name a binder carries. *)
module Binder_name = Binder_name

(** Top-level definitions. *)
module Decl = Decl

(** Why extraction erased an argument or subterm. *)
module Erasure_reason = Erasure_reason

(** Terms. *)
module Expr = Expr

(** Metavariables, which exist only until the program is frozen. *)
module Extracted = Extracted

(** Digests of a program, to check two readers saw the same one. *)
module Fingerprint = Fingerprint

(** The use of a global, with its type-scheme instantiation. *)
module Global_use = Global_use

(** Inductive definitions, their kinds and equivalences. *)
module Inductive = Inductive

(** A whole program's module signatures. *)
module Interface = Interface

(** Match branches. *)
module Match = Match

(** The module language. *)
module Module = Module

(** Lists with at least one element. *)
module Nonempty = Nonempty

(** The identity of one node of a term. *)
module Occurrence = Occurrence

(** The phase index of the grammar: [extracted], whose types may hold
    metavariables, and [frozen], whose cannot. *)
module Phase = Phase

(** Open annotations: metavariables freezing left unsolved. *)
module Open = Open

(** Match patterns. *)
module Pattern = Pattern

(** The default name of a declaration's type variable. *)
module Positional = Positional

(** A whole program's module structures. *)
module Program = Program

(** Record and type-class fields. *)
module Record = Record

(** Recursive declaration groups and local recursive groups. *)
module Recursion = Recursion

(** Constants' type schemes and their binder layouts. *)
module Schema = Schema

(** What extraction kept and erased of an object's arguments. *)
module Signature = Signature

(** Type expressions. *)
module Type = Type

(** Frozen types and terms as types and terms of any phase. *)
module Widen = Widen

(** Terms and programs taken from one phase to another, annotation by
    annotation. *)
module Retype = Retype

(** Freezing extracted types and terms, minting an open annotation for each
    unsolved metavariable. *)
module Freezer = Freezer

(** The type-variable numberings of a scheme. *)
module Scheme = Scheme

(** Global references compared as one entity, and their sets and maps. *)
module Ref = Ref

(** The identity of a Core binder. *)
module Binder = Binder

(** The lexical environment of a Core body. *)
module Lexenv = Lexenv
