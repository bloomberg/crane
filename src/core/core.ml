(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core, the functional program extraction produces ([grammar.ml] defines
    the language).  The grammar module is not exported, only its families,
    each under its final name: so a function the grammar provides for a
    type it keeps private -- making a metavariable cell, a global use, a
    recursive group -- is called only from its family's module. *)

module Binder_name = Binder_name
module Decl = Decl
module Erasure_reason = Erasure_reason
module Expr = Expr
module Extracted = Extracted
module Fingerprint = Fingerprint
module Global_use = Global_use
module Inductive = Inductive
module Interface = Interface
module Match = Match
module Module = Module
module Nonempty = Nonempty
module Occurrence = Occurrence
module Open = Open
module Pattern = Pattern
module Positional = Positional
module Program = Program
module Record = Record
module Recursion = Recursion
module Schema = Schema
module Signature = Signature
module Type = Type
