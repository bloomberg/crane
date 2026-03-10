(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {1 C++ Pretty-Printer}

    Final stage of the extraction pipeline:
    {v MiniCpp AST  --[cpp.ml]-->  C++ source code v}

    Converts {!Minicpp} AST nodes into C++ syntax using the
    {!Pp} pretty-printing combinators. *)

val pp_type : bool -> Names.variable list -> Miniml.ml_type -> Pp.t
(** [pp_type needs_typename vl ty] renders [ty] as C++ syntax.
    @param needs_typename if [true], prefix dependent types with [typename]
    @param vl type variable list for resolving type variable indices *)

val cpp_descr : Miniml.language_descr
(** Language descriptor for C++.  Provides the preamble, file suffix,
    pretty-printers, and other hooks that {!Extract_env} needs to
    drive a full extraction pass. *)

(** Reset all C++ extraction global state.
    MUST be called between separate extractions to avoid state pollution
    when running multiple extractions in the same process (e.g., during 'dune build').
    Clears: struct context, template context, method candidates, method registry, etc. *)
val reset_cpp_state : unit -> unit
