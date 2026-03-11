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

    Converts {!Minicpp} AST nodes into C++ syntax using the {!Pp}
    pretty-printing combinators. Lower-level rendering is delegated to:
    - {!Cpp_state} — mutable state and utilities
    - {!Cpp_names} — name resolution and qualification
    - {!Cpp_print} — type/expr/stmt/field/declaration pretty-printing
    - {!Cpp_ind} — inductive type rendering and decl-level dispatch *)

(** Language descriptor for C++. Provides the preamble, file suffix,
    pretty-printers, and other hooks that {!Extract_env} needs to drive a full
    extraction pass. *)
val cpp_descr : Miniml.language_descr
