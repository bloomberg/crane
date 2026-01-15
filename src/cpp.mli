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

val pp_type : bool -> Names.variable list -> Miniml.ml_type -> Pp.t
val cpp_descr : Miniml.language_descr

(** Reset all C++ extraction global state.
    MUST be called between separate extractions to avoid state pollution
    when running multiple extractions in the same process (e.g., during 'dune build').
    Clears: struct context, template context, method candidates, method registry, etc. *)
val reset_cpp_state : unit -> unit
