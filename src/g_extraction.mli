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

(** {1 Rocq Command Grammar for Crane Extraction}

    Interface for the [.mlg]-generated parser that wires Crane's vernacular
    commands (e.g. [Crane Extraction], [Crane Benchmark], and the [Set Crane
    ...] options) into Rocq's command grammar. The values below are the
    {!Genarg} witnesses for the custom argument entries used by those command
    rules; they let the generic-argument machinery serialize, print, and
    interpret the corresponding parameters. Each witness pairs with a
    [Table]-side representation (see {!Table.int_or_id} and {!Table.lang}). *)

(** Vernacular argument witness for integer-or-identifier parameters. *)
val wit_crane_int_or_id : Table.int_or_id Genarg.vernac_genarg_type

(** Vernacular argument witness for target language selection. *)
val wit_crane_language : Table.lang Genarg.vernac_genarg_type

(** Vernacular argument witness for C++ name string parameters. *)
val wit_cppname : string Genarg.vernac_genarg_type
