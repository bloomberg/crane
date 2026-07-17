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

(** {1 Extraction Environment and Commands}

    Top-level entry points for the [Crane Extraction] vernacular commands.
    Coordinates the full extraction pipeline:
    {v Rocq source  -->  MiniML  -->  MiniCpp  -->  C++ files v}

    Also handles dependency resolution, file I/O, and extraction-test
    coordination. *)

open Names
open Libnames

(** [Extraction qualid]: extract a single definition and print to stdout.
    @param opaque_access accessor for opaque constant bodies *)
val simple_extraction : opaque_access:Global.indirect_accessor -> qualid -> unit

(** [Crane Extraction "file" qualids]: extract listed definitions to a file.
    @param opaque_access accessor for opaque constant bodies
    @param the optional output filename; [None] prints to stdout
    @param the list of qualified names to extract *)
val full_extraction :
  opaque_access:Global.indirect_accessor -> string option -> qualid list -> unit

(** Perform a full extraction and evaluate [after_print] before the extraction
    state is reset. This lets consumers retain metadata derived from the exact
    names used while printing. *)
val full_extraction_with_result :
  opaque_access:Global.indirect_accessor ->
  string option ->
  qualid list ->
  (unit -> 'a) ->
  'a

(** [Separate Extraction qualids]: extract each definition to its own file.
    @param opaque_access accessor for opaque constant bodies
    @param the list of qualified names to extract *)
val separate_extraction :
  opaque_access:Global.indirect_accessor -> qualid list -> unit

(** [Extraction Library lib]: extract an entire library module.
    @param opaque_access accessor for opaque constant bodies
    @param the second argument is [true] for recursive (transitive) extraction
    @param lib the library module identifier to extract *)
val extraction_library :
  opaque_access:Global.indirect_accessor -> bool -> lident -> unit

(** Extract to file then compile with clang. Used by the test suite.
    @param opaque_access accessor for opaque constant bodies
    @param the optional output filename; [None] uses a temp file
    @param the list of qualified names to extract and compile *)
val extract_and_compile :
  opaque_access:Global.indirect_accessor -> string option -> qualid list -> unit

(** Build the complete MiniML structure for a set of definitions.
    @param opaque_access accessor for opaque constant bodies
    @param the list of global references to include
    @param the list of module paths to include in full
    @return the extracted MiniML structure *)
val mono_environment :
  opaque_access:Global.indirect_accessor ->
  GlobRef.t list ->
  ModPath.t list ->
  Miniml.ml_structure

(** Pretty-print a single declaration. Used by the Relation Extraction plugin.
    @param struc the full extraction structure (used for renaming context)
    @param mp the module path under which the declaration lives
    @param decl the declaration to render
    @return a pretty-printed Pp.t document *)
val print_one_decl : Miniml.ml_structure -> ModPath.t -> Miniml.ml_decl -> Pp.t

(** [Show Extraction]: show the extraction of the current ongoing proof.
    @param pstate the current proof state *)
val show_extraction : pstate:Declare.Proof.t -> unit
