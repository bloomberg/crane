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
    coordination.

    {2 The phases of one unit}

    [print_structure_to_file] runs, in this order:

    + {b Extraction} ([mono_environment], [optimize_struct]): Rocq terms to
      the MiniML structure, simplified.
    + {b Source analysis}, mutating tables and packets in place:
      [mark_used_customs] (and the non-atomic reference-count check that
      depends on it), [mark_higher_order_projections],
      [align_functor_instance_kinds], [demote_value_typeclasses].
    + {b Discovery} ([Common.Discover]): {!Cpp.prepare_structure} runs
      {!Structure_analysis.analyze} and installs its layout facts, then both
      files are rendered and the text discarded.  What survives is what the
      renders recorded: names, method registrations, wrapper and alias
      tables.  Every body is translated here.
    + {b Emission} ([Common.Emit Impl], then [Emit Intf]): both files are
      rendered for real.  Emission is meant to decide nothing; the table
      census taken after discovery is compared after emission
      ([check_no_late_decisions]).  The header pass reuses the functions the
      implementation pass generated ({!Cpp_ind.generated_once}).
    + {b Demands} are frozen ([Table.freeze_demands]) and each file is written
      with the preamble its body demanded, then formatted.

    Within a render, each MiniML declaration is generated
    ({!Cpp_ind.generate}, {!Gen_decls}, which translate bodies through
    {!Translation}), finished ({!Cpp_pipeline.finish}: loopify, depth
    flattening, last-use moves, borrow projections, constraint settling,
    erasure, free type variables), and printed ({!Cpp_print.pp_cpp_decl},
    which accepts only a {!Cpp_erasure.settled} declaration).

    Mutable state is registered with {!State} under one of two scopes:
    [Extraction] (one command) and [Unit] (one generated file).
    [CRANE_COUNT_GENERATION] reports how many bodies each phase translated;
    [CRANE_TRACE_PASSES] reports what each finishing pass changed. *)

open Names
open Libnames

(** [Extraction qualid]: extract a single definition and print to stdout.
    @param opaque_access accessor for opaque constant bodies *)
val simple_extraction : opaque_access:Global.indirect_accessor -> qualid -> unit

(** [Crane Extraction "file" qualids]: extract listed definitions to a file.
    @param validate reject an output filename that escapes the output directory
      (default [true]); trusted callers with an internal path pass [false]
    @param opaque_access accessor for opaque constant bodies
    @param the optional output filename; [None] prints to stdout
    @param the list of qualified names to extract *)
val full_extraction :
  ?validate:bool ->
  opaque_access:Global.indirect_accessor ->
  string option ->
  qualid list ->
  unit

(** How C++ spells an extracted constant, and Rocq's [tt], from where the
    constant is declared -- read while the unit's naming tables were live. *)
type export = {ex_ref : Names.GlobRef.t; ex_name : string; ex_unit : string}

(** {!full_extraction}, returning an {!export} for each requested
    constant. *)
val full_extraction_exports :
  ?validate:bool ->
  opaque_access:Global.indirect_accessor ->
  string option ->
  qualid list ->
  export list

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
