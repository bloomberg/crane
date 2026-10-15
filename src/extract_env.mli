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
    + {b Planning}, as values: the unit's {!Program_facts} and its
      {!Target_plan} -- the inductive kinds, then, once the unit's preparation
      has run, the template-parameter kinds -- each installed by
      {!Install_legacy_plan} into the tables unconverted readers consult.
    + {b Layout} ([Common.Plan]): {!Cpp.prepare_structure} runs
      {!Structure_analysis.analyze} and decides the layout ({!Module_plan});
      then the names of every global and module the unit declares and refers
      to are decided ({!Cpp.plan_names}, {!Cpp.plan_referenced_names}), the
      constructor structs' fields and storage, and every generated
      function's callable plan ({!Cpp.plan_callables}).  All go into the
      target plan, and are installed and frozen.
    + {b Emission} ([Common.Emit Impl], then [Emit Intf]): each file is
      rendered once, and every body translated there.  Emission decides
      nothing but the names of the helpers it lifts out of bodies; the table
      census taken after planning is compared after emission
      ([check_no_late_decisions]), and what it generated against what the
      unit declares ({!Generated_program.check_against_plan}).  The header
      pass reuses the functions the implementation pass generated
      ({!Cpp_ind.generated_once}).
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

(** {2 Pass order}

    The names of the passes each stage runs, in order; see {!Pipeline_trace}.
    Read by [unit_tests/pipeline_manifest.ml]. *)

(** Rewrites and analyses of the extracted structure, once per extraction. *)
val core_pass_names : string list

(** Analysing and planning one unit, before anything else of it runs. *)
val plan_pass_names : string list

(** The unit's remaining preparation, before its layout. *)
val unit_pass_names : string list

(** Deciding the unit's data representation once its preparation has run. *)
val represent_pass_names : string list

(** Settling the unit's layout, naming what it declares and refers to, and
    planning its callables, before anything of it is rendered. *)
val layout_pass_names : string list

(** The steps run on a unit's Core once its target is planned
    ({!Core_elaborate.structure}, {!Callable_abi.install_foreign}), in order. *)
val elaborate_pass_names : string list
