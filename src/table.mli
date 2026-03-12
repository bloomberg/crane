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

(** Extraction environment tables, custom extraction mappings, and configuration
    parameters. *)

open Names
open Libnames
open Miniml
open Declarations

module Refset' : CSig.USetS with type elt = GlobRef.t

module Refmap' : CSig.UMapS with type key = GlobRef.t

(** Get a safe basename identifier from a global reference. *)
val safe_basename_of_global : GlobRef.t -> Id.t

(** {2 Warning and Error messages} *)

(** Issue warning about axioms. *)
val warning_axioms : unit -> unit

(** Issue warning about opaques. *)
val warning_opaques : bool -> unit

(** Issue warning about ambiguous name. *)
val warning_ambiguous_name :
  ?loc:Loc.t -> qualid * ModPath.t * GlobRef.t -> unit

(** Issue warning about identifier. *)
val warning_id : string -> unit

(** Report error for axiom scheme. *)
val error_axiom_scheme : ?loc:Loc.t -> GlobRef.t -> int -> 'a

(** Report error for constant. *)
val error_constant : ?loc:Loc.t -> GlobRef.t -> 'a

(** Report error for inductive. *)
val error_inductive : ?loc:Loc.t -> GlobRef.t -> 'a

(** Report error for number of constructors. *)
val error_nb_cons : unit -> 'a

(** Report error for module clash. *)
val error_module_clash : ModPath.t -> ModPath.t -> 'a

(** Report error for missing module expression. *)
val error_no_module_expr : ModPath.t -> 'a

(** Report error for singleton becoming prop. *)
val error_singleton_become_prop : inductive -> 'a

(** Report error for unknown module. *)
val error_unknown_module : ?loc:Loc.t -> qualid -> 'a

(** Report error for scheme. *)
val error_scheme : unit -> 'a

(** Report error for non-visible reference. *)
val error_not_visible : GlobRef.t -> 'a

(** Report error for MPfile used as module. *)
val error_MPfile_as_mod : ModPath.t -> bool -> 'a

(** Check if inside section. *)
val check_inside_section : unit -> unit

(** Check if module file is loaded. *)
val check_loaded_modfile : ModPath.t -> unit

(** Get message for implicit kill reason. *)
val msg_of_implicit : kill_reason -> string

(** Issue error or warning for remaining implicit. *)
val err_or_warn_remaining_implicit : kill_reason -> unit

(** Print info message about file. *)
val info_file : string -> unit

(** {2 Utilities about module_path, kernel_names, and GlobRef.t} *)

(** Check if kernel name occurs in reference. *)
val occur_kn_in_ref : MutInd.t -> GlobRef.t -> bool

(** Get kernel name representation of reference. *)
val repr_of_r : GlobRef.t -> KerName.t

(** Get module path of reference. *)
val modpath_of_r : GlobRef.t -> ModPath.t

(** Get label of reference. *)
val label_of_r : GlobRef.t -> Label.t

(** Get base module path. *)
val base_mp : ModPath.t -> ModPath.t

(** Check if module path is a module file. *)
val is_modfile : ModPath.t -> bool

(** Get string representation of module file. *)
val string_of_modfile : ModPath.t -> string

(** Get file name from module file. *)
val file_of_modfile : ModPath.t -> string

(** Check if module path is toplevel. *)
val is_toplevel : ModPath.t -> bool

(** Check if at toplevel. *)
val at_toplevel : ModPath.t -> bool

(** Get length of module path. *)
val mp_length : ModPath.t -> int

(** Get all prefixes of module path. *)
val prefixes_mp : ModPath.t -> MPset.t

(** Find common prefix from list of module paths. *)
val common_prefix_from_list : ModPath.t -> ModPath.t list -> ModPath.t option

(** Get nth label from module path. *)
val get_nth_label_mp : int -> ModPath.t -> Label.t

(** Get labels of reference. *)
val labels_of_ref : GlobRef.t -> ModPath.t * Label.t list

(** {2 Table-related operations} *)

(** For avoiding repeated extraction of the same constant or inductive, we use
    cache functions below. Indexing by constant name isn't enough, due to
    modules we could have a same constant name but different content. So we
    check that the [constant_body] hasn't changed from recording time to
    retrieving time. Same for inductive: we store [mutual_inductive_body] as
    checksum. In both case, we should ideally also check the env *)

(** Add type definition to cache. *)
val add_typedef : Constant.t -> constant_body -> ml_type -> unit

(** Lookup type definition from cache. *)
val lookup_typedef : Constant.t -> constant_body -> ml_type option

(** Add constant type schema to cache. *)
val add_cst_type : Constant.t -> constant_body -> ml_schema -> unit

(** Lookup constant type schema from cache. *)
val lookup_cst_type : Constant.t -> constant_body -> ml_schema option

(** Add inductive to cache. *)
val add_ind : MutInd.t -> mutual_inductive_body -> ml_ind -> unit

(** Lookup inductive from cache. *)
val lookup_ind : MutInd.t -> mutual_inductive_body -> ml_ind option

(** Get number of parameters for inductive if available. *)
val get_ind_nparams_opt : MutInd.t -> int option

(** Get number of parameter variables for inductive if available. *)
val get_ind_num_param_vars_opt : MutInd.t -> int option

(** Add inductive kind to table. *)
val add_inductive_kind : MutInd.t -> inductive_kind -> unit

(** Check if reference is coinductive. *)
val is_coinductive : GlobRef.t -> bool

(** Check if any coinductive types exist. *)
val has_any_coinductive : unit -> bool

(** Check if ML type is coinductive. *)
val is_coinductive_type : ml_type -> bool

(** Mark that string literals are needed. *)
val mark_needs_string_literals : unit -> unit

(** Check if string literals are needed. *)
val needs_string_literals : unit -> bool

(** Reset string literals flag. *)
val reset_needs_string_literals : unit -> unit

(** Get record fields for a reference (empty for non-record). *)
val get_record_fields : GlobRef.t -> GlobRef.t option list

(** Get record fields from ML type. *)
val record_fields_of_type : ml_type -> GlobRef.t option list

(** Get types of record fields. *)
val record_field_types : GlobRef.t -> ml_type list

(** Get inductive type parameter variables. *)
val get_ind_ip_vars : GlobRef.t -> Names.Id.t list

(** Get number of significant type parameters. *)
val get_ind_nb_sign_keeps : GlobRef.t -> int

(** Check if reference is a typeclass. *)
val is_typeclass : GlobRef.t -> bool

(** Check if ML type is a typeclass. *)
val is_typeclass_type : ml_type -> bool

(** Check if C++ type is a typeclass. *)
val is_typeclass_type_cpp : Minicpp.cpp_type -> bool

(** Mark inductive as enum. *)
val add_enum_inductive : GlobRef.t -> unit

(** Check if inductive is enum. *)
val is_enum_inductive : GlobRef.t -> bool

(** Check if an inductive packet qualifies as an enum based on its structure.
    Returns true if all constructors are nullary, no type parameters are kept,
    and at least one constructor exists. *)
val is_enum_inductive_packet : Miniml.ml_ind -> int -> bool

(** Sigma type assertion. *)
type sigma_assertion =
  | AssertExpr of string
  | AssertComment of string

(** Add sigma assertion for a field. *)
val add_sigma_assertion : GlobRef.t -> int -> sigma_assertion -> unit

(** Get all sigma assertions for a reference. *)
val get_sigma_assertions : GlobRef.t -> (int * sigma_assertion) list

(** Add recursors for mutual inductive. *)
val add_recursors : Environ.env -> MutInd.t -> unit

(** Check if reference is a recursor. *)
val is_recursor : GlobRef.t -> bool

(** Add projection to table. *)
val add_projection : int -> Constant.t -> inductive -> unit

(** Check if reference is a projection. *)
val is_projection : GlobRef.t -> bool

(** Get projection arity. *)
val projection_arity : GlobRef.t -> int

(** Get projection info (inductive and arity). *)
val projection_info : GlobRef.t -> inductive * int (* arity *)

(** Initialize higher-order projections table. *)
val init_higher_order_projections : unit -> unit

(** Mark reference as higher-order projection. *)
val mark_higher_order_projection : GlobRef.t -> unit

(** Check if reference is higher-order projection. *)
val is_higher_order_projection : GlobRef.t -> bool

(** Add promoted type variable. *)
val add_promoted_type_var : GlobRef.t -> Names.Id.t -> unit

(** Check if reference has promoted type variable. *)
val is_promoted_type_var : GlobRef.t -> bool

(** Get promoted type variable name if exists. *)
val promoted_type_var_name : GlobRef.t -> Names.Id.t option

(** Add instance promoted types. *)
val add_instance_promoted_types :
  GlobRef.t -> (Names.Id.t * Miniml.ml_type) list -> unit

(** Get instance promoted types. *)
val get_instance_promoted_types :
  GlobRef.t -> (Names.Id.t * Miniml.ml_type) list

(** Add info axiom. *)
val add_info_axiom : GlobRef.t -> unit

(** Remove info axiom. *)
val remove_info_axiom : GlobRef.t -> unit

(** Add log axiom. *)
val add_log_axiom : GlobRef.t -> unit

(** Add cofixpoint definition. *)
val add_cofixpoint : GlobRef.t -> unit

(** Check if a definition is a cofixpoint. *)
val is_cofixpoint : GlobRef.t -> bool

(** Add axiom value (non-function axiom generated as zero-arg function). *)
val add_axiom_value : GlobRef.t -> unit

(** Check if a definition is an axiom value. *)
val is_axiom_value : GlobRef.t -> bool

(** Add symbol. *)
val add_symbol : GlobRef.t -> unit

(** Add symbol rule. *)
val add_symbol_rule : GlobRef.t -> Label.t -> unit

(** Mark reference as opaque. *)
val add_opaque : GlobRef.t -> unit

(** Remove opaque marking from reference. *)
val remove_opaque : GlobRef.t -> unit

(** Reset all extraction tables. *)
val reset_tables : unit -> unit

(** {2 Output Directory parameter} *)

(** Get base output directory. *)
val output_directory : unit -> string

(** [output_directory_for_module ()] returns the output directory with the
    module's subdirectory appended, mirroring the source file's location.
    Creates the subdirectory if it doesn't exist. Falls back to base output
    directory on error. *)
val output_directory_for_module : unit -> string

(** {2 AccessOpaque parameter} *)

(** Check if accessing opaque definitions is enabled. *)
val access_opaque : unit -> bool

(** {2 AutoInline parameter} *)

(** Check if auto-inline is enabled. *)
val auto_inline : unit -> bool

(** {2 TypeExpand parameter} *)

(** Check if type expansion is enabled. *)
val type_expand : unit -> bool

(** {2 Optimize parameter} *)

(** Optimization flags. *)
type opt_flag = {
  opt_kill_dum : bool;  (** 1: Kill dummy arguments *)
  opt_fix_fun : bool;  (** 2: Optimize fixpoint functions *)
  opt_case_iot : bool;  (** 4: Case optimization - iota *)
  opt_case_idr : bool;  (** 8: Case optimization - identity *)
  opt_case_idg : bool;  (** 16: Case optimization - general identity *)
  opt_case_cst : bool;  (** 32: Case optimization - constant *)
  opt_case_fun : bool;  (** 64: Case optimization - function *)
  opt_case_app : bool;  (** 128: Case optimization - application *)
  opt_let_app : bool;  (** 256: Let-application optimization *)
  opt_lin_let : bool;  (** 512: Linear let optimization *)
  opt_lin_beta : bool;
}
(** 1024: Linear beta reduction *)

(** Get current optimization flags. *)
val optims : unit -> opt_flag

(** Get code formatting style. *)
val format_style : unit -> string

(** Get standard library path. *)
val std_lib : unit -> string

(** Get BDE directory path. *)
val bde_dir : unit -> string

(** {2 Controls whether dummy lambdas are removed} *)

(** Check if conservative types mode is enabled. *)
val conservative_types : unit -> bool

(** {2 File comment} *)

(** Get comment to print at the beginning of files. *)
val file_comment : unit -> string

(** {2 Target language} *)

(** Target language for extraction. *)
type lang = Cpp

(** Benchmark language variant. *)
type benchmark_lang =
  | BenchmarkOCaml
  | BenchmarkCpp

(** Get current target language. *)
val lang : unit -> lang

(** {2 Extraction modes}

    Extraction modes: modular or monolithic, library or minimal.

    Nota:
    - Recursive Extraction: monolithic, minimal
    - Separate Extraction: modular, minimal
    - Extraction Library: modular, library *)

(** Set modular extraction mode. *)
val set_modular : bool -> unit

(** Check if modular extraction is enabled. *)
val modular : unit -> bool

(** Set library extraction mode. *)
val set_library : bool -> unit

(** Check if library extraction is enabled. *)
val library : unit -> bool

(** Set extraction compute mode. *)
val set_extrcompute : bool -> unit

(** Check if extraction compute mode is enabled. *)
val is_extrcompute : unit -> bool

(** {2 Custom inlining table} *)

(** Check if reference should be inlined. *)
val to_inline : GlobRef.t -> bool

(** Check if reference should be kept (not inlined). *)
val to_keep : GlobRef.t -> bool

(** {2 Implicit arguments table} *)

(** Get set of implicit argument positions for global reference. *)
val implicits_of_global : GlobRef.t -> Int.Set.t

(** {2 Custom ML extractions table} *)

(** UGLY HACK: registration of a function defined in [extraction.ml] *)
val type_scheme_nb_args_hook : (Environ.env -> Constr.t -> int) Hook.t

(** Check if reference has custom extraction. *)
val is_custom : GlobRef.t -> bool

(** Check if reference has inline custom extraction. *)
val is_inline_custom : GlobRef.t -> bool

(** Check if reference has foreign custom extraction. *)
val is_foreign_custom : GlobRef.t -> bool

(** Find callback name for reference if any. *)
val find_callback : GlobRef.t -> string option

(** Find custom extraction code for reference. *)
val find_custom : GlobRef.t -> string

(** Find custom extraction code if exists. *)
val find_custom_opt : GlobRef.t -> string option

(** Find custom type extraction (imports and code). *)
val find_type_custom : GlobRef.t -> string list * string

(** Check if branch array has custom match extraction. *)
val is_custom_match : ml_branch array -> bool

(** Find custom match extraction code. *)
val find_custom_match : ml_branch array -> string

(** Check if reference is a monad. *)
val is_monad : GlobRef.t -> bool

(** Check if reference is a bind operation. *)
val is_bind : GlobRef.t -> bool

(** Check if reference is a return operation. *)
val is_ret : GlobRef.t -> bool

(** Check if reference is void type. *)
val is_void : GlobRef.t -> bool

(** Check if reference is ghost (erased). *)
val is_ghost : GlobRef.t -> bool

(** Check if reference has any kind of custom extraction. *)
val is_any_custom : GlobRef.t -> bool

(** Check if reference has any kind of inline custom extraction. *)
val is_any_inline_custom : GlobRef.t -> bool

(** Find type for reference. *)
val find_type : GlobRef.t -> ml_type

(** {2 Extraction commands} *)

(** Set extraction target language. *)
val extraction_language : lang -> unit

(** Configure inline/keep for qualified identifiers. *)
val extraction_inline : bool -> qualid list -> unit

(** Print current inline extraction table. *)
val print_extraction_inline : unit -> Pp.t

(** Print foreign extraction table. *)
val print_extraction_foreign : unit -> Pp.t

(** Print callback extraction table. *)
val print_extraction_callback : unit -> Pp.t

(** Reset inline extraction table. *)
val reset_extraction_inline : unit -> unit

(** Reset foreign extraction table. *)
val reset_extraction_foreign : unit -> unit

(** Reset callback extraction table. *)
val reset_extraction_callback : unit -> unit

(** Extract callback with optional name. *)
val extract_callback : string option -> qualid -> unit

(** Add custom import. *)
val add_custom_import : string -> unit

(** Get list of custom imports. *)
val get_custom_imports : unit -> string list

(** Mark custom extraction as used. *)
val mark_custom_used : GlobRef.t -> unit

(** Reset used custom imports tracking. *)
val reset_used_custom_imports : unit -> unit

(** Extract constant with inline custom code. *)
val extract_constant_inline : bool -> qualid -> string list -> string -> unit

(** Extract constant with import custom code. *)
val extract_constant_import :
  bool -> qualid -> string list -> string -> string list -> unit

(** Extract constant with foreign code. *)
val extract_constant_foreign : qualid -> string -> unit

(** Extract inductive with custom representation. *)
val extract_inductive :
  qualid -> string -> string list -> string option -> string list -> unit

(** Extract monad with bind and return operations. *)
val extract_monad : qualid -> qualid -> qualid -> string -> string list -> unit

(** Extract void type. *)
val extract_void : qualid -> qualid -> unit

(** Skip extraction for qualified identifier. *)
val extract_skip : qualid -> unit

(** Check if module should be skipped. *)
val is_skip_module : ModPath.t -> bool

(** Skip entire module extraction. *)
val extract_skip_module : qualid -> unit

(** Skip extraction or module (OR combinator). *)
val extract_skip_or_module : qualid -> unit

(** Numeral information for numeric inductives. *)
type numeral_info = {
  num_zero_ctor : int;  (** Index of zero constructor *)
  num_succ_ctor : int;  (** Index of successor constructor *)
  num_fmt : string;  (** Format string for numeral *)
}

(** Check if inductive is numeric. *)
val is_numeral_inductive : GlobRef.t -> bool

(** Get numeral information if available. *)
val get_numeral_info : GlobRef.t -> numeral_info option

(** Extract numeral inductive. *)
val extract_numeral : qualid -> string -> unit

(** Register global definition with type. *)
val register_glob_def : GlobRef.t -> ml_type -> unit

(** Argument specifier for implicit extraction. *)
type int_or_id =
  | ArgInt of int
  | ArgId of Id.t

(** Configure implicit arguments for extraction. *)
val extraction_implicit : qualid -> int_or_id list -> unit

(** {2 Blacklisted filenames table} *)

(** Add filenames to blacklist. *)
val extraction_blacklist : string list -> unit

(** Reset filename blacklist. *)
val reset_extraction_blacklist : unit -> unit

(** Print current blacklist. *)
val print_extraction_blacklist : unit -> Pp.t
