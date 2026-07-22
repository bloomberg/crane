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

(** Issue warning about opaques.
    @param accessed [true] if opaque bodies were accessed (bypass-opacity mode),
                    [false] if they were extracted as axioms (default mode). *)
val warning_opaques : bool -> unit

(** Issue warning about ambiguous name.
    @param loc    optional source location for quickfix attachment
    @param (q, mp, r) the ambiguous qualid, the module path it may refer to,
                       and the global reference it may refer to *)
val warning_ambiguous_name :
  ?loc:Loc.t -> qualid * ModPath.t * GlobRef.t -> unit

(** Issue warning about identifier. *)
val warning_id : string -> unit

(** Report error for axiom scheme.
    @param loc optional source location
    @param r   the axiom global reference
    @param i   the required number of type variables *)
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

(** Report error for non-visible reference. *)
val error_not_visible : GlobRef.t -> 'a

(** Report error for MPfile used as module.
    @param mp the module file path being extracted
    @param b  [true] if the module was explicitly asked for (extraction
              directive), [false] if it was pulled in as a dependency *)
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

(** Check if kernel name occurs in reference.
    @param kn the mutual inductive name to search for
    @param r  the global reference to inspect (only [IndRef]/[ConstructRef] can match)
    @return [true] iff [r] is an inductive or constructor of [kn] *)
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


(** Get file name from module file. Escapes C standard header collisions. *)
val file_of_modfile : ModPath.t -> string

(** Get namespace name from module file. No filename escaping applied. *)
val ns_of_modfile : ModPath.t -> string

(** Check if module path is toplevel. *)
val is_toplevel : ModPath.t -> bool

(** Check if at toplevel. *)
val at_toplevel : ModPath.t -> bool

(** Get length of module path. *)
val mp_length : ModPath.t -> int

(** Get all prefixes of module path. *)
val prefixes_mp : ModPath.t -> MPset.t

(** Find common prefix from list of module paths.
    @param mp0 the reference module path whose prefixes are candidates
    @param mpl a list of module paths; the first one that is also a prefix of
               [mp0] is returned
    @return the first element of [mpl] that is a prefix of [mp0], or [None] *)
val common_prefix_from_list : ModPath.t -> ModPath.t list -> ModPath.t option

(** Get nth label from module path.
    @param n  1-based index counting from the innermost [MPdot] label outward
    @param mp the module path to index into *)
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

(** Add type definition to cache.
    @param kn the constant being cached
    @param cb the constant body used as a checksum to detect stale entries
    @param t  the extracted ML type to store *)
val add_typedef : Constant.t -> constant_body -> ml_type -> unit

(** Lookup type definition from cache.
    @param kn the constant to look up
    @param cb the current constant body; [None] is returned if this doesn't
              match the body stored when the entry was created
    @return [Some t] if found and the checksum matches, [None] otherwise *)
val lookup_typedef : Constant.t -> constant_body -> ml_type option

(** Lookup type definition without checksum validation.
    @return [Some t] if any entry for [kn] exists, regardless of staleness *)
val lookup_typedef_unchecked : Constant.t -> ml_type option

(** Add constant type schema to cache.
    @param kn the constant being cached
    @param cb the constant body used as a checksum to detect stale entries
    @param s  the extracted ML type schema to store *)
val add_cst_type : Constant.t -> constant_body -> ml_schema -> unit

(** Lookup constant type schema from cache.
    @param kn the constant to look up
    @param cb the current constant body; [None] is returned on checksum mismatch
    @return [Some s] if found and the checksum matches, [None] otherwise *)
val lookup_cst_type : Constant.t -> constant_body -> ml_schema option

(** Add inductive to cache.
    @param kn    the mutual inductive name being cached
    @param mib   the inductive body used as a checksum to detect stale entries
    @param ml_ind the extracted ML inductive to store *)
val add_ind : MutInd.t -> mutual_inductive_body -> ml_ind -> unit

(** Lookup inductive from cache.
    @param kn  the mutual inductive name to look up
    @param mib the current inductive body; [None] is returned on checksum mismatch
    @return [Some ind] if found and the checksum matches, [None] otherwise *)
val lookup_ind : MutInd.t -> mutual_inductive_body -> ml_ind option

(** Get number of parameters for inductive if available. *)
val get_ind_nparams_opt : MutInd.t -> int option

(** Get number of parameter variables for inductive if available. *)
val get_ind_num_param_vars_opt : MutInd.t -> int option

(** Compute the kept type-variable names among an inductive packet's
    PARAMETER positions only (the first [ind_nparams] entries of [ip_sign]),
    excluding type INDICES.  Used to distinguish a scheme's own parameters
    (e.g. [List (A:Type)]) from indices it is applied to (e.g. the [A] in
    [wrap : Set -> Type]), which are not template-representable in C++.
    @param ind the inductive body
    @param p the packet (one constructor group) to compute parameter vars for
    @return the kept parameter variable names, and their count *)
val ind_param_vars :
  Miniml.ml_ind -> Miniml.ml_ind_packet -> Names.Id.t list * int

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

(** Mark that the [crane_erase_fn] runtime helper must be emitted. *)
val mark_needs_erase_fn : unit -> unit

(** Check whether the [crane_erase_fn] runtime helper is needed. *)
val needs_erase_fn : unit -> bool

(** Reset the [crane_erase_fn] flag. *)
val reset_needs_erase_fn : unit -> unit

(** Mark that [crane_itree.h] is needed (reified ITree types in output). *)
val require_itree_header : unit -> unit

(** Check whether [crane_itree.h] is needed. *)
val needs_itree_header : unit -> bool

(** Reset the itree header flag (between extraction units). *)
val reset_itree_header : unit -> unit

(** Record a [main] function for wrapper generation.
    @param name       the renamed function name (e.g. [_main])
    @param ret_type   the ML return type
    @param struct_opt enclosing struct qualifier, if any
    @param needs_run  true if the return type is a reified ITree
                      (needs [->run()]), false if the monad was erased *)
val set_main_function : Id.t -> ml_type -> Id.t option -> bool -> unit

(** Return the recorded main function, if any:
    [(name, return_type, struct_qualifier, needs_run)]. *)
val get_main_function : unit -> (Id.t * ml_type * Id.t option * bool) option

(** Reset main function tracking (between extraction units). *)
val reset_main_function : unit -> unit

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

(** Get the ML field types for a constructor, as stored in [ip_types].
    Returns [None] if the inductive is not in the extraction table.
    The list order matches the constructor argument order. *)
val get_ctor_ip_types_opt : GlobRef.t -> Miniml.ml_type list option

(** Get the number of C++ parameter type variables for the inductive
    containing the given constructor.  Only [Keep] entries in the PARAMETER
    portion of [ip_sign] (first [ind_nparams] positions) are counted —
    type indices are excluded.  Mirrors the [param_vars] computation in
    [gen_ind_header_v2].  Returns 0 on lookup failure. *)
val get_ctor_num_param_vars : GlobRef.t -> int

(** Check if reference is a typeclass. *)
val is_typeclass : GlobRef.t -> bool

(** Check if ML type is a typeclass. *)
val is_typeclass_type : ml_type -> bool

(** Check if C++ type is a typeclass. *)
val is_typeclass_type_cpp : Minicpp.cpp_type -> bool

(** Mark inductive as flat (single-ctor, no variant wrapper). *)
val add_flat_inductive : GlobRef.t -> unit

(** Check if inductive is flat. *)
val is_flat_inductive : GlobRef.t -> bool

(** Mark inductive as enum. *)
val add_enum_inductive : GlobRef.t -> unit

(** Check if inductive is enum. *)
val is_enum_inductive : GlobRef.t -> bool

(** Check if the inductive has any constructor field whose type refers
    back to the same MutInd (recursive self-reference).  Such inductives
    store self-refs as [shared_ptr] internally. *)
val has_recursive_fields : GlobRef.t -> bool

(** Check whether an inductive type has dependent parameters — i.e., the type
    of some parameter references an earlier parameter (via de Bruijn index). *)
val has_dependent_params : GlobRef.t -> bool

(** Check if an inductive packet qualifies as an enum based on its structure.
    Returns true if all constructors are nullary, no type parameters are kept,
    and at least one constructor exists.
    @param ind the extracted ML inductive (contains all packets)
    @param i   0-based index of the packet within [ind] to test *)
val is_enum_inductive_packet : Miniml.ml_ind -> int -> bool

(** Check if an inductive packet qualifies as flat (single constructor, no kept
    type parameters, not coinductive, not mutual, no self-referencing fields).
    Mirrors the [is_flat] check in [gen_ind_header_v2]. *)
val is_flat_inductive_packet : Names.MutInd.t -> Miniml.ml_ind -> int -> bool

(** Compute the C++ enum constructor name for constructor [j] of inductive
    [(kn, i)] by looking up the extraction packet. Deterministic regardless
    of the KerName used (canonical or functor-applied).
    @param kn the mutual inductive kernel name
    @param i  0-based packet index within the mutual inductive
    @param j  1-based constructor index within the packet
    @return the C++ enum enumerator name (e.g. [e_ZERO]) *)
val enum_ctor_name_of_ref : MutInd.t -> int -> int -> string

(** Sigma type assertion. *)
type sigma_assertion =
  | AssertExpr of string
  | AssertComment of string

(** Add sigma assertion for a field.
    @param r   the function global reference the assertion belongs to
    @param idx 0-based parameter index the assertion is attached to
    @param a   the assertion to record *)
val add_sigma_assertion : GlobRef.t -> int -> sigma_assertion -> unit

(** Get all sigma assertions for a reference. *)
val get_sigma_assertions : GlobRef.t -> (int * sigma_assertion) list

(** Add recursors for mutual inductive.
    @param env the global environment used to look up the inductive body
    @param ind the mutual inductive whose [_rec]/[_rect] recursors to register *)
val add_recursors : Environ.env -> MutInd.t -> unit

(** Check if reference is a recursor. *)
val is_recursor : GlobRef.t -> bool

(** Add projection to table.
    @param n    the arity (number of type parameters) of the projection
    @param kn   the constant representing the projection function
    @param ip   the inductive type the projection belongs to *)
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

(** Record phantom type variable indices for a function. Phantom tvars are
    template type parameters that C++ cannot deduce from non-function value
    parameters. They are removed from the template param list and replaced
    with [auto] in the generated definition. Call sites must drop the
    corresponding type arguments. Indices are 1-based (matching Tvar indexing). *)
val set_phantom_tvars : GlobRef.t -> int list -> unit

(** Get phantom type variable indices for a function (empty if none). *)
val get_phantom_tvars : GlobRef.t -> int list

(** Add promoted type variable. *)
val add_promoted_type_var : GlobRef.t -> Names.Id.t -> unit

(** Check if reference has promoted type variable. *)
val is_promoted_type_var : GlobRef.t -> bool

(** Get promoted type variable name if exists. *)
val promoted_type_var_name : GlobRef.t -> Names.Id.t option

(** Register an erased type constant (non-promoted type-valued record field). *)
val add_erased_type_const : GlobRef.t -> unit

(** Check if reference is an erased type constant. *)
val is_erased_type_const : GlobRef.t -> bool

(** Register a value-dependent type scheme (kind takes a value argument, e.g.
    [sym_semty : sym -> Type]).  Applied to a value it erases to [std::any]. *)
val add_value_dep_type_scheme : GlobRef.t -> unit

(** Check whether a reference is a value-dependent type scheme. *)
val is_value_dep_type_scheme : GlobRef.t -> bool

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

(** [validate_output_target target] rejects a user-supplied extraction target
    filename that could escape the output directory. Absolute paths and [..]
    components raise a Rocq user error; ordinary relative subpaths are accepted.
    Guards against path traversal / arbitrary file write (CWE-22/CWE-73). *)
val validate_output_target : string -> unit

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

(** {2 Loopify pass} *)

(** Check if the loopify pass is enabled (recursive → iterative transformation).
*)
val loopify : unit -> bool

(** Check whether a specific function should be loopified (per-function override
    first, then global setting). *)
val should_loopify : GlobRef.t -> bool

(** Mark references for loopify (true) or noloopify (false).
    @param b [true] to force loopification of the listed functions,
             [false] to opt them out (override the global [Crane Loopify] setting)
    @param l list of qualified identifiers to configure *)
val extraction_loopify : bool -> qualid list -> unit

(** Reset per-function loopify table. *)
val reset_extraction_loopify : unit -> unit

(** {2 File comment} *)

(** Get comment to print at the beginning of files. *)
val file_comment : unit -> string

(** {2 Target language} *)

(** Target language for extraction. *)
type lang = Cpp

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

(** True when [s] names a C++ scalar type that is trivially copyable
    (integers, floats, char variants, fixed-width aliases, [std::nullptr_t]). *)
val is_trivially_copyable_cpp_name : string -> bool

(** True when [r] is a custom-extracted inductive whose C++ representation is
    a trivially-copyable scalar (e.g. [nat] → [unsigned int]). *)
val is_custom_scalar_ref : GlobRef.t -> bool

(** Append [_] to struct names that collide with C++ global names
    (e.g. [std], [crane], [persistent_array]). *)
val escape_reserved_struct_name : string -> string

(** Find custom type extraction (imports and code). *)
val find_type_custom : GlobRef.t -> string list * string

(** Check if branch array has custom match extraction. *)
val is_custom_match : ml_branch array -> bool

(** Find custom match extraction code. *)
val find_custom_match : ml_branch array -> string

(** Look up the match template for an inductive directly by GlobRef. *)
val find_custom_match_by_ref : GlobRef.t -> string option

(** Structured accessor for projecting a field from a value of a custom type. *)
type accessor = AccMember of string | AccDeref

(** For single-constructor custom types, return the accessor for each type-arg
    binding, derived from the match template.  Returns [None] for multi-branch
    types or when the template structure is not recognized. *)
val find_custom_accessors : GlobRef.t -> accessor list option

(** Get the constructor template strings for an inductive, in constructor order. *)
val find_custom_ctor_templates : Names.inductive -> string list

(** Get the header import list registered for a GlobRef via [From] declarations. *)
val get_ref_import_list : GlobRef.t -> string list

(** Check if reference is a monad. *)
val is_monad : GlobRef.t -> bool

(** Check if reference is a bind operation. *)
val is_bind : GlobRef.t -> bool

(** Check if reference is a return operation. *)
val is_ret : GlobRef.t -> bool

(** Get monad template string if reference is a registered monad. *)
val get_monad_template_opt : GlobRef.t -> string option

(** Check if reference is void type. *)
val is_void : GlobRef.t -> bool

(** Check if reference is ghost (erased). *)
val is_ghost : GlobRef.t -> bool

(** Check if reference is Rocq's [unit] type. *)
val is_unit_type : GlobRef.t -> bool

(** Check if reference is Rocq's [tt] constructor. *)
val is_tt_constructor : GlobRef.t -> bool

(** Resolve the GlobRef for Rocq's [unit] type. *)
val resolve_unit_type : unit -> GlobRef.t option

(** Resolve the GlobRef for Rocq's [tt] constructor. *)
val resolve_tt_ctor : unit -> GlobRef.t option

(** Check if reference has any kind of custom extraction. *)
val is_any_custom : GlobRef.t -> bool

(** Check if reference has any kind of inline custom extraction. *)
val is_any_inline_custom : GlobRef.t -> bool

(** Find type for reference. *)
val find_type : GlobRef.t -> ml_type

(** {2 Extraction commands} *)

(** Set extraction target language. *)
val extraction_language : lang -> unit

(** Configure inline/keep for qualified identifiers.
    @param b  [true] to mark the identifiers for inlining, [false] to mark
              them as NoInline (keep)
    @param l  the list of qualified identifiers to configure *)
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

(** Extract callback with optional name.
    @param optstr optional alias string to use instead of the default name
    @param x      the qualified identifier of the function to register as a callback *)
val extract_callback : string option -> qualid -> unit

(** Get list of custom imports. *)
val get_custom_imports : unit -> string list

(** Mark custom extraction as used. *)
val mark_custom_used : GlobRef.t -> unit

(** Reset used custom imports tracking. *)
val reset_used_custom_imports : unit -> unit

(** Extract constant with inline custom code.
    @param inline [true] to mark the constant as Inline (inlined at call sites),
                  [false] for NoInline
    @param r      the qualified identifier of the constant to extract
    @param ids    type parameter names for type-scheme axioms (usually [[]])
    @param s      the C++ replacement expression or type string *)
val extract_constant_inline : bool -> qualid -> string list -> string -> unit

(** Extract constant with import custom code.
    @param inline  [true] to mark as Inline, [false] for NoInline
    @param r       the qualified identifier of the constant to extract
    @param ids     type parameter names for type-scheme axioms (usually [[]])
    @param s       the C++ replacement expression or type string
    @param imports list of C++ headers to [#include] when this constant is used *)
val extract_constant_import :
  bool -> qualid -> string list -> string -> string list -> unit

(** Extract constant with foreign code.
    @param r the qualified identifier of the constant (must be a function)
    @param s the C++ foreign function name to call at extraction sites *)
val extract_constant_foreign : qualid -> string -> unit

(** Extract inductive with custom representation.
    @param r       the qualified identifier of the inductive type
    @param s       the C++ type name replacing the inductive
    @param l       list of C++ constructor representation strings, one per
                   constructor (length must match the number of constructors)
    @param optstr  optional C++ match template string for custom pattern matching
    @param imports list of C++ headers to [#include] when this type is used *)
val extract_inductive :
  qualid -> string -> string list -> string option -> string list -> unit

(** Extract monad with bind and return operations.
    @param m       the qualified identifier of the monad type constructor
    @param b       the qualified identifier of the bind operation
    @param r       the qualified identifier of the return operation
    @param s       the C++ template string for the monad type
    @param imports list of C++ headers to [#include] when this monad is used *)
val extract_monad : qualid -> qualid -> qualid -> string -> string list -> unit

(** Extract void type.
    @param v the qualified identifier of the void type (maps to [void] in C++)
    @param g the qualified identifier of the ghost term (the single constructor,
             erased to nothing at call sites) *)
val extract_void : qualid -> qualid -> unit

(** Register a pointer-equality guard for a comparison function.
    [Crane Guard Compare f => Eq] inserts [if (&p1 == &p2) return Eq;]
    at the top of [f], where [p1] and [p2] are the first two [const T&]
    parameters of the same type. *)
val extract_guard_compare : qualid -> qualid -> unit

(** Look up the guard-compare return constructor for a function, if any. *)
val find_guard_compare : GlobRef.t -> GlobRef.t option

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
  num_converters : GlobRef.t list;
    (** Converter functions (e.g. [Nat.of_num_uint]) that parse digit chains
        into this numeral type.  Resolved automatically from the inductive's
        module when [Crane Extract Numeral] is processed. *)
}

(** Check if inductive is numeric. *)
val is_numeral_inductive : GlobRef.t -> bool

(** Get numeral information if available. *)
val get_numeral_info : GlobRef.t -> numeral_info option

(** Check if a function is a registered numeral converter (e.g.
    [Nat.of_num_uint]).  These are resolved from the same module as the
    numeral inductive during [Crane Extract Numeral] processing. *)
val is_numeral_converter : GlobRef.t -> bool

(** Return the numeral inductive targeted by a converter function, if any. *)
val numeral_ind_of_converter : GlobRef.t -> GlobRef.t option

(** Extract numeral inductive.
    @param r   the qualified identifier of the inductive type (e.g. [nat])
    @param fmt the C++ format string for numeral literals (e.g. ["%nu"]) *)
val extract_numeral : qualid -> string -> unit

(** Register global definition with type.
    @param id the global reference of the definition being registered
    @param ty the ML type to associate with it, used for type-directed
              code generation at call sites *)
val register_glob_def : GlobRef.t -> ml_type -> unit

(** Argument specifier for implicit extraction. *)
type int_or_id =
  | ArgInt of int
  | ArgId of Id.t

(** Configure implicit arguments for extraction.
    @param r the qualified identifier of the function
    @param l list of argument specifiers (by position [ArgInt] or name [ArgId])
             indicating which arguments should be treated as implicit and dropped
             during extraction *)
val extraction_implicit : qualid -> int_or_id list -> unit

(** {2 Blacklisted filenames table} *)

(** Add filenames to blacklist. *)
val extraction_blacklist : string list -> unit

(** Reset filename blacklist. *)
val reset_extraction_blacklist : unit -> unit

(** Print current blacklist. *)
val print_extraction_blacklist : unit -> Pp.t

(** Inductives promoted into their own namespace struct (e.g. String.string →
    [namespace String { struct String }]).  Lives here to break the
    Translation ↔ Cpp_state cycle. *)
val promoted_inductives : (GlobRef.t, unit) Hashtbl.t
