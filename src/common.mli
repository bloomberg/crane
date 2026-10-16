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

(** Pretty-printing utilities, name resolution, and renaming for extracted code.
*)

open Names
open Miniml

(** {2 Generic utility functions (string, list)} *)

(** [globref_equal r1 r2] tests equality of two global references. *)
val globref_equal : Names.GlobRef.t -> Names.GlobRef.t -> bool

(** [contains_substring haystack needle] checks if [haystack] contains [needle].
*)
val contains_substring : string -> string -> bool

(** Whether a module path lies inside a functor's parameter. *)
val under_mp_bound : Names.ModPath.t -> bool

(** [render_template substs tmpl] replaces each [(placeholder, value)] pair
    in [substs] within [tmpl].  Used for numeric literal formatting templates. *)
val render_template : (string * string) list -> string -> string

(** [last lst] returns the last element of a non-empty list.
    @raise Failure if the list is empty. *)
val last : 'a list -> 'a

(** [last_two lst] returns the last two elements of a list.
    @raise Failure if the list has fewer than two elements. *)
val last_two : 'a list -> 'a * 'a

(** [extract_at_pos pos lst] extracts the element at position [pos] from [lst].
    Returns (Some element, remaining_list) or (None, original_list). *)
val extract_at_pos : int -> 'a list -> 'a option * 'a list

(** [intersperse sep lst] inserts [sep] between each element of [lst]. *)
val intersperse : 'a -> 'a list -> 'a list

(** [prepend_to_all sep lst] prepends [sep] before each element of [lst]. *)
val prepend_to_all : 'a -> 'a list -> 'a list

(** By default, in module Format, you can do horizontal placing of blocks even
    if they include newlines, as long as the number of chars in the blocks are
    less that a line length. To avoid this awkward situation, we attach a big
    virtual size to [fnl] newlines. *)

(** Forced newline. *)
val fnl : unit -> Pp.t

(** Two consecutive newlines. *)
val fnl2 : unit -> Pp.t

(** Space if true, empty otherwise. *)
val space_if : bool -> Pp.t

(** Wrap in parentheses if the boolean is true. *)
val pp_par : bool -> Pp.t -> Pp.t

(** [pp_apply] : a head part applied to arguments, possibly with parenthesis *)
val pp_apply : Pp.t -> bool -> Pp.t list -> Pp.t

(** Like [pp_apply] but for C++ function call syntax (no space before parens,
    comma-separated arguments). *)
val pp_apply_cpp : Pp.t -> Pp.t list -> Pp.t

(** Print elements as a comma-separated tuple with parens. *)
val pp_tuple : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as comma-separated list without parens. *)
val pp_list : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as comma-separated list with newlines between. *)
val pp_list_newline : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as newline-separated statements. *)
val pp_list_stmt : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as a boxed tuple with line-break hints. *)
val pp_boxed_tuple : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print a list of identifiers as space-separated bindings. *)
val pr_binding : Id.t list -> Pp.t

(** Find a fresh name for [id] by incrementing subscript until no collision. *)
val rename_id : Id.t -> Id.Set.t -> Id.t

(** {2 de Bruijn environments} *)

(** de Bruijn environment: names in scope and set of avoided names. *)
type env = Id.t list * Id.Set.t

(** A fresh de Bruijn environment avoiding the global names: those planning
    decided once {!freeze_global_ids} has run, the current ones before. *)
val empty_env : unit -> env

(** Fix the global names every later {!empty_env} avoids at the ones decided
    so far.  Called where planning ends, before any body is generated. *)
val freeze_global_ids : unit -> unit

(** Prefix of the names Crane introduces itself, which no Rocq identifier is
    spelled with in C++. *)
val crane_local_prefix : string

(** The C++ spelling of a Rocq identifier, as an [Id.t]. *)
val cpp_id_of_id : Id.t -> Id.t

(** Rename a list of variables to fresh lowercase names. *)
val rename_vars : Id.Set.t -> Id.t list -> env

(** Rename type variables to fresh lowercase names. *)
val rename_tvars : Id.Set.t -> Id.t list -> Id.t list

(** Push new variable names into the de Bruijn environment. *)
val push_vars : Id.t list -> env -> Id.t list * env

(** Like {!push_vars} but for typed variable pairs. *)
val push_vars' : (Id.t * ml_type) list -> env -> (Id.t * ml_type) list * env

(** Look up a de Bruijn index in the environment. *)
val get_db_name : int -> env -> Id.t

(** Look up a de Bruijn index in the environment, or [None] when it names no
    binder there.  Indices out of the current scope do occur; prefer this to
    catching the exception {!get_db_name} raises. *)
val get_db_name_opt : int -> env -> Names.Id.t option

(** {2 Extraction phases and renaming} *)

(** Which file an emission pass is writing. *)
type file =
  | Impl  (** the [.cpp] *)
  | Intf  (** the [.h] *)

(** What a pass is for.  {!Plan} decides, before anything is rendered: the
    names of what a unit declares and refers to, its layout, its callables.
    An {!Emit} pass renders one file and reads those decisions.  Beyond its
    text it may only demand -- the headers its body includes -- and generate
    the helpers it lifts out of the bodies it translates, which are named as
    they are lifted; {!names_decided_while_emitting} is how that is checked. *)
type phase =
  | Plan
  | Emit of file

(** Set the current extraction phase. *)
val set_phase : phase -> unit

(** Get the current extraction phase. *)
val get_phase : unit -> phase

(** How diagnostics name a phase: [planning], [implementation], [header]. *)
val phase_name : phase -> string

(** The files whose namespace a rendered name was written through, whose
    headers the unit includes. *)
val opened_libraries : unit -> ModPath.t list

(** Activate separate-extraction naming: every cross-file reference is spelled
    in full, and the last component of a qualified type name is capitalized to
    match the C++ struct name ([Datatypes::List]).  Cleared automatically on
    reset. *)
val set_force_cross_file_qualification : unit -> unit

(** Whether separate-extraction naming is active. *)
val get_force_cross_file_qualification : unit -> bool

(** Record which module paths belong to the current extraction output.
    References to any other module path will be treated as external by
    {!is_non_output_module}; replaces any previously recorded set. *)
val set_non_output_modules : Names.ModPath.t list -> unit

(** [true] iff [mp] is known but not part of the current extraction output —
    i.e., its definition will live in a different generated file. *)
val is_non_output_module : Names.ModPath.t -> bool

(** Clear the set of non-output module paths recorded by
    {!set_non_output_modules}. *)
val clear_non_output_modules : unit -> unit

type kind =
  | Term
  | Type
  | Cons
  | Mod  (** Kind of global identifier: term, type, constructor, or module. *)

(** Kernel [Label.t] of a global reference: the constant's own label for a
    [ConstRef], and the enclosing mutual-inductive block's label for an
    [IndRef] or [ConstructRef]. *)
val label_of_r : GlobRef.t -> Label.t

(** Escape a Rocq identifier into one C++ accepts: suffix reserved keywords
    with [_], and replace primes with [_].  Names that reach C++ without
    passing through the reference tables (module-type labels, for instance)
    must still be run through this. *)
val modular_rename : kind -> Id.t -> string

(** Print a reference using a specific kernel name key. *)
val pp_global_with_key : kind -> KerName.t -> GlobRef.t -> string

(** Print a reference using its canonical kernel name. Has side effects on the
    renaming tables. *)
val pp_global : kind -> GlobRef.t -> string

(** Emit the file [mp] under the namespace [ns] rather than its own name, in
    its declaration and in every reference to it.  Must be decided before any
    file is rendered. *)
val rename_file_namespace : ModPath.t -> string -> unit

(** The name of the file defining a reference, when a reference to it from the
    current scope must name it; for a name hoisted to its file's namespace. *)
val file_qualifier : kind -> GlobRef.t -> string option

(** Print just the short name of a reference (for declarations). *)
val pp_global_name : kind -> GlobRef.t -> string

(** The short name already decided for a reference, if any.  Unlike
    {!pp_global_name} it decides nothing and demands nothing: it is how a
    check reads a plan back. *)
val decided_global_name : GlobRef.t -> string option

type decided_name =
  | Global_name of GlobRef.t
  | Module_name of ModPath.t

(** The names of globals and modules an emission pass of the current unit
    decided, rather than read from the plan, in the order it decided them.
    A functor parameter's, which is its own name, is not among them. *)
val names_decided_while_emitting : unit -> decided_name list

(** {!pp_global_name} as an [Id.t]: the short C++ name a reference is emitted
    under, for the many places that need it as an identifier rather than a
    string (a struct field, a method, a [using] alias). *)
val id_of_global : kind -> GlobRef.t -> Id.t

(** Print the type name for an eponymous record reference.  Returns the
    enclosing module name for consistent struct/type naming. *)
val pp_type_name_capitalized : GlobRef.t -> string

(** Print a module path. *)
val pp_module : ModPath.t -> string

(** The C++ name of a module label, as {!modular_rename} spells it. *)
val module_label_name : Label.t -> string

(** Pre-scan the structure for module/inductive name collisions.  When a module
    has the same C++ name as an inductive type that is either its sibling or
    declared inside it, the module is renamed with a ["_Mod"] suffix.
    Must be called before any [pp_global] or [pp_module] calls. *)
val detect_sibling_module_inductive_collisions : ml_structure -> unit

(** The name a module's C++ struct is emitted under, including any suffix
    {!detect_sibling_module_inductive_collisions} gave it. *)
val emitted_module_name : ModPath.t -> string

(** {!emitted_module_name} if already decided, deciding and demanding
    nothing, as {!decided_global_name}. *)
val decided_module_name : ModPath.t -> string option

(** The members every inductive's C++ struct declares for itself (the variant
    alias, its accessors, the deep copy).  Whatever else is emitted inside that
    struct has to keep clear of these names. *)
val inductive_generated_members : Id.Set.t

(** Record that [r] is emitted as a member of the struct of inductive [ind], so
    that its C++ name avoids {!inductive_generated_members} and [ind]'s factory
    methods.  Must be called before any [pp_global] for [r]. *)
val reserve_methodified : ind:GlobRef.t -> GlobRef.t -> unit

(** Get module paths of all visible layers. *)
val get_visible_mps : unit -> ModPath.t list

(** Get the module path of the innermost visible layer. *)
val top_visible_mp : unit -> ModPath.t

(** Push a module onto the visibility stack. The [module_path list] corresponds
    to module parameters, the innermost one coming first in the list.
    [members] are the C++ names the module's scope declares: an outer name
    they hide is qualified, even in a body printed ahead of their
    declarations. *)
val push_visible : ?members:Id.Set.t -> ModPath.t -> ModPath.t list -> unit

(** Pop the innermost visible layer. *)
val pop_visible : unit -> unit

(** The C++ names a structure declares as members of its struct, as
    {!push_visible} takes them. *)
val member_names_of_sel : Miniml.ml_module_structure -> Id.Set.t

(** A snapshot of the visibility stack: the scope a name is spelled from. *)
type visibility

val current_visibility : unit -> visibility

(** [with_visibility v f] runs [f] with the visibility stack at [v], restoring
    the stack as it was however [f] leaves. *)
val with_visibility : visibility -> (unit -> 'a) -> 'a

(** Global scope: no layer visible. *)
val global_visibility : visibility

(** [inside ?members mp params v] is [v] with [mp]'s scope innermost, as
    {!push_visible} would make it. *)
val inside : ?members:Id.Set.t -> ModPath.t -> ModPath.t list -> visibility -> visibility

(** The visibility enclosing the innermost scope of [v]. *)
val enclosing_visibility : visibility -> visibility

val equal_visibility : visibility -> visibility -> bool

(** The scopes of a visibility, innermost first, for a diagnostic. *)
val pp_visibility : visibility -> Pp.t

(** A name as name resolution settled it, before it is flattened to text: the
    qualifier components that reach it, outermost first.  Callers that need to
    know how a name came out should ask here rather than inspect the printed
    string. *)
type resolved = {rn_parts : string list}

(** The resolved name as text. *)
val resolved_string : resolved -> string

(** Whether the resolved name comes out carrying a [::] qualifier. *)
val resolved_is_qualified : resolved -> bool

(** The resolved name split at its last [::], as (qualifier, final component).
    [None] when the name comes out unqualified. *)
val resolved_split : resolved -> (string * string) option

(** Resolve a module path to its name, as the visible scopes qualify it;
    {!pp_module} is this plus {!resolved_string}. *)
val resolve_module : Names.ModPath.t -> resolved

(** {2 Resolution in an explicit scope}

    Each of these is a function of the visibility it is given and the naming
    tables, so it answers the same wherever it is asked; the printer's
    {!pp_global_with_key}, {!resolve_module} and {!file_qualifier} are these
    at the visibility it is writing in. *)

(** The name of a reference written where the visibility is. *)
val resolve_global : visibility -> kind -> KerName.t -> GlobRef.t -> string

(** The name of a module written where the visibility is. *)
val resolve_module_in : visibility -> ModPath.t -> resolved

(** {!file_qualifier} where the visibility is. *)
val resolve_file_qualifier : visibility -> kind -> GlobRef.t -> string option

(** Reset all renaming tables. *)
val reset_renaming_tables : unit -> unit

(** Set the set of reserved keywords for the target language. *)
val set_keywords : Id.Set.t -> unit

(** Whether [mp] is emitted as a C++ struct, and so is a scope a name can be
    qualified by.  The extraction root is not one: its members go to global
    scope, where they are spelled bare. *)
val is_struct_module : ModPath.t -> bool

(** Get the set of reserved keywords for the target language. *)
val get_keywords : unit -> Id.Set.t

(** Whether C++ refuses [s] as a name of Crane's choosing: a keyword, a name
    the runtime headers already own, or a macro the preprocessor would expand.
    Ask this of the spelling about to be emitted; each case-form of a name is a
    different name to the preprocessor. *)
val is_reserved_cpp_name : string -> bool

(** Set the names reserved only where a declaration reaches global scope. *)
val set_global_scope_keywords : Id.Set.t -> unit

(** Whether C++ refuses [s] as the name of a declaration emitted at global
    scope, because a C or POSIX library header already declares something else
    under it.  A name inside a namespace or struct is asked
    {!is_reserved_cpp_name} instead. *)
val is_reserved_at_global_scope : string -> bool

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then the constants are
    directly turned into chars *)

(** Check whether an ML term is an [ascii] constructor application that can be
    decoded into a native C++ [char] literal. *)
val is_native_char : ml_ast -> bool

(** Decode an [ascii] constructor application into a native [char] value. *)
val get_native_char : ml_ast -> char

(** Pretty-print an ascii constructor as a C++ char literal. *)
val pp_native_char : ml_ast -> Pp.t

(** Special hack for constants of type String.string : if an
    [Extract Inductive string => string] has been declared, then the constants
    are directly turned into string literals *)

(** Check whether an ML term is a fully statically-known [string] built from
    [EmptyString]/[String] constructors with constant [ascii] characters, that
    can be turned into a native C++ string literal. *)
val is_native_string : ml_ast -> bool

(** Extract the underlying OCaml string from a statically-known [string]
    term (see {!is_native_string}). *)
val get_native_string : ml_ast -> string

(** Pretty-print a statically-known [string] term as a C++ string literal. *)
val pp_native_string : ml_ast -> Pp.t

(** Registered name for the sig type (used for existential type extraction). *)
val sig_type_name : string

(** {2 Synthetic name generators}

    Centralized naming conventions for generated C++ identifiers. Each function
    takes an integer index and returns a string or [Id.t]. *)

(** Name for template type parameter [i], e.g. ["T0"]. *)
val tvar_name : int -> string

(** {!tvar_name} as an [Id.t]. *)
val tvar_id : int -> Id.t

(** Name for an anonymous/unresolved type variable [i], e.g. ["_tvar0"]. *)
val anon_tvar_name : int -> string

(** {!anon_tvar_name} as an [Id.t]. *)
val anon_tvar_id : int -> Id.t

(** Name for a function-typed template parameter [i], e.g. ["F0"]. *)
val fun_tparam_name : int -> string

(** {!fun_tparam_name} as an [Id.t]. *)
val fun_tparam_id : int -> Id.t

(** Fallback positional name for constructor field [i] when no binder name is
    registered, e.g. ["a0"] (["d_a0"] under the BDE flavor). *)
val field_param_name : int -> string

(** {!field_param_name} as an [Id.t]. *)
val field_param_id : int -> Id.t

(** {2 Constructor Field Name Registry}

    See {!Common.ctor_field_names} for design rationale. *)

(** A stable key for the inductive owning a constructor struct.  Accepts
    either the inductive or one of its constructors. *)
val ctor_owner_key : Names.GlobRef.t -> string

(** Register a named field for a constructor struct.  [owner] is the inductive
    the constructor belongs to (or the constructor itself). *)
val register_ctor_field_name :
  owner:Names.GlobRef.t -> string -> int -> Id.t -> unit

(** Look up the field name; falls back to [d_a{idx}] if unregistered. *)
val lookup_ctor_field_name : owner:Names.GlobRef.t -> string -> int -> Id.t

(** Clear the registry between extraction passes. *)
val reset_ctor_field_names : unit -> unit

(** {2 Constructor Binding Name Registry}

    Stores the base names used for structured-binding variables in pattern
    matches.  For fields whose kernel binder was anonymous the name falls back
    to the indexed form (e.g. [a0]) to prevent shadowing in nested matches. *)

(** Register a binding variable name for a constructor field. *)
val register_ctor_bind_name :
  owner:Names.GlobRef.t -> string -> int -> Id.t -> unit

(** Look up the binding variable name; falls back to [a{idx}] if unregistered. *)
val lookup_ctor_bind_name : owner:Names.GlobRef.t -> string -> int -> Id.t

(** Name for a synthesized eta-expansion binder [i], e.g. ["_x0"].  Used when a
    let-bound lambda must be eta-expanded to match its declared arity;
    numbered by de Bruijn depth at the synthesis site so nested synthesized
    binders cannot collide with each other or with source-level names, which
    never start with [_x]. *)
val eta_param_name : int -> string

(** {!eta_param_name} as an [Id.t]. *)
val eta_param_id : int -> Id.t

(** Name for a synthesized type-class instance parameter [i], e.g. ["_tcI0"]. *)
val tc_instance_name : int -> string

(** {!tc_instance_name} as an [Id.t]. *)
val tc_instance_id : int -> Id.t

(** Whether an identifier is one {!tc_instance_id} minted -- the binder for a
    typeclass instance passed as a concept template parameter.  Such a binder
    is synthesised here rather than extracted, so its name is the record of
    what it is; a binder that came from Coq is classified by its ML type
    instead. *)
val is_tc_instance_id : Names.Id.t -> bool

(** Fallback name for constructor [i] when no better name is available, e.g.
    ["Ctor0"]. *)
val ctor_fallback_name : int -> string

(** {!ctor_fallback_name} as an [Id.t]. *)
val ctor_fallback_id : int -> Id.t

(** The [n]th scrutinee cache temporary: [_cs], [_cs1], [_cs2], ...  A custom
    match template that mentions its scrutinee more than once binds it to one
    of these first, so a non-trivial scrutinee is evaluated once.

    Minted and recognised in the same place: {!Loopify} elides the redundant
    alias these introduce, and had been re-parsing the spelling to spot them. *)
val scrutinee_cache_id : int -> Id.t

(** Whether [id] is a {!scrutinee_cache_id}. *)
val is_scrutinee_cache_id : Id.t -> bool

(** Fallback name for a de-Bruijn-indexed variable [i] when no source binder
    name is available, e.g. ["_db0"]. *)
val db_fallback_name : int -> string

(** {!db_fallback_name} as an [Id.t]. *)
val db_fallback_id : int -> Id.t

(** Rename a template type parameter for the BDE flavor (prefixes with
    ["t_"]); identity under the standard flavor. *)
val tparam_name : Id.t -> Id.t

(** The template parameter names of the struct generated for packet [p] of
    inductive [kn]: the promoted variables its payloads name, then its own
    parameters. *)
val ind_struct_tparams :
  MutInd.t -> Miniml.ml_ind -> Miniml.ml_ind_packet -> Id.t list

(** Compute the C++ enum constructor name for a single already-uppercased
    string [s]: applies the BDE [e_] prefix, or escapes a spelling
    {!is_reserved_cpp_name} rules out.  Does not perform collision avoidance;
    prefer {!enum_ctor_names_of_packet} when the full sibling set is
    available. *)
val enum_ctor_name : string -> string

(** Compute the C++ enum constructor name for a single constructor [Id.t].
    See {!enum_ctor_name}. *)
val enum_ctor_name_of_id : Id.t -> string

(** Compute C++ enum constructor names for all constructors of an inductive
    type packet. Handles prime escaping and intra-enum collision avoidance.
    Deterministic: same packet always produces the same names. *)
val enum_ctor_names_of_packet : Id.t array -> string array

(** The C++ enum constructor name for constructor [j] (1-based) of packet [i]
    of the inductive [kn], by looking up its siblings. *)
val enum_ctor_name_of_ref : MutInd.t -> int -> int -> string

(** The last [::]-separated component of a qualified name, e.g. [Nat::add]
    becomes [add]. *)
val last_component : string -> string

(** Capitalize only the last [::]-separated component of a qualified name,
    e.g. [Nat::add] becomes [Nat::Add]. *)
val capitalize_last_component : string -> string

(** {2 Needed C++ Headers} *)

(** [writes h] records that what is being written needs the header [h].  It
    demands nothing: a unit's demands are read off what is generated ahead of
    its files ({!Cpp_demands}), and under [CRANE_CHECK_IR] what was written is
    checked against them ({!Table.written_needs_header}). *)
val writes : Table.header -> unit

(** [writes_standard h] is [writes (Standard h)]. *)
val writes_standard : string -> unit

(** What is being written erases a value, and so needs obj.h. *)
val writes_obj : unit -> unit
