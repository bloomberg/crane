(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** This module holds the mutable, per-extraction rendering state and registries
   shared across the C++ pretty-printers. It owns the current render context
   ([render_ctx]), the method and name-resolution
   registries, the [std::]-namespace name configuration ([std_names]),
   eponymous-record tracking, and the wrapper/collision/global-scope tables.
   Much of the surface is intentionally mutable global state (refs and
   hashtables) that is reset between extraction units via [reset_cpp_state]. *)

(** {2 Owned cells}

    A cell made by one of these is emptied by {!reset_cpp_state}, enrolled where
    it is defined.  [census] reports the size to {!Table.census}. *)

val owned_table : ?census:bool -> string -> ('a, 'b) Hashtbl.t
val owned_list : ?census:bool -> string -> 'a list ref
val owned_ref : 'a -> 'a ref

(** {2 Method registry} *)

(** Per-run and global method registries plus their accessors. *)
val method_registry : Method_registry.t option ref

(** Pre-built registry from the full [ml_structure], used in separate extraction
    so cross-module method calls are recognised. [None] when unset; cleared by
    [reset_cpp_state]. *)
val global_method_registry : Method_registry.t option ref

(** Set [global_method_registry] to [Some] the given registry. *)
val set_global_method_registry : Method_registry.t -> unit

(** Reset [global_method_registry] to [None]. *)
val clear_global_method_registry : unit -> unit

(** Return the contents of [method_registry].
    @raise CErrors.Anomaly if the registry has not been initialized. *)
val get_method_registry : unit -> Method_registry.t

(** {2 Name resolution} *)

(** Name-resolution cache and its accessor. *)
val name_cache : Name_resolution.t option ref

(** Return the contents of [name_cache].
    @raise CErrors.Anomaly if the cache has not been initialized. *)
val get_name_cache : unit -> Name_resolution.t

(** Pretty-printers for type variables and parameter lists. *)
val pp_tvar : Names.variable -> Pp.t

(** Print type variables as a boxed tuple, followed by a space when the list is
    non-empty. *)
val pp_parameters : Names.variable list -> Pp.t

(** Print already-rendered parameter strings as a boxed tuple, followed by a
    space when the list is non-empty. *)
val pp_string_parameters : string list -> Pp.t

(** Look up a custom type rendering for a global reference, if any. *)
val find_type_custom_opt : Names.GlobRef.t -> (string list * string) option

(** Reserved C++ keywords that identifiers must avoid. *)
val keywords : Names.Id.Set.t

(** C and POSIX library functions, refused only to a declaration that reaches
    global scope: there a Crane name of another kind -- a type alias, a
    variable, a struct -- redefines the library's rather than overloading it.
    Inside a namespace or struct they are ordinary names. *)
val c_library_globals : Names.Id.Set.t

(** {2 Output modules} *)

(** Set of module paths that are valid extraction outputs. *)
val valid_output_modules : (Names.ModPath.t, unit) Hashtbl.t

(** Replace the contents of [valid_output_modules] with the given module paths;
    afterwards only those modules yield [#include] lines from [pp_open]. *)
val set_valid_output_modules : Names.ModPath.t list -> unit

(** Empty [valid_output_modules], re-enabling [#include] emission for every
    module. *)
val clear_valid_output_modules : unit -> unit

(** {2 Wrappers} *)

(** Global registry of wrapper names that were not merged. *)
val global_unmerged_wrappers : (string, unit) Hashtbl.t

(** Record that the given wrapper struct name must stay unmerged across
    extraction passes, so references use the qualified form. *)
val mark_global_unmerged : string -> unit

(** [true] if the wrapper struct name was marked by [mark_global_unmerged]. *)
val is_global_unmerged : string -> bool

(** Empty [global_unmerged_wrappers]. *)
val clear_global_unmerged : unit -> unit

(** {2 Preamble} *)

(** Pretty-printers for includes, comments, and file preambles. *)
val pp_open : Names.ModPath.t -> Pp.t

(** The text as C++ line comments, one per line. *)
val pp_comment : string -> Pp.t

(** Print an optional header comment followed by a blank line; empty for
    [None]. *)
val pp_header_comment : string option -> Pp.t

(** Append a newline to the document unless it is empty. *)
val then_nl : Pp.t -> Pp.t

(** Build the preamble of an implementation file: the optional header comment
    followed by one [pp_open] line per used module. The first and last
    arguments are ignored. *)
val preamble : 'a -> string option -> Names.ModPath.t list -> 'b -> Pp.t

(** Build the preamble of a header/signature file; currently identical to
    [preamble]. *)
val sig_preamble : 'a -> string option -> Names.ModPath.t list -> 'b -> Pp.t

(** {2 Render context} *)

(** Where in the output the pretty-printer currently is. Immutable: the
    mutability lives in one installed position ({!current_render_ctx}), so that save/restore around a
    sub-render cannot forget a field. *)
type render_ctx = {
  rc_file : Common.file;  (** The file being written. *)
  rc_in_struct : bool;
  rc_concepts_hoisted : bool;
  rc_scope : Scope_plan.scope option;
  rc_in_template : bool;
  rc_module : Names.ModPath.t option;
      (** The module whose element is being written, if one is: the one
          whose struct a synthesised template it writes may be declared in
          ({!Cpp_print.ctor_alias_home}). *)
  rc_frame : Cpp_resolution.frame;
      (** The scopes printing the declaration being written has entered
          inside the one it is written in, innermost first
          ({!Cpp_names.enter}). *)
  rc_names : Cpp_resolution.table option;
      (** The names of the declaration of the tree being written
          ({!Cpp_ast.Declaration}), resolved before it is printed; none
          where what is written is no such declaration -- planning, the
          driver's own text, a synthesised template's body -- whose names
          are resolved where they are written. *)
  rc_visibility : Common.visibility option;
      (** The scopes whose names are visible where the printer is, innermost
          first: the planned visibility of what is being written
          ({!Scope_plan.visibility}), with a layer for each scope printing
          has entered that declares names ({!Cpp_names.next}); none where
          nothing planned it, where naming anything is an anomaly: no
          visibility is installed for a name to fall back on. *)
}

(** The context at the start of the file [file]: file scope, outside every
    struct. *)
val file_start : Common.file -> render_ctx

(** The context at file scope in the file [c] is written in. *)
val at_file_scope : render_ctx -> render_ctx

(** The position installed, reset by [reset_cpp_state]: where planning, and a
    boundary of the printer, reads it.  Printing threads the position through
    the scopes it enters ({!entering_scope}), so under [CRANE_CHECK_IR] a
    read inside one is a violation. *)
val current_render_ctx : unit -> render_ctx


(** A concept a frame is holding back until after the struct it was written
    in, identified by whatever declares it. *)
type held_concept =
  | HCmodtype of Names.ModPath.t  (** a module type's concept *)
  | HCclass of Names.GlobRef.t  (** a type class's concept *)

(** Equality on {!held_concept}. *)
val held_concept_equal : held_concept -> held_concept -> bool

(** The functor bodies whose module types are file-scope concepts over the
    functor's parameters as well as [M]: the body's path, the functor's
    label, and its parameters. *)
val functor_concept_scopes : (Names.ModPath.t * (Names.Label.t * Names.ModPath.t list)) list ref

(** Whether a concept is one the current frame is holding back. *)
val is_held_back_in : held_concept list -> held_concept -> bool

(** Where the header declares one of a module's concepts.  No concept can
    be declared inside a struct, so a module nested in one declares its
    concepts at file scope.  Otherwise a concept goes ahead of the module's
    struct, whose body may constrain a functor with it, unless it names one
    of the struct's members, when it follows the struct. *)
type concept_placement = Ahead_of_struct | After_struct | At_file_scope

(** The concepts of a module's classes and module types, planned ahead of
    the files: where each is declared, and which the struct's body treats as
    not declared yet ({!concept_held_back}). *)
type concept_plan = {
  placements : (held_concept * concept_placement) list;
      (** The class concepts, then the module-type concepts, in declaration
          order. *)
  held_back : held_concept list;
}

(** [plan_module_concepts mp plan] plans [plan] for the module [mp]. *)
val plan_module_concepts : Names.ModPath.t -> concept_plan -> unit

(** The concepts planned for the module [mp]; an anomaly if none were. *)
val concept_plan : Names.ModPath.t -> concept_plan

(** [planned_held_back ~file mp] is what the concepts held back around the
    body of the module [mp] are in [file], innermost first: in the header,
    those each module frame around it ({!Scope_plan.frames}) holds back,
    as planned ({!concept_plan}); in the implementation, which declares no
    concept, none. *)
val planned_held_back : file:Common.file -> Names.ModPath.t -> held_concept list

(** Whether the struct the position is in holds concept [c] back: declared
    after it, so a constraint inside it cannot name [c] yet.  What is held
    back is planned around the module the position writes an element of, in
    the file it is written in ({!planned_held_back}). *)
val concept_held_back : render_ctx -> held_concept -> bool

(** Whether the concept of type class [r] is held back by the struct the position is
    in: declared after it, so nothing inside may name it.  A
    [static_assert] is deferred with it, and a template parameter it would
    constrain is left a plain [typename], which the deferred assertion still
    checks for every instance. *)
val class_concept_held_back : render_ctx -> Names.GlobRef.t -> bool

(** [with_render_ctx upd f] renders [f] in the context [upd] derives from the
    current one, restoring the enclosing context on the way out however [f]
    leaves -- returning or raising. The only supported way to change the
    context.  Deriving it inside a scope printing entered is a violation, as
    reading it is ({!current_render_ctx}). *)
val with_render_ctx : (render_ctx -> render_ctx) -> (unit -> 'a) -> 'a

(** [entering_scope f] runs [f] inside a scope printing entered, which
    installs no position: printing hands the position to what it prints
    there.  A declaration's spelling is one, entered wherever the
    declaration is resolved or printed. *)
val entering_scope : (unit -> 'a) -> 'a

(** [writing_file file f] renders [f] as part of the file [file]. *)
val writing_file : Common.file -> (unit -> 'a) -> 'a

(** [element_position mp c] is the position [c] writing an element of the
    module [mp]: in the visibility planned for its body. *)
val element_position : Names.ModPath.t -> render_ctx -> render_ctx

(** [writing_element_of mp f] runs [f] writing an element of the module
    [mp] ({!element_position}, {!current_render_ctx}). *)
val writing_element_of : Names.ModPath.t -> (unit -> 'a) -> 'a

(** [installing c f] runs [f] with the position [c] installed, which the
    caller threads: for what is reached beneath it that still reads the
    installed position -- the generators the driver calls -- rather than
    being handed it. *)
val installing : render_ctx -> (unit -> 'a) -> 'a

(** {2 Template static accessors} *)

(** Tracking for template static accessor labels and their kernel names. *)
val template_static_accessors : (Names.ModPath.t * Names.Label.t) list ref

(** Canonical kernel names of template static accessors, which is what a
    constant reached through a module alias is. Cleared by
    [reset_cpp_state]. *)
val template_static_accessor_kns : (Names.KerName.t, unit) Hashtbl.t

(** Record the definition at the given module path and label as a template
    static accessor (Meyers singleton), by adding it to
    [template_static_accessors].  Idempotent. *)
val register_template_static_accessor :
  Names.ModPath.t -> Names.Label.t -> unit

(** Whether the definition [lbl] of [mp] is recorded as an accessor. *)
val is_template_static_accessor : Names.ModPath.t -> Names.Label.t -> bool

(** {!register_template_static_accessor} for a global reference, which also
    records the constant's kername for cross-functor matching. *)
val register_template_static_accessor_ref : Names.GlobRef.t -> unit

(** {2 Eponymous records} *)

(** In-flight state used while emitting an eponymous record. *)
val eponymous_type_ref : Names.GlobRef.t option ref

(** Set during module rendering when the eponymous inductive should be promoted
    into the module struct; [cpp_ind.ml] then renders its fields flat instead of
    inside a wrapping struct. Reset to [None] by [reset_cpp_state]. *)
val eponymous_promote_ref : Names.GlobRef.t option ref

(** Method candidates collected for the current eponymous type, as
    [(function_ref, body, type, this_position)] where [this_position] is the
    0-based index of the first argument matching the eponymous type. Reset to
    [[]] by [reset_cpp_state]. *)
val method_candidates :
  (Names.GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref

(** The eponymous record of the module being rendered, as
    [(record_ref, field_refs, ind_packet)], whose fields are merged into the
    module struct. Reset to [None] by [reset_cpp_state]. *)
val eponymous_record :
  (Names.GlobRef.t * Miniml.record_field list * Miniml.ml_ind_packet)
  option ref

(** {2 Scoped render state} *)

(** [with_module_frame f] renders [f] as a module frame: it starts with no
    eponymous type, no eponymous record and no method candidates of its own, and
    leaves the enclosing frame's untouched, however [f] leaves -- returning or
    raising. *)
val with_module_frame : (unit -> 'a) -> 'a

(** [setting cell v f] runs [f] with [cell] holding [v] and puts the enclosing
    contents back on the way out, however [f] leaves -- returning or raising. *)
val setting : 'a ref -> 'a -> (unit -> 'b) -> 'b

(** {2 std:: names} *)

(** Configurable names for the [std::] symbols emitted by the extractor. *)
type std_names = {
  shared_ptr : string;
  make_shared : string;
  move : string;
  forward : string;
  logic_error : string;
  ns : string;
  string : string;  (** the string class a spliced literal is constructed as *)
  same_as : string;
  declval : string;
  convertible_to : string;
  holds_alternative : string;
  get_if : string;
  get : string;
  variant : string;  (** the tagged union inductives store alternatives in *)
  variant_header : Table.header;  (** the header declaring {!variant} *)
  enable_from_this : string;
}

(** The plain [std::] flavor of {!std_names} (with the ["s"]
    string-literal suffix). *)
val default_std_names : std_names

(** The names in effect for the current extraction pass; initialized by
    [init_std_names] and read through [sn]. *)
val std_names : std_names ref

(** Build a name set for a namespace prefix. ["bsl::"] yields the BDE flavor
    (with the ["_s"] suffix); any other prefix yields
    [default_std_names]. *)
val mk_std_names : string -> std_names

(** Set [std_names] from the current [Table] settings: the BDE flavor when
    [Table.std_lib ()] is ["BDE"], otherwise the [std::] flavor; then, if
    [Table.non_atomic_rc ()], override the smart pointer with [crane::rc] /
    [crane::make_rc] / [crane::enable_rc_from_this]. *)
val init_std_names : unit -> unit

(** Shorthand for [!std_names]. *)
val sn : unit -> std_names

(** Whether an ML type denotes a typeclass instance. *)
val is_typeclass_instance : 'a -> Miniml.ml_type -> bool

(** {2 Wrapper and scope tables} *)

(** [wrapper_qualify_modname mp name] re-roots [name] at the wrapper struct
    holding [mp], when [mp] is a bystander that struct nests under its own name.
    The module-as-a-module counterpart of [wrapper_qualify]. *)
val wrapper_qualify_modname : Names.ModPath.t -> string -> string

(** Wrapper struct names that have pending declarations and therefore cannot be
    merged, with the module each wraps. Cleared by [reset_cpp_state]. *)
val unmerged_wrappers : (string, Names.ModPath.t) Hashtbl.t

(** Whether an inductive's struct is written inside a wrapper that holds
    other declarations, and so is spelled [List::list] rather than [List]: a
    property of its declaration, the same wherever a use is written. *)
val in_unmerged_wrapper : Names.GlobRef.t -> bool

(** What a nested struct name was emitted for: a Rocq reference, or a module
    (which has no [GlobRef.t]). *)
type nested_struct_owner =
  | NSref of Names.GlobRef.t
  | NSmodule of Names.ModPath.t

(** C++ names of structs emitted as members of an enclosing struct, mapped to
    every owner they stand for. A nested struct shadows any global-scope type
    of the same name. Cleared by [reset_cpp_state]. *)
val nested_struct_names : (string, nested_struct_owner list) Hashtbl.t

(** The inductives a module's rendering promoted, under [CRANE_CHECK_IR]. *)
val rendered_promotions : Names.GlobRef.t list ref

(** Record that a module's rendering promoted the inductive, under
    [CRANE_CHECK_IR]: the planned ones must be exactly the rendered ones. *)
val rendered_promotion : Names.GlobRef.t -> unit

(** The same owner. *)
val nested_struct_owner_equal : nested_struct_owner -> nested_struct_owner -> bool

(** The nested structs the printer printed, under [CRANE_CHECK_IR]. *)
val printed_nested_structs : (string * nested_struct_owner) list ref

(** Record that the printer printed [owner] as a nested struct named
    [name], under [CRANE_CHECK_IR]: the planned ones must be exactly the
    printed ones. *)
val printed_nested_struct : string -> nested_struct_owner -> unit

(** Record that an owner was emitted as a nested struct under the given C++
    name. *)
val add_nested_struct_name : string -> nested_struct_owner -> unit

(** Whether the reference is itself emitted as a struct nested in another. *)
val is_nested_struct_ref : Names.GlobRef.t -> bool

(** Whether a reference rendered unqualified under the given name is shadowed
    by a nested struct of that name. False for the shadower itself. *)
val is_shadowed_global_name : string -> Names.GlobRef.t -> bool

(** Qualify a C++ name with its wrapper struct when the reference's module path
    is a wrapper module. [VarRef] references (lifted declarations) are never
    qualified, and already-qualified names are only rewritten for
    collision-wrapped modules, whose child qualifier is replaced by the wrapper
    struct name.
    @return the possibly-qualified name *)
val wrapper_qualify : Names.GlobRef.t -> Cpp_name.t -> Cpp_name.t

(** {2 Method registration} *)

(** The candidate a function, given its body and type, is as a method of an
    eponymous type, where the registry made it one
    ({!Method_registry.planned_candidate}); the render adds no method. *)
val planned_method_candidate :
  Names.GlobRef.t ->
  Names.GlobRef.t ->
  Miniml.ml_ast -> Miniml.ml_type -> Method_registry.method_candidate option

(** Look up a function in the method registry.
    @return [Some (eponymous_type, this_position)] if it is registered as a
      method, [None] otherwise *)
val is_registered_method : Names.GlobRef.t -> (Names.GlobRef.t * int) option

(** Number of value parameters a registered method takes, receiver included;
    [0] when unknown. *)
val lookup_method_arity : Names.GlobRef.t -> int

(** Return the 0-based positions, in a registered method's type-variable list,
    of the inductive's own template parameters — those deducible from the
    receiver and thus omitted from explicit template arguments. *)
val lookup_method_ind_tvar_positions : Names.GlobRef.t -> int list

(** The type of a registered method's receiver at the given instantiation: the
    eponymous inductive applied to the type arguments sitting at
    {!lookup_method_ind_tvar_positions}. [None] when the reference is not a
    registered method, or is not instantiated at all of those positions. *)
val method_receiver_cpp_type :
  Names.GlobRef.t -> Minicpp.cpp_type list -> Minicpp.cpp_type option

(** Whether the method's return type is erased to [std::any]
    ({!Method_registry.method_returns_any}). *)
val method_returns_any : Names.GlobRef.t -> bool

(** {2 Eponymous record registry} *)

(** Declarations of the structure currently being emitted. *)
val current_structure_decls :
  (Names.Label.t * Miniml.ml_structure_elem) list ref

(** {2 Per-run reset} *)

(** Reset all mutable state between extraction units. *)
val reset_cpp_state : unit -> unit

(** {2 Projections} *)

(** Queries about eponymous-record and suppressed projections, and dfix filtering. *)
val is_eponymous_record_projection : Names.GlobRef.t -> bool

(** [true] for a projection that is not a higher-order projection, and so should
    not be rendered as a standalone function. *)
val is_suppressed_projection : Names.GlobRef.t -> bool

(** Drop from a [Dfix] group the entries that are inline customs, local or
    globally registered method candidates, eponymous-record projections, or
    suppressed projections. *)
val filter_dfix : Miniml.ml_fix_def list -> Miniml.ml_fix_def list
