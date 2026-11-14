(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The mutable, per-extraction state and registries shared by the C++
   printing modules ({!Cpp}, {!Cpp_print}, {!Cpp_ind}, {!Cpp_names},
   {!Cpp_leaf_plan}), which print the finished CppIR program.  It defines the
   position type every writer is handed ({!render_ctx}), and owns the method
   and name-resolution registries, the [std::]-namespace name configuration
   ({!std_names}), eponymous-record tracking, and the wrapper, nested-struct
   and concept-placement tables.  Much of the surface is mutable global state
   (refs and hashtables) that {!reset_cpp_state} empties between extractions;
   it lives here so the other [cpp_*] modules can share it without depending
   on each other. *)

(** {2 Owned cells}

    A cell made by one of these is emptied by {!reset_cpp_state}, enrolled where
    it is defined.  [census] reports the size to {!Table.census}. *)

(** [owned_table name] is a fresh hash table emptied on reset, reported to
    the census under [name] unless [~census:false]. *)
val owned_table : ?census:bool -> string -> ('a, 'b) Hashtbl.t

(** [owned_list name] is a fresh list ref emptied on reset; [census] as for
    {!owned_table}. *)
val owned_list : ?census:bool -> string -> 'a list ref

(** [owned_ref init] is a ref restored to [init] on reset; it holds one
    value, so it is not censused. *)
val owned_ref : 'a -> 'a ref

(** {2 Method registry} *)

(** The unit's method registry, built once per extraction pass by scanning
    the [ml_structure]; read through {!get_method_registry}. *)
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

(** The name-resolution cache, populated once per extraction pass; read
    through {!get_name_cache}. *)
val name_cache : Name_resolution.t option ref

(** Return the contents of [name_cache].
    @raise CErrors.Anomaly if the cache has not been initialized. *)
val get_name_cache : unit -> Name_resolution.t

(** Print a type variable by its name. *)
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

(** The module paths that produce output files in separate extraction.
    Empty means every module does. *)
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

(** [#include "m.h"] for the module, followed by a newline; nothing if
    {!valid_output_modules} is non-empty and does not contain it. *)
val pp_open : Names.ModPath.t -> Pp.t

(** The text as C++ line comments, one per line. *)
val pp_comment : string -> Pp.t

(** Print an optional header comment followed by a blank line; empty for
    [None]. *)
val pp_header_comment : string option -> Pp.t

(** Append a newline to the document unless it is empty. *)
val then_nl : Pp.t -> Pp.t

(** Build the preamble of an implementation or a header file: the optional
    header comment followed by one [pp_open] line per used module. The first
    and last arguments are ignored. *)
val preamble : 'a -> string option -> Names.ModPath.t list -> 'b -> Pp.t

(** {2 Render context} *)

(** Where a synthesised template is declared: inside the struct of a
    module, as its members are written, or at namespace scope, beneath the
    unit's files, innermost last -- the files as the module whose element
    first spelled it sees them. *)
type declared_in = In_struct_of of Names.ModPath.t | At_namespace_scope of Names.ModPath.t list

(** A parameter of a holder ({!ctor_alias}), as its body writes it: a
    captured variable written applied to the alias's own argument, a type
    constructor ([template <typename> class F0]); one written bare, or a
    class instance the body reads a type out of, a type ([typename P1]). *)
type holder_parameter = Constructor_parameter of Names.Id.t | Type_parameter of Names.Id.t

(** What a holder is applied to where it is written, the argument for each
    of its parameters in order: a type variable of the enclosing declaration
    its body captures, by index (and the name it is written by, where it
    carries one), or a class instance its body reads a type out of. *)
type holder_argument = Captured_variable of int * Names.Id.t option | Captured_instance of Names.Id.t

(** A template synthesised for a type constructor with no template name of
    its own, where it is spelled as a template template argument
    ([Cpp_leaf_plan.ctor_alias_at]). *)
type ctor_alias = {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : holder_parameter list option;
      (** A holder's parameters, in order, where it is one; none where it is
          a plain alias. *)
  ca_declared : declared_in;  (** Where it is declared ([Cpp_leaf_plan.ctor_alias_declared]). *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared, with the
          sentinel where the template's own parameter goes. *)
  ca_type : Cpp_ir.Resolved.Type.t;  (** That type. *)
  ca_vars : Names.Id.t list;  (** The names of the variables it names by index. *)
  ca_uses : tyctor_use list;
      (** How its body writes the type constructors in it, decided where the
          body was planned: what printing its declaration reads. *)
}

(** How a type constructor written as a template template argument is
    written, decided where it is planned ([Cpp_leaf_plan.ctor_alias_at]). *)
and tyctor_use = {
  tu_constructor : Cpp_ir.Resolved.Type.t;
      (** The constructor: the type with its arguments stripped
          ([Cpp_print.tyctor_constructor]). *)
  tu_vars : Names.Id.t list;  (** The names of the type variables it names by index. *)
  tu_alias : (ctor_alias * holder_argument list) option;
      (** The template synthesised for it, with the arguments a holder is
          applied to, if it has no template name of its own. *)
}

(** What the names written at a position are read off. *)
type naming =
  | No_names
      (** Nothing: naming anything here is an anomaly.  Every position
          starts so ({!file_start}). *)
  | Naming_live of live_namers
      (** The program, where the resolver names a key where it stands
          ({!Cpp_names.live_name}): the one position that names live, with
          the namers it hands the naming functions it shares with the
          printer, which name nothing live themselves. *)
  | Names_resolved of Cpp_resolution.table
      (** The names of what is being written, resolved before it is
          written: a leaf of the tree ({!Cpp_ast.unprinted.names}), or what
          planning spells, which it resolves first. *)

(** How the resolver names, at a position, a key, a global, and the inline
    custom text of a global, if it has one, writes a global type's head,
    and answers any key. *)
and live_namers = {
  live_key : render_ctx -> Cpp_resolution.key -> Cpp_name.t;
  live_global : render_ctx -> Common.kind -> Names.GlobRef.t -> Cpp_name.t;
  live_inline : Names.GlobRef.t -> string option;
  live_head : render_ctx -> Cpp_resolution.head_form -> Names.GlobRef.t -> Cpp_resolution.head;
  live_value : render_ctx -> Cpp_resolution.key -> Cpp_resolution.value;
}

(** Where the type printer reads how a type constructor is written. *)
and tyctor_plan =
  | Unplanned  (** Nowhere: writing one here is an anomaly. *)
  | Deciding of tyctor_decision
      (** Off planning, which decides it where it is spelled and notes the
          decision: what planning reads off what it plans. *)
  | Planned of tyctor_use list
      (** Off the plan of the leaf being printed; an anomaly if it has none
          for the constructor. *)

(** How planning decides, at a position, how a type constructor naming the
    given variables is written, and the uses it has decided, in the order
    first spelled: the printer decides none. *)
and tyctor_decision = {
  decide : render_ctx -> Names.Id.t list -> Cpp_ir.Resolved.Type.t -> (ctor_alias * holder_argument list) option;
      (** The decision ([Cpp_leaf_plan.ctor_alias_at]). *)
  noted : tyctor_use list ref;  (** The uses decided so far, in the order first spelled. *)
}

(** The out-of-line definition being written: the scope it is a member
    of, as planned, which a name written outside that struct's body is
    qualified by; and the promoted type variables whose alias its file
    declares at file scope ({!header_file_scope}), which such a variable
    written in it means instead of a member of that struct. *)
and out_of_line = {
  ol_scope : Scope_plan.scope;  (** The scope it is a member of. *)
  ol_file_scope_aliases : Names.Id.Set.t;
      (** The promoted type variables whose alias its file declares at file
          scope. *)
}

(** Where in the output something is written or planned: a value, handed
    to whatever writes there and derived as each scope is entered
    ({!Cpp_names.next}).  No position is installed anywhere for a reader to
    find. *)
and render_ctx = {
  rc_file : Common.file;  (** The file being written. *)
  rc_in_struct : bool;
      (** Inside a struct body; affects how nested type references are
          qualified and whether a held-back concept may be named. *)
  rc_concepts_hoisted : bool;
      (** The type class concepts of the current module are already
          written. *)
  rc_scope : out_of_line option;
      (** The out-of-line definition being written, if one is. *)
  rc_in_template : bool;
      (** Inside a template struct (a functor); affects [typename]
          insertion and how a module-level value is written. *)
  rc_module : Names.ModPath.t option;
      (** The module whose element is being written, if one is: the one
          whose struct a synthesised template it writes may be declared in
          ([Cpp_leaf_plan.ctor_alias_home]). *)
  rc_frame : Cpp_resolution.frame;
      (** The scopes printing the declaration being written has entered
          inside the one it is written in, innermost first
          ({!Cpp_names.enter_from}). *)
  rc_names : naming;  (** What the names written here are read off ({!naming}). *)
  rc_visibility : Common.visibility option;
      (** The scopes whose names are visible where the declaration being
          written is written, innermost first: its planned visibility
          ({!Scope_plan.visibility}); none where nothing planned it, where
          naming anything is an anomaly: no visibility is installed for a
          name to fall back on.  The scopes printing has entered inside it
          ({!rc_frame}) that declare names add their layers where the
          resolver reads it ({!Cpp_names.visibility_at}): printing a
          resolved name needs none of them. *)
  rc_aliases : ctor_alias list ref option;
      (** Where the synthesised templates spelled from here are collected,
          in the order first spelled, by what asked which ones its text
          spells ([Cpp_leaf_plan.ctor_aliases_found]); none where nothing
          collects them.  Every position derived from this one collects into
          the same list, a template's body written where it is declared
          included. *)
  rc_tyctors : tyctor_plan;
      (** How the type constructors written from here are written
          ({!tyctor_plan}). *)
}

(** The context at the start of the file [file]: file scope, outside every
    struct. *)
val file_start : Common.file -> render_ctx

(** What a file declares at file scope: the types, by the entity each
    declaration declares, and the promoted type variables among them, by
    the name their one alias is declared under ({!Table.promoted_type_var_field}). *)
type file_scope = {
  fs_types : Names.GlobRef.Set.t;  (** The types it declares at file scope. *)
  fs_aliases : Names.Id.Set.t;  (** The promoted type variables among them, by alias name. *)
}

(** What the header declares at file scope, planned with its layout
    ({!Cpp_leaf_plan.file_scope_types}); [None] until planned, which file
    layout planning's own questions are asked before.  The implementation
    declares no type of its own. *)
val header_file_scope : file_scope option ref

(** The types the file [file] declares at file scope, as planned: none
    before they are planned. *)
val file_scope_types_of : Common.file -> Names.GlobRef.Set.t

(** The promoted type variables whose alias the file [file] declares at
    file scope, as planned: none before they are planned. *)
val file_scope_aliases_of : Common.file -> Names.Id.Set.t


(** A concept a frame is holding back until after the struct it was written
    in, identified by whatever declares it. *)
type held_concept =
  | HCmodtype of Names.ModPath.t  (** a module type's concept *)
  | HCclass of Names.GlobRef.t  (** a type class's concept *)

(** Equality on {!held_concept}. *)
val held_concept_equal : held_concept -> held_concept -> bool

(** The modules whose module types are file-scope concepts over a
    functor's parameters ({!Module_plan.concept_scope}): a functor's body,
    an application of the functor, or an alias of the application, each by
    its path, with the functor and its argument modules. *)
val functor_concept_scopes : (Names.ModPath.t * Module_plan.concept_scope) list ref

(** Whether a concept is one the current frame is holding back. *)
val is_held_back_in : held_concept list -> held_concept -> bool

(** Where the header declares one of a module's concepts.  No concept can
    be declared inside a struct, so a module nested in one declares its
    concepts at file scope.  Otherwise a concept goes ahead of the module's
    struct, whose body may constrain a functor with it, unless it names one
    of the struct's members, when it follows the struct.
    {ul {- [Ahead_of_struct]: ahead of the module's struct.}
        {- [After_struct]: after the struct, because it names a member.}
        {- [At_file_scope]: at file scope, because the module is nested in
           a struct.}} *)
type concept_placement = Ahead_of_struct | After_struct | At_file_scope

(** The concepts of a module's classes and module types, planned ahead of
    the files: where each is declared, and which the struct's body treats as
    not declared yet ({!concept_held_back}). *)
type concept_plan = {
  placements : (held_concept * concept_placement) list;
      (** The class concepts, then the module-type concepts, in declaration
          order. *)
  held_back : held_concept list;
      (** The concepts declared after the struct, which its body may not
          name. *)
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

(** [element_position mp c] is the position [c] writing an element of the
    module [mp]: in the visibility planned for its body. *)
val element_position : Names.ModPath.t -> render_ctx -> render_ctx

(** {2 What function bodies read} *)

(** [plan_function_reads s]: [s] is every global a function body of the
    unit names, from the unit's installed declarations
    ({!Unit_program.installed_finished}), before either file is rendered.
    The program-wide set from {!note_program_reads} is added to it. *)
val plan_function_reads : Ref.Can.Set.t -> unit

(** [note_program_reads s], before any unit of a separate extraction is
    generated: [s] is every global another declaration of the program names.
    A function of a later unit, not yet generated when an earlier one is
    planned, may read a value of the earlier one; each unit's
    {!plan_function_reads} counts all of [s]. *)
val note_program_reads : Ref.Can.Set.t -> unit

(** Whether a function body of the unit names [r] (as planned by
    {!plan_function_reads}; nothing does before it is planned).  A header's
    [static inline] variable such a body reads is written [[[gnu::used]]]:
    see the CppIR [Variable] case of {!Cpp_print}'s declaration printer. *)
val read_by_a_function : Names.GlobRef.t -> bool

(** {2 Template static accessors} *)

(** The definitions written as function accessors (Meyers singletons)
    instead of static inline variables, by module path and label, to avoid
    template static initialisation order problems. *)
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

(** The eponymous type of the module being rendered: an inductive [m] in a
    module [M], whose functions taking an [m] become methods of it.  Reset
    by {!with_module_frame} and {!reset_cpp_state}. *)
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

(** Configurable names for the [std::] symbols emitted by the extractor.
    Each is the [std::] or [bsl::] spelling of the field's name unless noted;
    [Crane NonAtomicRc], [Crane FastVariant], [Crane SharedVariant] and
    [CRANE_COUNT_RC] substitute runtime names ({!init_std_names}). *)
type std_names = {
  shared_ptr : string;  (** the smart pointer for recursive fields *)
  make_shared : string;  (** its factory *)
  move : string;
  forward : string;
  logic_error : string;
  ns : string;  (** the bare namespace, ["std"] or ["bsl"] *)
  string : string;  (** the string class a spliced literal is constructed as *)
  same_as : string;  (** unqualified in the BDE flavor *)
  declval : string;
  convertible_to : string;  (** unqualified in the BDE flavor *)
  holds_alternative : string;
  get_if : string;
  get : string;
  variant : string;  (** the tagged union inductives store alternatives in *)
  variant_header : Table.header;  (** the header declaring {!variant} *)
  enable_from_this : string;  (** the base a type that hands out pointers to itself derives from *)
}

(** The plain [std::] flavor of {!std_names}. *)
val default_std_names : std_names

(** The names in effect for the current extraction pass; initialized by
    [init_std_names] and read through [sn]. *)
val std_names : std_names ref

(** Build a name set for a namespace prefix. ["bsl::"] yields the BDE flavor;
    any other prefix yields [default_std_names]. *)
val mk_std_names : string -> std_names

(** Set [std_names] from the current [Table] settings: the BDE flavor when
    [Table.std_lib ()] is ["BDE"], otherwise the [std::] flavor; then, under
    [Table.fast_variant ()] or [Table.shared_variant ()], the [crane::]
    variant accessors (and, for the former, [crane::variant]); then, under
    [Table.count_rc ()], the counting pointer, or else under
    [Table.non_atomic_rc ()], [crane::rc] / [crane::make_rc] /
    [crane::enable_rc_from_this]. *)
val init_std_names : unit -> unit

(** Shorthand for [!std_names]. *)
val sn : unit -> std_names

(** {2 Wrapper and scope tables} *)

(** Wrapper struct names that have pending declarations and therefore cannot be
    merged, with the module each wraps. Cleared by [reset_cpp_state]. *)
val unmerged_wrappers : (string, Names.ModPath.t) Hashtbl.t

(** Whether an inductive's struct is written inside a wrapper that holds
    other declarations, and so is spelled [List::list] rather than [List]: a
    property of its declaration, the same wherever a use is written. *)
val in_unmerged_wrapper : Names.GlobRef.t -> bool

(** {!in_unmerged_wrapper}, the inductive's short name given. *)
val in_unmerged_wrapper_named : string -> Names.GlobRef.t -> bool

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

(** Equality on {!nested_struct_owner}. *)
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
    of the inductive's own template parameters: those deducible from the
    receiver and thus omitted from explicit template arguments. *)
val lookup_method_ind_tvar_positions : Names.GlobRef.t -> int list

(** Whether the method's return type is erased to [std::any]
    ({!Method_registry.method_returns_any}). *)
val method_returns_any : Names.GlobRef.t -> bool

(** {2 Current structure} *)

(** Declarations of the structure currently being emitted, scanned for
    methods defined by sibling modules of the same Rocq module. *)
val current_structure_decls :
  (Names.Label.t * Miniml.ml_structure_elem) list ref

(** {2 Per-run reset} *)

(** Reset all mutable state between extraction units. *)
val reset_cpp_state : unit -> unit

(** {2 Projections} *)

(** Whether the reference is a projection of the eponymous record
    ({!eponymous_record}), redundant once its fields are merged into the
    module struct. *)
val is_eponymous_record_projection : Names.GlobRef.t -> bool

(** [true] for a projection that is not a higher-order projection, and so should
    not be rendered as a standalone function. *)
val is_suppressed_projection : Names.GlobRef.t -> bool

(** Drop from a [Dfix] group the entries that are inline customs, local or
    globally registered method candidates, eponymous-record projections, or
    suppressed projections. *)
val filter_dfix : Miniml.ml_fix_def list -> Miniml.ml_fix_def list
