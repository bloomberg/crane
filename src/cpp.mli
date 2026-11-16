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

(** {1 C++ extraction driver}

    Final stage of the extraction pipeline, from a Core structure to the
    text of a header and an implementation file.  Before either file is
    rendered it analyses the structure ({!prepare_structure}), plans what
    rendering reads (the [plan_*] values: names, scopes, callable heads,
    file layout, synthesised templates), generates every declaration the
    files write and finishes it into CppIR in the unit's program
    ({!generate_ahead}, {!Unit_program}).  Each file's render then assembles
    the finished declarations into a CppAST tree ({!Cpp_ast}), schedules,
    resolves and prints it.  Lower-level work is delegated to:
    {ul
    {- {!Unit_plan.Cpp_state}: per-unit render state and plans;}
    {- {!Unit_plan.Cpp_names}: name resolution and qualification;}
    {- {!Cpp_ind}: which C++ declarations a Core declaration becomes;}
    {- {!Cpp_leaf_plan} and {!Cpp_print}: what a CppIR leaf asks of
       resolution and scheduling, and its printing;}
    {- {!Cpp_concepts}: module-type concepts as text.}} *)

(** Language descriptor for C++. Provides the preamble, file suffix,
    pretty-printers, and other hooks that {!Extract_env} needs to drive a full
    extraction pass. *)
val cpp_descr : Translation_state.t Backend.t

(** The methods registered for the inductives of a structure
    ({!Core_plan.Method_registry.create}), decided outside every module body. *)
val method_registry_of : Translation_state.t -> Core.Program.t -> Core_plan.Method_registry.t

(** Decide the unit's layout before either file is rendered: analyse the
    structure ({!Core_plan.Structure}), record what rendering reads of the
    analysis, and return the {!Core_plan.Module_plan} it decides, which the unit's
    context [u] does not hold yet, how the unit's inductives are
    classified ({!Unit_plan.Context.t.names}), and the analysis, which the
    backend's plans for the unit hold ({!Unit_plan.Cpp_state.plans.analysis}). *)
val prepare_structure :
  Translation_state.t -> Unit_plan.Context.t -> Core.Program.t -> Core_plan.Module_plan.t * Core_plan.Name_resolution.t * Core_plan.Structure.t

(** [registered_methods kn ind] -- each function registered as a method of
    one of [ind]'s inductives, generated with it: the inductive, the
    variables of the struct it is generated in -- an eponymous record's own,
    otherwise the inductive's struct's -- and the method's candidate. *)
val registered_methods :
  Translation_state.t -> ?order:(Core_plan.Method_registry.method_candidate list -> Core_plan.Method_registry.method_candidate list) ->
  Names.MutInd.t ->
  Core.Inductive.t ->
  (Names.GlobRef.t * Names.Id.t list * Core_plan.Method_registry.method_candidate) list

(** The callable plan of each function the renders will generate, in the
    order of the unit's modules and declarations, or the reverse if
    [reversed]; planned once the plan {!prepare_structure} returns is
    installed, and before anything is rendered.  A function no render
    generates -- a method, a projection, an
    inline custom -- has none.  With them, the plans of each instance's
    struct's methods, by name; and the frame and the concepts of each
    module, as the walk planning them entered it, which the backend's plans
    for the unit hold ({!Unit_plan.Cpp_state.plans}). *)
val plan_callables :
  Translation_state.t -> ?reversed:bool ->
  Core.Program.t ->
  (Core_plan.Callable_abi.t list * (Names.GlobRef.t * (Names.Id.t * Core_plan.Callable_abi.t) list) list)
  * (Unit_plan.Cpp_state.module_frame Names.MPmap.t * Unit_plan.Cpp_state.concept_plan Names.MPmap.t)

(** Generate every function the renders write, and every instance's struct,
    before either file is rendered, for both files
    ({!Cpp_ind.generating_ahead}), in the unit given. *)
val generate_ahead : Translation_state.t -> Unit_plan.Context.t -> Core.Program.t -> unit

(** Generate what one declaration, an element of the module [module_], is
    written as, before it is rendered, and finish it into the unit's
    program: the walk {!generate_ahead} would make for a structure holding
    only it, in the unit given. *)
val generate_decl_ahead : Translation_state.t -> Unit_plan.Context.t -> module_:Names.ModPath.t -> Core.Decl.t -> unit

(** The files the names of the unit [s] are written through, read off what
    {!generate_ahead} generated: what its files include. *)
val files_named_ahead : Translation_state.t -> Unit_plan.Context.t -> Core.Program.t -> Names.ModPath.t list

(** The customs the unit's files write, read off what {!generate_ahead}
    generated in the unit given: whose imports its files include. *)
val customs_written_ahead : Translation_state.t -> Unit_plan.Context.t -> Core.Ref.User.Set.t

(** Plan, from what {!generate_ahead} finished, which globals the unit's
    function bodies read ({!Unit_plan.Cpp_state.read_by_a_function}): every installed
    declaration's but a variable's, whose initialiser is not a function
    body. *)
val plan_function_reads : unit -> unit

(** Plan, before either file is rendered and from what {!generate_ahead}
    generated, where the header writes what it does not write in place --
    the erasure landing pads and the declarations of lifted helpers at the
    top, the member definitions a datatype gave up at the end -- and which
    modules' structs it declares ahead of the file: a struct of nothing but
    static function declarations whose types are declared by the file's
    forward declarations and name nothing inside another struct.  [u] is
    the unit's context. *)
val plan_file_layout : Translation_state.t -> Unit_plan.Context.t -> Core.Program.t -> unit

(** The plan of the synthesised templates each file writes, before either
    is rendered ({!Cpp_leaf_plan.plan_ctor_aliases}). *)
val plan_ctor_aliases : Translation_state.t -> Core.Program.t -> Unit_plan.Cpp_state.ctor_alias_plan

(** The C++ name of each global the unit declares, a functor's body
    included, decided in declaration order ({!Base.Common.pp_global_name}): an
    inductive's, then its constructors', then a record's fields, at the kind
    a declaration is printed at.  A custom mapping's name is its text, and is
    not among them. *)
val plan_names : Core.Program.t -> (Names.GlobRef.t * string) list

(** The C++ name of each global the unit refers to, decided once
    {!plan_names} has named what it declares, in the order a walk of the
    structure meets them: every global a term, pattern, type or module
    specification names, the fields of a record a match takes apart, the
    constructors of an inductive a type names, and, under separate
    extraction, the field behind a promoted type variable another file
    declares.  Custom mappings included: a render asks for their names too,
    for a variant-shaped custom's constructor structs or a custom class's
    fields.  With these and {!plan_names} decided, rendering computes no
    global's name but a helper's lifted out of a body as it is generated. *)
val plan_referenced_names : Core.Program.t -> (Names.GlobRef.t * string) list

(** The C++ name of each module the unit declares, a functor's body's
    included, decided in declaration order ({!Base.Common.emitted_module_name}). *)
val plan_module_names : Core.Program.t -> (Names.ModPath.t * string) list

(** The C++ names of the fields of each constructor whose struct the unit
    generates -- an inductive's, not a class's or a
    record's, nor a custom type's -- decided from the binder names the
    constructor was declared with
    ({!Translation_naming.compute_and_register_field_names}), once the
    constructors' names are. *)
val plan_field_names : Core.Program.t -> (Names.GlobRef.t * Names.Id.t list) list

(** The inductives promoted to their eponymous module's struct, which the
    module's struct then is ({!Unit_plan.Context.t.promoted_inductives}): those of the
    modules outside a functor's body, which the implementation renders
    outside every struct, as the unit's context [u] plans its scopes. *)
val plan_promoted_inductives : Unit_plan.Context.t -> Core.Program.t -> Names.GlobRef.t list

(** The constants emitted as an accessor function returning a function-local
    static (a Meyers singleton), which a use spells as a call: one written in
    a template -- a functor's body, or a module promoted to its eponymous
    inductive's struct where that has parameters -- and, inside a module's
    struct, one that is a template itself, or any under separate extraction;
    each a constant its generation does not make a function.  [u] is the
    unit's context. *)
val plan_accessors : Translation_state.t -> Unit_plan.Context.t -> Core.Program.t -> Names.GlobRef.t list

(** The scope of each module the unit emits as a struct: how a definition of
    one of its members, written outside the struct's body, names the
    struct. *)
val plan_scopes : Translation_state.t -> Core.Program.t -> Core_plan.Scope_plan.t

(** The structs written inside another struct, each with the name it is
    written under: a module's, and an inductive's -- its struct or its enum
    -- declared in a module.  A global type of the same name is spelled
    [::name] where one of them would capture it, and a reference to one of
    them is qualified by its enclosing struct. *)
val plan_nested_structs :
  Translation_state.t -> Core.Program.t -> (string * Unit_plan.Cpp_state.nested_struct_owner) list

(** The concrete types each instance the unit declares gives its class's
    promoted variables ({!Gen_decls.instance_promoted_types}), which a call
    through it substitutes for them. *)
val plan_instance_promoted_types :
  Translation_state.t -> Core.Program.t -> (Names.GlobRef.t * (Names.Id.t * Core.Type.t) list) list

(** The wrapper structs that hold declarations of their module's -- its
    functions, generated as the wrapper's members -- and so cannot be merged
    with the eponymous inductive's struct: a reference to the inductive then
    spells the wrapper's member.  Decided from what the wrapper's module
    declares, before the header renders the members.  Each with the module
    it wraps. *)
val plan_unmerged_wrappers : Translation_state.t -> unit -> (string * Names.ModPath.t) list

(** [plan_concept_prerequisites plan s] is [plan] with the labels of the
    top-level elements of [s]'s files that the concepts at the top of the
    header cannot be read without, which move ahead of them.  Asked once the
    wrappers holding declarations are installed: whether an inductive is
    spelled qualified by its wrapper depends on them. *)
val plan_concept_prerequisites : Translation_state.t -> Core_plan.Module_plan.t -> Core.Program.t -> Core_plan.Module_plan.t

(** The fields each constructor struct of an inductive the unit generates
    stores behind the smart pointer
    ({!Gen_decls.constructor_pointer_fields}): the inductive, the
    constructor's struct name, and each field's index with whether it holds
    the inductive itself.  A flat inductive has no constructor struct. *)
val plan_pointer_fields :
  Translation_state.t -> Core.Program.t -> (Names.GlobRef.t * string * (int * bool) list) list
