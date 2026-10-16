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

(** {1 C++ Pretty-Printer}

    Final stage of the extraction pipeline:
    {v MiniCpp AST  --[cpp.ml]-->  C++ source code v}

    Converts {!Minicpp} AST nodes into C++ syntax using the {!Pp}
    pretty-printing combinators. Lower-level rendering is delegated to:
    - {!Cpp_state} — mutable state and utilities
    - {!Cpp_names} — name resolution and qualification
    - {!Cpp_print} — type/expr/stmt/field/declaration pretty-printing
    - {!Cpp_ind} — inductive type rendering and decl-level dispatch *)

(** Language descriptor for C++. Provides the preamble, file suffix,
    pretty-printers, and other hooks that {!Extract_env} needs to drive a full
    extraction pass. *)
val cpp_descr : Miniml.language_descr

(** Decide the unit's layout before either file is rendered: analyse the
    structure ({!Structure_analysis}), record what rendering reads of the
    analysis, and return the {!Module_plan} it decides, which is not yet
    installed. *)
val prepare_structure : Miniml.ml_structure -> Module_plan.t

(** The callable plan of each function the renders will generate, in the
    order of the unit's modules and declarations, or the reverse if
    [reversed]; planned once the plan {!prepare_structure} returns is
    installed, and before anything is rendered.  A function no render generates -- a method, a projection, an
    inline custom -- has none.  With them, the plans of each instance's
    struct's methods, by name. *)
val plan_callables :
  ?reversed:bool ->
  Miniml.ml_structure ->
  Callable_abi.t list * (Names.GlobRef.t * (Names.Id.t * Callable_abi.t) list) list

(** Generate every function the renders write, before either file is
    rendered, for both files ({!Cpp_ind.generating_ahead}). *)
val generate_ahead : Miniml.ml_structure -> unit

(** Generate the functions one declaration is written as, before it is
    rendered in the module at the top of the visibility stack: the walk
    {!generate_ahead} would make for a structure holding only it. *)
val generate_decl_ahead : Miniml.ml_decl -> unit

(** The C++ name of each global the unit declares, a functor's body
    included, decided in declaration order ({!Common.pp_global_name}): an
    inductive's, then its constructors', then a record's fields, at the kind
    a declaration is printed at.  A custom mapping's name is its text, and is
    not among them. *)
val plan_names : Miniml.ml_structure -> (Names.GlobRef.t * string) list

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
val plan_referenced_names : Miniml.ml_structure -> (Names.GlobRef.t * string) list

(** The C++ name of each module the unit declares, a functor's body's
    included, decided in declaration order ({!Common.emitted_module_name}). *)
val plan_module_names : Miniml.ml_structure -> (Names.ModPath.t * string) list

(** The C++ names of the fields of each constructor whose struct the unit
    generates -- an inductive's, not a class's or a
    record's, nor a custom type's -- decided from the binder names the
    constructor was declared with
    ({!Translation_support.compute_and_register_field_names}), once the
    constructors' names are. *)
val plan_field_names : Miniml.ml_structure -> (Names.GlobRef.t * Names.Id.t list) list

(** The inductives promoted to their eponymous module's struct, which the
    module's struct then is ({!Table.promote_inductive}): those of the
    modules outside a functor's body, which the implementation renders
    outside every struct. *)
val plan_promoted_inductives : Miniml.ml_structure -> Names.GlobRef.t list

(** The constants emitted as an accessor function returning a function-local
    static (a Meyers singleton), which a use spells as a call: one written in
    a template -- a functor's body, or a module promoted to its eponymous
    inductive's struct where that has parameters -- and, inside a module's
    struct, one that is a template itself, or any under separate extraction;
    each a constant its generation does not make a function. *)
val plan_accessors : Miniml.ml_structure -> Names.GlobRef.t list

(** The scope of each module the unit emits as a struct: how a definition of
    one of its members, written outside the struct's body, names the
    struct. *)
val plan_scopes : Miniml.ml_structure -> Scope_plan.t

(** The structs written inside another struct, each with the name it is
    written under: a module's, and an inductive's -- its struct or its enum
    -- declared in a module.  A global type of the same name is spelled
    [::name] where one of them would capture it, and a reference to one of
    them is qualified by its enclosing struct. *)
val plan_nested_structs :
  Miniml.ml_structure -> (string * Cpp_state.nested_struct_owner) list

(** The concrete types each instance the unit declares gives its class's
    promoted variables ({!Gen_decls.instance_promoted_types}), which a call
    through it substitutes for them. *)
val plan_instance_promoted_types :
  Miniml.ml_structure -> (Names.GlobRef.t * (Names.Id.t * Miniml.ml_type) list) list

(** The wrapper structs that hold declarations of their module's -- its
    functions, generated as the wrapper's members -- and so cannot be merged
    with the eponymous inductive's struct: a reference to the inductive then
    spells the wrapper's member.  Decided from what the wrapper's module
    declares, before the header renders the members. *)
val plan_unmerged_wrappers : unit -> string list

(** The fields each such constructor struct stores behind the smart pointer
    ({!Gen_decls.constructor_pointer_fields}): the inductive, the
    constructor's struct name, and each field's index with whether it holds
    the inductive itself.  A flat inductive has no constructor struct. *)
val plan_pointer_fields :
  Miniml.ml_structure -> (Names.GlobRef.t * string * (int * bool) list) list
