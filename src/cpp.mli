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
    inline custom -- has none. *)
val plan_callables : ?reversed:bool -> Miniml.ml_structure -> Callable_abi.t list

(** The C++ name of each global the unit declares, a functor's body
    included, decided in declaration order ({!Common.pp_global_name}): an
    inductive's, then its constructors', then a record's fields, at the kind
    a declaration is printed at.  A custom mapping's name is its text, and is
    not among them. *)
val plan_names : Miniml.ml_structure -> (Names.GlobRef.t * string) list

(** The C++ names of the fields of each constructor whose struct the unit
    generates -- an inductive's, not a class's or a
    record's, nor a custom type's -- decided from the binder names the
    constructor was declared with
    ({!Translation_support.compute_and_register_field_names}), once the
    constructors' names are. *)
val plan_field_names : Miniml.ml_structure -> (Names.GlobRef.t * Names.Id.t list) list

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
