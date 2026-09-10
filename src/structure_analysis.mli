(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** {1 Structure Analysis}

    Pre-analyzes the full [ml_structure] before any C++ rendering begins. This
    is the second pass in Crane's multi-pass extraction pipeline (after
    {!Method_registry}).

    The analysis performs four tasks:
    + {b Enum registration.} Identifies inductives whose constructors are all
      nullary and have no type parameters. These are rendered as [enum class] in
      C++ rather than the usual [std::variant]-based struct. Results are
      registered in {!Table} via [Table.add_enum_inductive] so the rest of the
      pipeline can query them.
    + {b Inductive name collection.} Builds a list of
      [(capitalized_name, defining_modpath)] pairs for every inductive in the
      structure. Used by [cpp.ml] for name collision detection: if a wrapper
      module has the same name as an inductive from a different module, the
      wrapper must use a disambiguated name.
    + {b Global-scope enum collection.} After enum registration, identifies
      which enums appear at global scope (i.e. as top-level [SEdecl] entries
      rather than inside sub-modules). These are emitted before any wrapper
      modules or the main module.
    + {b Module classification and topological sort.} Classifies each top-level
      module as either a "wrapper module" (a simple module containing only
      declarations, no sub-modules — suitable for wrapping in a C++ struct) or a
      regular module. Then topologically sorts all non-main modules by their
      cross-module dependencies so that definitions appear before uses. The main
      module (the last one in the structure) is always emitted last.

    {2 Relationship to other modules}

    - Runs {i after} {!Method_registry.create}, because the topological sort
      needs to know about method registrations to correctly model cross-module
      dependencies (a function that calls a method on a type from another module
      depends on that module).
    - Runs {i before} [cpp.ml]'s rendering pass, which consumes the {!t} result
      to iterate over modules in the correct order.
    - The enum registration side-effect ([Table.add_enum_inductive]) is also
      needed by {!Method_registry}, which is why enum detection also happens
      during the method registry pass (for inductives encountered before this
      analysis runs). *)

open Names
open Miniml

(** Per-module analysis result. *)
type module_info = {
  modpath : ModPath.t;  (** The Rocq module path for this module. *)
  sels : (Label.t * ml_structure_elem) list;
      (** The module's declaration list (labels and structure elements). This is
          the same list that appears in the original [ml_structure], preserved
          here so that [cpp.ml] can iterate over it without re-extracting from
          the original structure. *)
  wrapper_name : string option;
      (** If this module should be wrapped in a C++ struct, [Some name] gives
          the capitalized wrapper struct name (e.g. ["List"] for the [list]
          module). [None] if the module should not be wrapped — either because
          it contains sub-modules, or because it is the main module, or because
          it lacks function declarations.

          A module qualifies as a wrapper when:
          - It contains at least one function declaration ([Dterm] or [Dfix]),
          - All its entries are bare declarations (no [SEmodule] or [SEmodtype]
            children),
          - It is a file-level module ([is_modfile mp]),
          - It is not the main module. *)
  is_main : bool;
      (** Whether this is the main module (the one being extracted). The main
          module is always last in the sorted order and is not wrapped — its
          declarations are emitted directly. *)
}

(** Complete analysis result returned by {!analyze}. *)
type t = {
  sorted_modules : module_info list;
      (** All modules from the structure, topologically sorted so that
          dependencies come before dependents. The main module is always last.

          The sort uses Kahn's algorithm on a dependency graph built by scanning
          each module's declarations for references to other modules. If a cycle
          is detected, the original order is preserved as a fallback. *)
  inductive_names : (string * ModPath.t) list;
      (** [(capitalized_name, defining_modpath)] for every inductive type in the
          structure. Used by [cpp.ml] to detect name collisions between wrapper
          modules and inductives from other modules.

          For example, if module [Nat] defines inductive [nat] and module [Tree]
          also has a type called [Nat], the rendering needs to disambiguate. *)
  global_scope_enums : GlobRef.t list;
      (** Enum inductives that appear at global scope (top-level [SEdecl]
          entries). These are emitted as [enum class] declarations before any
          wrapper modules or the main module, ensuring they are available for
          use in all subsequent declarations.

          Enums inside sub-modules are emitted within their containing module's
          scope instead. *)
  collision_wrappers : (ModPath.t * string) list;
      (** [(modpath, wrapper_struct_name)] for every module path that a name
          collision forces inside a parent wrapper struct: a child module whose
          capitalised name is already taken by an inductive from elsewhere, that
          child's body, and each of its declarations.

          This is layout, and so belongs here rather than in the printer: the
          name resolver is built from it before rendering begins, and a table
          the printer went on adding to would be one the resolver had already
          read. *)
}

(** Perform all structure analysis in a single pass.

    This is the main entry point, called once from [cpp.ml] at the start of
    [do_struct_with_decl_tracking], immediately after creating the
    {!Method_registry}.

    Side effects:
    - Calls [Table.add_enum_inductive] for each detected enum.

    @param method_registry
      Used by the topological sort to detect cross-module dependencies arising
      from method calls. When a function calls a method on a type from another
      module, there is an implicit dependency on the module that defines the
      type (because the method is emitted inside that module's struct).
    @param ml_structure The full extraction structure to analyze.
    @return Analysis results consumed by [cpp.ml]'s rendering pass. *)
val analyze : Method_registry.t -> ml_structure -> t
