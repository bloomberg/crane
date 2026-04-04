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

(** Mutable state and utility functions for C++ code generation.

    This module holds all global mutable state (render context, hashtables,
    refs) used across the C++ pretty-printer, along with small utility functions
    that depend on that state. Centralising state here avoids circular
    dependencies between the other cpp_* modules. *)

open Pp
open CErrors
open Names
open ModPath
open Table
open Miniml
open Modutil
open Common
open Minicpp

(** {2 Pp box shadows}

    Since all output is reformatted by clang-format, the Pp box-layout algorithm
    is wasted work. Shadow h/v/hov with identity to skip box construction while
    keeping the same Pp.t type. *)

(** Shadow horizontal box constructor with identity. *)
let h x = x

(** Shadow vertical box constructor with identity. *)
let v _ x = x

(** Shadow horizontal-or-vertical box constructor with identity. *)
let hov _ x = x

(** The method registry is created once per extraction pass by scanning the full
    ml_structure. It replaces the old global_method_registry and
    methods_returning_any hashtables. Queries go through get_method_registry().
*)
let method_registry : Method_registry.t option ref = ref None

(** Get the method registry, raising an anomaly if not initialized. *)
let get_method_registry () =
  match !method_registry with
  | Some r -> r
  | None -> CErrors.anomaly (Pp.str "method_registry not initialized.")

(** Pre-computed name resolution cache — populated once per extraction pass.
    Queries go through get_name_cache(). *)
let name_cache : Name_resolution.t option ref = ref None

(** Get the name cache, raising an anomaly if not initialized. *)
let get_name_cache () =
  match !name_cache with
  | Some c -> c
  | None -> CErrors.anomaly (Pp.str "name_cache not initialized.")

(** {2 Some utility functions.} *)

(** Pretty-print a type variable as a string. *)
let pp_tvar id = str (Id.to_string id)

(** Pretty-print type parameters as a boxed tuple with optional trailing space.
*)
let pp_parameters l = pp_boxed_tuple pp_tvar l ++ space_if (l <> [])

(** Pretty-print string parameters as a boxed tuple with optional trailing
    space. *)
let pp_string_parameters l = pp_boxed_tuple str l ++ space_if (l <> [])

(** Helper to get custom type mapping with ids, returning option *)
let find_type_custom_opt r =
  if is_custom r then
    (* Safe to call find_type_custom since is_custom returned true *)
    Some (find_type_custom r)
  else
    None

(** {2 C++ renaming issues.} *)

(** Set of C++ keywords and reserved identifiers that must be avoided. *)
let keywords =
  List.fold_right
    (fun s -> Id.Set.add (Id.of_string s))
    [
      (* C++ keywords *)
      "alignas";
      "alignof";
      "and";
      "and_eq";
      "asm";
      "auto";
      "bitand";
      "bitor";
      "bool";
      "break";
      "case";
      "catch";
      "char";
      "char8_t";
      "char16_t";
      "char32_t";
      "class";
      "compl";
      "concept";
      "const";
      "consteval";
      "constexpr";
      "constinit";
      "const_cast";
      "continue";
      "co_await";
      "co_return";
      "co_yield";
      "decltype";
      "default";
      "delete";
      "do";
      "double";
      "dynamic_cast";
      "else";
      "enum";
      "explicit";
      "export";
      "extern";
      "false";
      "float";
      "for";
      "friend";
      "goto";
      "if";
      "inline";
      "int";
      "long";
      "mutable";
      "namespace";
      "new";
      "noexcept";
      "not";
      "not_eq";
      "nullptr";
      "operator";
      "or";
      "or_eq";
      "private";
      "protected";
      "public";
      "register";
      "reinterpret_cast";
      "requires";
      "return";
      "short";
      "signed";
      "sizeof";
      "static";
      "static_assert";
      "static_cast";
      "struct";
      "switch";
      "template";
      "this";
      "thread_local";
      "throw";
      "true";
      "try";
      "typedef";
      "typeid";
      "typename";
      "union";
      "unsigned";
      "using";
      "virtual";
      "void";
      "volatile";
      "wchar_t";
      "while";
      "xor";
      "xor_eq";
      (* Reserved identifiers *)
      "_";
      "__";
    ]
    Id.Set.empty

(** Note: do not shorten [str "foo" ++ fnl ()] into [str "foo\n"], the '\n'
    character interacts badly with the Format boxing mechanism *)

(** Pretty-print an open directive for a module. *)
let pp_open mp = str ("open " ^ string_of_modfile mp) ++ fnl ()

(** Pretty-print a comment with OCaml-style delimiters. *)
let pp_comment s = str "(* " ++ hov 0 s ++ str " *)"

(** Pretty-print an optional header comment. *)
let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl2 ()

(** Add a newline after pp if it's non-empty. *)
let then_nl pp = if Pp.ismt pp then mt () else pp ++ fnl ()

(** Generate preamble for implementation files. *)
let preamble _ comment used_modules _usf =
  pp_header_comment comment ++ then_nl (prlist pp_open used_modules)

(** Generate preamble for signature/header files. *)
let sig_preamble _ comment _used_modules _usf = pp_header_comment comment

(** {2 The pretty-printer for C++ syntax} *)

(* ============================================================================
   Render context — mutable state tracking the rendering position. These refs
   are saved/restored around sub-renders using with_render_ctx.
   ============================================================================ *)

(** Consolidated render context state. All mutable rendering context in a single
    record instead of 5 separate refs. *)
type render_ctx = {
  (* Inside a struct body? Affects qualification of nested type references. *)
  mutable rc_in_struct : bool;
  (* TypeClass concepts already emitted for the current module? *)
  mutable rc_concepts_hoisted : bool;
  (* Current struct name for qualifying out-of-struct definitions *)
  mutable rc_struct_name : Pp.t option;
  (* Current struct's ModPath for ModPath-based qualification checks. Needed
     when the C++ struct name differs from the Rocq module path. *)
  mutable rc_struct_mp : ModPath.t option;
  (* Inside a template struct (functor)? Affects typename keyword insertion. *)
  mutable rc_in_template : bool;
}

(** Global render context state. *)
let render_ctx =
  {
    rc_in_struct = false;
    rc_concepts_hoisted = false;
    rc_struct_name = None;
    rc_struct_mp = None;
    rc_in_template = false;
  }

(** Accumulator for nested module type concepts that must be hoisted out of
    requires bodies *)
let hoisted_concept_defs : Pp.t list ref = ref []

(** Snapshot of render context state for save/restore. Using a record prevents
    individual fields from drifting out of sync across save/restore boundaries.
*)
type render_ctx_snapshot = {
  rcs_in_struct : bool;
  rcs_concepts_hoisted : bool;
  rcs_struct_name : Pp.t option;
  rcs_struct_mp : ModPath.t option;
  rcs_in_template : bool;
}

(** Save the current render context state. *)
let save_render_ctx () =
  {
    rcs_in_struct = render_ctx.rc_in_struct;
    rcs_concepts_hoisted = render_ctx.rc_concepts_hoisted;
    rcs_struct_name = render_ctx.rc_struct_name;
    rcs_struct_mp = render_ctx.rc_struct_mp;
    rcs_in_template = render_ctx.rc_in_template;
  }

(** Restore render context from a snapshot. *)
let restore_render_ctx s =
  render_ctx.rc_in_struct <- s.rcs_in_struct;
  render_ctx.rc_concepts_hoisted <- s.rcs_concepts_hoisted;
  render_ctx.rc_struct_name <- s.rcs_struct_name;
  render_ctx.rc_struct_mp <- s.rcs_struct_mp;
  render_ctx.rc_in_template <- s.rcs_in_template

(** Execute [f] with modified render context, restoring the snapshot afterward.
    This replaces the error-prone pattern of manually saving/restoring
    individual refs. *)
let with_render_ctx ~(setup : unit -> unit) (f : unit -> 'a) : 'a =
  let saved = save_render_ctx () in
  setup ();
  let result = f () in
  restore_render_ctx saved;
  result

(** Track definitions rendered as function accessors (Meyers singletons) instead
    of static inline variables, due to template static init ordering. Stores
    (functor_modpath, label) pairs. At call sites, we match by label and check
    if the caller's modpath corresponds to an application of the functor. This
    is needed because functor application creates new constants with distinct
    canonical names that can't be matched by GlobRef equality. *)
let template_static_accessors : (ModPath.t * Label.t) list ref = ref []

(** Maps applied module paths to their functor source modpaths. E.g.,
    NatWrapper's modpath -> Wrapper's modpath. Populated when processing
    MEapply. *)
let functor_app_sources : (ModPath.t, ModPath.t) Hashtbl.t = Hashtbl.create 16

(** Track eponymous type info for method generation. When a module M contains an
    inductive type m (lowercase of M), functions taking shared_ptr<m> as first
    arg become methods on m. *)
let eponymous_type_ref : GlobRef.t option ref = ref None

(** Set during module rendering when the eponymous inductive should be promoted
    into the module struct. cpp_ind.ml checks this to render fields flat instead
    of a wrapping struct. *)
let eponymous_promote_ref : GlobRef.t option ref = ref None

(** Accumulator for non-inductive definitions that should be emitted after the
    promoted template struct at file scope. *)
let eponymous_deferred : Pp.t ref = ref (Pp.mt ())

(** Set of promoted inductives — overrides is_merged_inductive for name
    resolution so that promoted types use the capitalized module name. *)
let promoted_inductives : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 4

(** Whether the promoted inductive needs enable_shared_from_this. Captured
    during flat rendering in cpp_ind.ml, consumed by the MEstruct wrapper in
    cpp.ml. *)
let eponymous_promote_sft : bool ref = ref false

(** Collected method candidates: (function_ref, body, type, this_position) for
    current eponymous type. this_position is the index (0-based) of the first
    argument that matches the eponymous type. *)
let method_candidates :
    (GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref =
  ref []

(** Eponymous record: when a module M contains a record with the same name
    (e.g., module CHT with record CHT), we merge the record fields into the
    module struct to avoid C++ name conflicts. Stores: (record_ref, field_refs,
    ind_packet) *)
let eponymous_record :
    (GlobRef.t * GlobRef.t option list * Miniml.ml_ind_packet) option ref =
  ref None

(* NOTE: The global method registry has moved to Method_registry. Lookups go
   through get_method_registry(). *)

(** Resolved standard library names — computed once per extraction pass from
    Table.std_lib() and queried everywhere instead of 20+ scattered checks. *)
type std_names = {
  shared_ptr : string; (* "std::shared_ptr" or "bsl::shared_ptr" *)
  unique_ptr : string; (* "std::unique_ptr" or "bsl::unique_ptr" *)
  make_shared : string; (* "std::make_shared" or "bsl::make_shared" *)
  make_unique : string; (* "std::make_unique" or "bsl::make_unique" *)
  visit : string; (* "std::visit" or "bsl::visit" *)
  move : string; (* "std::move" or "bsl::move" *)
  forward : string; (* "std::forward" or "bsl::forward" *)
  any_cast : string; (* "std::any_cast" or "bsl::any_cast" *)
  logic_error : string; (* "std::logic_error" or "bsl::logic_error" *)
  overloaded : string; (* "Overloaded" or "bdlf::Overloaded" *)
  ns : string; (* "std" or "bsl" — general prefix *)
  str_suffix : string; (* "s" or "_s" — string literal suffix *)
  same_as : string; (* "std::same_as" or "same_as" *)
  declval : string; (* "std::declval" or "bsl::declval" *)
  convertible_to : string; (* "std::convertible_to" or "convertible_to" *)
}

(** Global reference to standard library names, initialized by init_std_names.
*)
let std_names : std_names ref =
  ref
    {
      shared_ptr = "std::shared_ptr";
      unique_ptr = "std::unique_ptr";
      make_shared = "std::make_shared";
      make_unique = "std::make_unique";
      visit = "std::visit";
      move = "std::move";
      forward = "std::forward";
      any_cast = "std::any_cast";
      logic_error = "std::logic_error";
      overloaded = "Overloaded";
      ns = "std";
      str_suffix = "s";
      same_as = "std::same_as";
      declval = "std::declval";
      convertible_to = "std::convertible_to";
    }

(** Create a std_names record with the given prefix. *)
let mk_std_names prefix =
  match prefix with
  | "bsl::" ->
    {
      shared_ptr = prefix ^ "shared_ptr";
      unique_ptr = prefix ^ "unique_ptr";
      make_shared = prefix ^ "make_shared";
      make_unique = prefix ^ "make_unique";
      visit = prefix ^ "visit";
      move = prefix ^ "move";
      forward = prefix ^ "forward";
      any_cast = prefix ^ "any_cast";
      logic_error = prefix ^ "logic_error";
      overloaded = "bdlf::Overloaded";
      ns = "bsl";
      str_suffix = "_s";
      same_as = "same_as";
      declval = prefix ^ "declval";
      convertible_to = "convertible_to";
    }
  | _ ->
    (* Default to "std::" *)
    {
      shared_ptr = "std::shared_ptr";
      unique_ptr = "std::unique_ptr";
      make_shared = "std::make_shared";
      make_unique = "std::make_unique";
      visit = "std::visit";
      move = "std::move";
      forward = "std::forward";
      any_cast = "std::any_cast";
      logic_error = "std::logic_error";
      overloaded = "Overloaded";
      ns = "std";
      str_suffix = "s";
      same_as = "std::same_as";
      declval = "std::declval";
      convertible_to = "std::convertible_to";
    }

(** Initialize standard library names based on Table.std_lib() setting. *)
let init_std_names () =
  if Table.std_lib () = "BDE" then
    std_names := mk_std_names "bsl::"
  else
    std_names := mk_std_names "std::"

(** Short accessor for current standard library names. *)
let sn () = !std_names

(** Inline check: is a term a typeclass instance? Replaces
    is_typeclass_instance. A term is a typeclass instance if its return type is
    a Tglob referencing a typeclass. *)
let is_typeclass_instance _body ty =
  let rec return_type = function
    | Miniml.Tarr (_, rest) -> return_type rest
    | t -> t
  in
  match return_type ty with
  | Miniml.Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false

(** Wrapper module table: maps ModPath.t of imported modules to their
   wrapper struct name. When a module like Stdlib.Init.Nat is wrapped
   in 'struct Nat { ... }', this table records the mapping so that
   references to functions in that module get properly qualified. *)
let wrapper_module_table : (ModPath.t, string) Hashtbl.t = Hashtbl.create 16

(** Collision wrapper table: tracks modpaths that were registered as
    collision-wrapped (i.e., a child module whose name collides with a global
    inductive, wrapped into a parent struct). For these, wrapper_qualify_name
    strips the child qualifier. *)
let collision_wrapper_table : (ModPath.t, unit) Hashtbl.t = Hashtbl.create 16

(** Global-scope enum table: tracks enum inductives that were rendered at global
    scope (not inside any struct). Used to avoid incorrect struct qualification
    in .cpp files. *)
let global_scope_enum_table : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 16

(** Pending wrapper declarations: maps a Dnspace struct name (e.g., "Nat") to
    pre-rendered forward declarations (specs) that should be injected into that
    struct. Full definitions are rendered separately in PASS 3 after all types
    are defined. Populated during do_struct_with_decl_tracking PASS 1. Consumed
    during Dnspace rendering in PASS 2. *)
let pending_wrapper_decls : (string, Pp.t) Hashtbl.t = Hashtbl.create 16

(** Set of wrapper struct names that have pending declarations and thus cannot
    be merged. Populated alongside pending_wrapper_decls during PASS 1. Used
    during type/expression rendering to decide between merged (List<A>) and
    unmerged (List::list<A>) name formats. Not consumed during rendering. *)
let unmerged_wrappers : (string, unit) Hashtbl.t = Hashtbl.create 16

(** Maps capitalized inductive names to their ModPaths across all modules.
    Pre-populated in do_struct_with_decl_tracking before code generation. Used
    to detect module-inductive name collisions (e.g., N/Z appearing as both an
    inductive from BinNums and a module from BinNat). *)
let global_inductive_names : (string, ModPath.t) Hashtbl.t = Hashtbl.create 16

(** Check if a GlobRef belongs to a wrapper module and return the qualified
    name. If the reference's module path matches a wrapper module, prepend the
    struct name. Only qualify ConstRef globals (actual Rocq constants from
    modules). VarRef globals are lifted declarations (like _foo_aux) that should
    not be qualified with a wrapper struct name — their modpath comes from
    Lib.make_kn which reflects the current library, not the wrapper module. *)
let wrapper_qualify_name (r : GlobRef.t) (name : string) : string =
  match r with
  | GlobRef.VarRef _ -> name (* Lifted declarations: never qualify *)
  | _ ->
    let mp = modpath_of_r r in
    ( match Hashtbl.find_opt wrapper_module_table mp with
    | Some struct_name when not (String.contains name ':') ->
      struct_name ^ "::" ^ name
    | Some struct_name when String.contains name ':' ->
      (* Name is already qualified (e.g., "N::add" from visibility stack). Only
         strip the child qualifier for collision-wrapped entries (e.g., BinNat
         wrapping N). For normal wrappers (e.g., List wrapping list), keep the
         full qualification. *)
      if Hashtbl.mem collision_wrapper_table mp then
        match
          String.index_opt name ':'
        with
        | Some colon_pos
          when colon_pos > 0
               && colon_pos + 1 < String.length name
               && name.[colon_pos + 1] = ':' ->
          let func_part =
            String.sub name (colon_pos + 2) (String.length name - colon_pos - 2)
          in
          struct_name ^ "::" ^ func_part
        | _ -> name
      else
        name
    | _ -> name )

(** Register a method with the method registry. *)
let register_method
    (func_ref : GlobRef.t)
    (epon_ref : GlobRef.t)
    (this_pos : int)
    ?(ind_tvar_positions : int list = [])
    () =
  Method_registry.register_method
    (get_method_registry ())
    func_ref
    epon_ref
    this_pos
    ~ind_tvar_positions

(** Check if a function is registered as a method, returning its eponymous type
    and this position if so. *)
let is_registered_method (func_ref : GlobRef.t) : (GlobRef.t * int) option =
  Method_registry.is_registered_method (get_method_registry ()) func_ref

(** Look up the inductive's type variable positions (0-based indices into the
    function's tys list) for a registered method. These positions correspond to
    the inductive's template params which are already deducible from the
    receiver object and should be omitted from explicit template arguments in
    method calls. *)
let lookup_method_ind_tvar_positions (func_ref : GlobRef.t) : int list =
  Method_registry.lookup_ind_tvar_positions (get_method_registry ()) func_ref

(** Register that a method returns std::any or bsl::any. *)
let register_method_returns_any (func_ref : GlobRef.t) =
  Method_registry.register_method_returns_any (get_method_registry ()) func_ref

(** Check if a method is registered as returning std::any or bsl::any. *)
let method_returns_any (func_ref : GlobRef.t) : bool =
  Method_registry.method_returns_any (get_method_registry ()) func_ref

(** Global registry of eponymous records. When a module M contains a record with
    the same name (e.g., module CHT with record CHT), the record fields are
    merged directly into the module struct. This avoids C++ name conflicts where
    both the module and record would have the same name.

    This registry is global (not per-module) because type references from OTHER
    modules need to know how to render the type name. Without this registry, a
    reference to CHT from another module would incorrectly generate "CHT::cHT"
    instead of just "CHT".

    See also: pp_inductive_type_name which uses this registry for type name
    rendering. *)
let global_eponymous_record_registry : (GlobRef.t, unit) Hashtbl.t =
  Hashtbl.create 100

(** Register a record as eponymous with its containing module. *)
let register_eponymous_record (record_ref : GlobRef.t) =
  Hashtbl.replace global_eponymous_record_registry record_ref ()

(** Check if a GlobRef is registered as an eponymous record. *)
let is_eponymous_record_global (r : GlobRef.t) : bool =
  Hashtbl.mem global_eponymous_record_registry r

(** Check if a constant (function) is inside an eponymous template module.
    Returns Some record_ref if the function is inside a module whose name
    matches a registered eponymous record. This is used to correctly generate
    StructName<Args>::funcName() instead of StructName::funcName<Args>(). *)
let get_containing_eponymous_struct (r : GlobRef.t) : GlobRef.t option =
  match r with
  | GlobRef.ConstRef kn ->
    (* Get the module path containing this constant *)
    let mp = Names.Constant.modpath kn in
    (* Check if there's an eponymous record whose module path matches *)
    let result = ref None in
    Hashtbl.iter
      (fun record_ref () ->
        let record_mp =
          match record_ref with
          | GlobRef.IndRef (ind, _) -> Names.MutInd.modpath ind
          | _ -> mp (* Won't match *)
        in
        (* Check if the constant is in the same module as the record *)
        if ModPath.equal mp record_mp then result := Some record_ref )
      global_eponymous_record_registry;
    !result
  | _ -> None

(** Track current structure's declarations for finding methods from sibling
    modules. When processing a module like List inside tree.v, we need to also
    scan sibling declarations (like app) that are from the same Rocq module. *)
let current_structure_decls : (Label.t * Miniml.ml_structure_elem) list ref =
  ref []

(** Track which standard library headers are needed by the generated code.
    Populated during the Pre-phase dry run; read by extract_env.ml to emit
    only necessary #include directives. *)
module SSet = Set.Make (String)

let needed_headers : SSet.t ref = ref SSet.empty

let require_header h = needed_headers := SSet.add h !needed_headers

let get_needed_headers () = SSet.elements !needed_headers

let reset_needed_headers () = needed_headers := SSet.empty

(** Reset ALL global state - must be called between extractions to avoid
    pollution. This prevents state from one extraction affecting another when
    running multiple extractions in the same process (e.g., during 'dune
    build'). *)
let reset_cpp_state () =
  render_ctx.rc_in_struct <- false;
  render_ctx.rc_concepts_hoisted <- false;
  render_ctx.rc_struct_name <- None;
  render_ctx.rc_struct_mp <- None;
  render_ctx.rc_in_template <- false;
  Doc_comments.reset ();
  eponymous_type_ref := None;
  eponymous_promote_ref := None;
  eponymous_deferred := Pp.mt ();
  Hashtbl.clear promoted_inductives;
  eponymous_promote_sft := false;
  eponymous_record := None;
  method_candidates := [];
  current_structure_decls := [];
  method_registry := None;
  name_cache := None;
  Hashtbl.clear global_eponymous_record_registry;
  Hashtbl.clear wrapper_module_table;
  Hashtbl.clear collision_wrapper_table;
  Hashtbl.clear global_scope_enum_table;
  Hashtbl.clear pending_wrapper_decls;
  Hashtbl.clear unmerged_wrappers;
  Hashtbl.clear global_inductive_names;
  template_static_accessors := [];
  Hashtbl.clear functor_app_sources;
  hoisted_concept_defs := [];
  Common.reset_ctor_field_names ();
  reset_needed_headers ();
  Table.reset_itree_header ();
  Table.reset_main_function ()

(** Check if a function is a projection for the eponymous record. Such
    projections are redundant when the record fields are merged into the module
    struct. *)
let is_eponymous_record_projection r =
  match !eponymous_record with
  | None -> false
  | Some (epon_ref, _, _) ->
    if Table.is_projection r then
      let ip, _arity = Table.projection_info r in
      (* Check if this projection's inductive matches the eponymous record *)
      Environ.QGlobRef.equal Environ.empty_env (GlobRef.IndRef ip) epon_ref
    else
      false

(** Check if a projection should be suppressed (not rendered as higher-order).
*)
let is_suppressed_projection r =
  Table.is_projection r && not (Table.is_higher_order_projection r)

(** Filter a Dfix group, removing entries that are inline customs, method
    candidates (local or globally registered), eponymous record projections, or
    suppressed projections. Returns the three filtered arrays (refs, bodies,
    types). *)
let filter_dfix rv defs typs =
  let is_method_candidate x =
    List.exists
      (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env x r')
      !method_candidates
  in
  let is_global_method x = is_registered_method x <> None in
  let filter =
    Array.to_list
      (Array.map
         (fun x ->
           (not (is_inline_custom x))
           && (not (is_method_candidate x))
           && (not (is_global_method x))
           && (not (is_eponymous_record_projection x))
           && not (is_suppressed_projection x) )
         rv )
  in
  let filter_array mask arr =
    let lst = Array.to_list arr in
    let filtered =
      List.filter_map
        (fun (keep, x) -> if keep then Some x else None)
        (List.combine mask lst)
    in
    Array.of_list filtered
  in
  (filter_array filter rv, filter_array filter defs, filter_array filter typs)
