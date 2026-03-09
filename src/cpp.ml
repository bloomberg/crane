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

(*s Production of C++ syntax. *)

open Pp
open CErrors
open Util
open Names
open ModPath
open Table
open Miniml
open Mlutil
open Modutil
open Common
open Minicpp
open Translation


(* The method registry is created once per extraction pass by scanning the full
   ml_structure. It replaces the old global_method_registry and methods_returning_any
   hashtables. Queries go through get_method_registry(). *)
let method_registry : Method_registry.t option ref = ref None

let get_method_registry () =
  match !method_registry with
  | Some r -> r
  | None -> failwith "method_registry not initialized"

(* Pre-computed name resolution cache — populated once per extraction pass.
   Queries go through get_name_cache(). *)
let name_cache : Name_resolution.t option ref = ref None

let get_name_cache () =
  match !name_cache with
  | Some c -> c
  | None -> failwith "name_cache not initialized"


(*s Some utility functions. *)

let pp_tvar id = str (Id.to_string id)

let pp_parameters l =
  (pp_boxed_tuple pp_tvar l ++ space_if (not (List.is_empty l)))

let pp_string_parameters l =
  (pp_boxed_tuple str l ++ space_if (not (List.is_empty l)))

(*s C++ renaming issues. *)

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ (* C++ keywords *)
    "alignas"; "alignof"; "and"; "and_eq"; "asm"; "auto"; "bitand";
    "bitor"; "bool"; "break"; "case"; "catch"; "char"; "char8_t";
    "char16_t"; "char32_t"; "class"; "compl"; "concept"; "const";
    "consteval"; "constexpr"; "constinit"; "const_cast"; "continue";
    "co_await"; "co_return"; "co_yield"; "decltype"; "default";
    "delete"; "do"; "double"; "dynamic_cast"; "else"; "enum";
    "explicit"; "export"; "extern"; "false"; "float"; "for"; "friend";
    "goto"; "if"; "inline"; "int"; "long"; "mutable"; "namespace";
    "new"; "noexcept"; "not"; "not_eq"; "nullptr"; "operator"; "or";
    "or_eq"; "private"; "protected"; "public"; "register";
    "reinterpret_cast"; "requires"; "return"; "short"; "signed";
    "sizeof"; "static"; "static_assert"; "static_cast"; "struct";
    "switch"; "template"; "this"; "thread_local"; "throw"; "true";
    "try"; "typedef"; "typeid"; "typename"; "union"; "unsigned";
    "using"; "virtual"; "void"; "volatile"; "wchar_t"; "while";
    "xor"; "xor_eq";
    (* Reserved identifiers *)
    "_" ; "__" ]
  Id.Set.empty

(* Note: do not shorten [str "foo" ++ fnl ()] into [str "foo\n"],
   the '\n' character interacts badly with the Format boxing mechanism *)

let pp_open mp = str ("open "^ string_of_modfile mp) ++ fnl ()

let pp_comment s = str "(* " ++ hov 0 s ++ str " *)"

let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl2 ()

let then_nl pp = if Pp.ismt pp then mt () else pp ++ fnl ()

let preamble _ comment used_modules usf =
  pp_header_comment comment ++
  then_nl (prlist pp_open used_modules) (* ++
  then_nl (pp_tdummy usf ++ pp_mldummy usf) *)

let sig_preamble _ comment used_modules usf =
  pp_header_comment comment (* ++
  then_nl (pp_tdummy usf) *)

(*s The pretty-printer for C++ syntax*)

(* ============================================================================
   Render context — mutable state tracking the rendering position.
   These refs are saved/restored around sub-renders using with_render_ctx.
   ============================================================================ *)

(* Inside a struct body? Affects qualification of nested type references. *)
let in_struct_context = ref false
(* TypeClass concepts already emitted for the current module? *)
let concepts_hoisted = ref false
(* Current struct name for qualifying out-of-struct definitions *)
let current_struct_name : Pp.t option ref = ref None
(* Current struct's ModPath for ModPath-based qualification checks.
   Needed when the C++ struct name differs from the Rocq module path. *)
let current_struct_mp : ModPath.t option ref = ref None
(* Inside a template struct (functor)? Affects typename keyword insertion. *)
let in_template_struct = ref false

(* Snapshot of render context state for save/restore.
   Using a record prevents individual fields from drifting out of sync
   across save/restore boundaries. *)
type render_ctx_snapshot = {
  rcs_in_struct : bool;
  rcs_concepts_hoisted : bool;
  rcs_struct_name : Pp.t option;
  rcs_struct_mp : ModPath.t option;
  rcs_in_template : bool;
}

let save_render_ctx () = {
  rcs_in_struct = !in_struct_context;
  rcs_concepts_hoisted = !concepts_hoisted;
  rcs_struct_name = !current_struct_name;
  rcs_struct_mp = !current_struct_mp;
  rcs_in_template = !in_template_struct;
}

let restore_render_ctx s =
  in_struct_context := s.rcs_in_struct;
  concepts_hoisted := s.rcs_concepts_hoisted;
  current_struct_name := s.rcs_struct_name;
  current_struct_mp := s.rcs_struct_mp;
  in_template_struct := s.rcs_in_template

(* Execute [f] with modified render context, restoring the snapshot afterward.
   This replaces the error-prone pattern of manually saving/restoring individual refs. *)
let with_render_ctx ~(setup : unit -> unit) (f : unit -> 'a) : 'a =
  let saved = save_render_ctx () in
  setup ();
  let result = f () in
  restore_render_ctx saved;
  result
(* Track definitions rendered as function accessors (Meyers singletons)
   instead of static inline variables, due to template static init ordering.
   Stores (functor_modpath, label) pairs. At call sites, we match by label
   and check if the caller's modpath corresponds to an application of the
   functor. This is needed because functor application creates new constants
   with distinct canonical names that can't be matched by GlobRef equality. *)
let template_static_accessors : (ModPath.t * Label.t) list ref = ref []
(* Maps applied module paths to their functor source modpaths.
   E.g., NatWrapper's modpath → Wrapper's modpath.
   Populated when processing MEapply. *)
let functor_app_sources : (ModPath.t, ModPath.t) Hashtbl.t = Hashtbl.create 16
(* Track eponymous type info for method generation.
   When a module M contains an inductive type m (lowercase of M),
   functions taking shared_ptr<m> as first arg become methods on m. *)
let eponymous_type_ref : GlobRef.t option ref = ref None
(* Collected method candidates: (function_ref, body, type, this_position) for current eponymous type.
   this_position is the index (0-based) of the first argument that matches the eponymous type. *)
let method_candidates : (GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref = ref []

(* Eponymous record: when a module M contains a record with the same name (e.g., module CHT with record CHT),
   we merge the record fields into the module struct to avoid C++ name conflicts.
   Stores: (record_ref, field_refs, ind_packet) *)
let eponymous_record : (GlobRef.t * GlobRef.t option list * Miniml.ml_ind_packet) option ref = ref None

(* NOTE: The global method registry has moved to Method_registry.
   Lookups go through get_method_registry(). *)

(* Resolved standard library names — computed once per extraction pass
   from Table.std_lib() and queried everywhere instead of 20+ scattered checks. *)
type std_names = {
  shared_ptr : string;     (* "std::shared_ptr" or "bsl::shared_ptr" *)
  unique_ptr : string;     (* "std::unique_ptr" or "bsl::unique_ptr" *)
  make_shared : string;    (* "std::make_shared" or "bsl::make_shared" *)
  make_unique : string;    (* "std::make_unique" or "bsl::make_unique" *)
  visit : string;          (* "std::visit" or "bsl::visit" *)
  move : string;           (* "std::move" or "bsl::move" *)
  forward : string;        (* "std::forward" or "bsl::forward" *)
  any_cast : string;       (* "std::any_cast" or "bsl::any_cast" *)
  logic_error : string;    (* "std::logic_error" or "bsl::logic_error" *)
  overloaded : string;     (* "Overloaded" or "bdlf::Overloaded" *)
  ns : string;             (* "std" or "bsl" — general prefix *)
  str_suffix : string;     (* "s" or "_s" — string literal suffix *)
  same_as : string;        (* "std::same_as" or "same_as" *)
  declval : string;        (* "std::declval" or "bsl::declval" *)
  convertible_to : string; (* "std::convertible_to" or "convertible_to" *)
}

let std_names : std_names ref = ref {
  shared_ptr = "std::shared_ptr"; unique_ptr = "std::unique_ptr";
  make_shared = "std::make_shared"; make_unique = "std::make_unique";
  visit = "std::visit"; move = "std::move"; forward = "std::forward";
  any_cast = "std::any_cast";
  logic_error = "std::logic_error"; overloaded = "Overloaded";
  ns = "std"; str_suffix = "s";
  same_as = "std::same_as"; declval = "std::declval";
  convertible_to = "std::convertible_to";
}

let init_std_names () =
  if Table.std_lib () = "BDE" then
    std_names := {
      shared_ptr = "bsl::shared_ptr"; unique_ptr = "bsl::unique_ptr";
      make_shared = "bsl::make_shared"; make_unique = "bsl::make_unique";
      visit = "bsl::visit"; move = "bsl::move"; forward = "bsl::forward";
      any_cast = "bsl::any_cast";
      logic_error = "bsl::logic_error"; overloaded = "bdlf::Overloaded";
      ns = "bsl";
      str_suffix = "_s"; same_as = "same_as"; declval = "bsl::declval";
      convertible_to = "convertible_to";
    }
  else
    std_names := {
      shared_ptr = "std::shared_ptr"; unique_ptr = "std::unique_ptr";
      make_shared = "std::make_shared"; make_unique = "std::make_unique";
      visit = "std::visit"; move = "std::move"; forward = "std::forward";
      any_cast = "std::any_cast";
      logic_error = "std::logic_error"; overloaded = "Overloaded";
      ns = "std"; str_suffix = "s";
      same_as = "std::same_as"; declval = "std::declval";
      convertible_to = "std::convertible_to";
    }

let sn () = !std_names

(* Inline check: is a term a typeclass instance? Replaces is_typeclass_instance.
   A term is a typeclass instance if its return type is a Tglob referencing a typeclass. *)
let is_typeclass_instance _body ty =
  let rec return_type = function
    | Miniml.Tarr (_, rest) -> return_type rest
    | t -> t
  in
  match return_type ty with
  | Miniml.Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false

(* Wrapper module table: maps ModPath.t of imported modules to their
   wrapper struct name. When a module like Stdlib.Init.Nat is wrapped
   in 'struct Nat { ... }', this table records the mapping so that
   references to functions in that module get properly qualified. *)
let wrapper_module_table : (ModPath.t, string) Hashtbl.t = Hashtbl.create 16

(* Collision wrapper table: tracks modpaths that were registered as collision-wrapped
   (i.e., a child module whose name collides with a global inductive, wrapped into
   a parent struct). For these, wrapper_qualify_name strips the child qualifier. *)
let collision_wrapper_table : (ModPath.t, unit) Hashtbl.t = Hashtbl.create 16

(* Global-scope enum table: tracks enum inductives that were rendered at global scope
   (not inside any struct). Used to avoid incorrect struct qualification in .cpp files. *)
let global_scope_enum_table : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 16

(* Pending wrapper declarations: maps a Dnspace struct name (e.g., "Nat") to
   pre-rendered forward declarations (specs) that should be injected into that struct.
   Full definitions are rendered separately in PASS 3 after all types are defined.
   Populated during do_struct_with_decl_tracking PASS 1.
   Consumed during Dnspace rendering in PASS 2. *)
let pending_wrapper_decls : (string, Pp.t) Hashtbl.t = Hashtbl.create 16

(* Set of wrapper struct names that have pending declarations and thus cannot be merged.
   Populated alongside pending_wrapper_decls during PASS 1.
   Used during type/expression rendering to decide between merged (List<A>)
   and unmerged (List::list<A>) name formats. Not consumed during rendering. *)
let unmerged_wrappers : (string, unit) Hashtbl.t = Hashtbl.create 16

(* Maps capitalized inductive names to their ModPaths across all modules.
   Pre-populated in do_struct_with_decl_tracking before code generation.
   Used to detect module-inductive name collisions (e.g., N/Z appearing
   as both an inductive from BinNums and a module from BinNat). *)
let global_inductive_names : (string, ModPath.t) Hashtbl.t = Hashtbl.create 16



(* Check if a GlobRef belongs to a wrapper module and return the qualified name.
   If the reference's module path matches a wrapper module, prepend the struct name.
   Only qualify ConstRef globals (actual Rocq constants from modules).
   VarRef globals are lifted declarations (like _foo_aux) that should not be
   qualified with a wrapper struct name — their modpath comes from Lib.make_kn
   which reflects the current library, not the wrapper module. *)
let wrapper_qualify_name (r : GlobRef.t) (name : string) : string =
  match r with
  | GlobRef.VarRef _ -> name  (* Lifted declarations: never qualify *)
  | _ ->
    let mp = modpath_of_r r in
    match Hashtbl.find_opt wrapper_module_table mp with
    | Some struct_name when not (String.contains name ':') ->
      struct_name ^ "::" ^ name
    | Some struct_name when String.contains name ':' ->
      (* Name is already qualified (e.g., "N::add" from visibility stack).
         Only strip the child qualifier for collision-wrapped entries
         (e.g., BinNat wrapping N). For normal wrappers (e.g., List wrapping list),
         keep the full qualification. *)
      if Hashtbl.mem collision_wrapper_table mp then
        (match String.index_opt name ':' with
         | Some colon_pos when colon_pos > 0 && colon_pos + 1 < String.length name && name.[colon_pos + 1] = ':' ->
           let func_part = String.sub name (colon_pos + 2) (String.length name - colon_pos - 2) in
           struct_name ^ "::" ^ func_part
         | _ -> name)
      else
        name
    | _ -> name

let register_method (func_ref : GlobRef.t) (epon_ref : GlobRef.t) (this_pos : int) ?(ind_tvar_positions : int list = []) () =
  Method_registry.register_method (get_method_registry ()) func_ref epon_ref this_pos ~ind_tvar_positions

let is_registered_method (func_ref : GlobRef.t) : (GlobRef.t * int) option =
  Method_registry.is_registered_method (get_method_registry ()) func_ref

(* Look up the inductive's type variable positions (0-based indices into
   the function's tys list) for a registered method.
   These positions correspond to the inductive's template params which
   are already deducible from the receiver object and should be omitted
   from explicit template arguments in method calls. *)
let lookup_method_ind_tvar_positions (func_ref : GlobRef.t) : int list =
  Method_registry.lookup_ind_tvar_positions (get_method_registry ()) func_ref

let register_method_returns_any (func_ref : GlobRef.t) =
  Method_registry.register_method_returns_any (get_method_registry ()) func_ref

let method_returns_any (func_ref : GlobRef.t) : bool =
  Method_registry.method_returns_any (get_method_registry ()) func_ref

(* Global registry of eponymous records.
   When a module M contains a record with the same name (e.g., module CHT with record CHT),
   the record fields are merged directly into the module struct. This avoids C++ name
   conflicts where both the module and record would have the same name.

   This registry is global (not per-module) because type references from OTHER modules
   need to know how to render the type name. Without this registry, a reference to CHT
   from another module would incorrectly generate "CHT::cHT" instead of just "CHT".

   See also: pp_inductive_type_name which uses this registry for type name rendering. *)
let global_eponymous_record_registry : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 100

let register_eponymous_record (record_ref : GlobRef.t) =
  Hashtbl.replace global_eponymous_record_registry record_ref ()

let is_eponymous_record_global (r : GlobRef.t) : bool =
  Hashtbl.mem global_eponymous_record_registry r

(* Check if a constant (function) is inside an eponymous template module.
   Returns Some record_ref if the function is inside a module whose name matches
   a registered eponymous record. This is used to correctly generate
   StructName<Args>::funcName() instead of StructName::funcName<Args>(). *)
let get_containing_eponymous_struct (r : GlobRef.t) : GlobRef.t option =
  match r with
  | GlobRef.ConstRef kn ->
    (* Get the module path containing this constant *)
    let mp = Names.Constant.modpath kn in
    (* Check if there's an eponymous record whose module path matches *)
    let result = ref None in
    Hashtbl.iter (fun record_ref () ->
      let record_mp = match record_ref with
        | GlobRef.IndRef (ind, _) -> Names.MutInd.modpath ind
        | _ -> mp  (* Won't match *)
      in
      (* Check if the constant is in the same module as the record *)
      if ModPath.equal mp record_mp then
        result := Some record_ref
    ) global_eponymous_record_registry;
    !result
  | _ -> None

(* Track current structure's declarations for finding methods from sibling modules.
   When processing a module like List inside tree.v, we need to also scan
   sibling declarations (like app) that are from the same Rocq module. *)
let current_structure_decls : (Label.t * Miniml.ml_structure_elem) list ref = ref []

(* Reset ALL global state - must be called between extractions to avoid pollution.
   This prevents state from one extraction affecting another when running multiple
   extractions in the same process (e.g., during 'dune build'). *)
let reset_cpp_state () =
  restore_render_ctx {
    rcs_in_struct = false;
    rcs_concepts_hoisted = false;
    rcs_struct_name = None;
    rcs_struct_mp = None;
    rcs_in_template = false;
  };
  eponymous_type_ref := None;
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
  Hashtbl.clear functor_app_sources

(* Check if a function is a projection for the eponymous record.
   Such projections are redundant when the record fields are merged into the module struct. *)
let is_eponymous_record_projection r =
  match !eponymous_record with
  | None -> false
  | Some (epon_ref, _, _) ->
      if Table.is_projection r then
        let (ip, _arity) = Table.projection_info r in
        (* Check if this projection's inductive matches the eponymous record *)
        Environ.QGlobRef.equal Environ.empty_env (GlobRef.IndRef ip) epon_ref
      else
        false

let is_suppressed_projection r =
  Table.is_projection r && not (Table.is_higher_order_projection r)

(** Filter a Dfix group, removing entries that are inline customs,
    method candidates (local or globally registered), eponymous record
    projections, or suppressed projections.  Returns the three filtered
    arrays (refs, bodies, types). *)
let filter_dfix rv defs typs =
  let is_method_candidate x =
    List.exists (fun (r', _, _, _) ->
      Environ.QGlobRef.equal Environ.empty_env x r'
    ) !method_candidates
  in
  let is_global_method x = is_registered_method x <> None in
  let filter = Array.to_list (Array.map (fun x ->
    not (is_inline_custom x) &&
    not (is_method_candidate x) &&
    not (is_global_method x) &&
    not (is_eponymous_record_projection x) &&
    not (is_suppressed_projection x)
  ) rv) in
  (Array.filter_with filter rv,
   Array.filter_with filter defs,
   Array.filter_with filter typs)

(* Beware of the side-effects of [pp_global] and [pp_modname].
   They are used to update table of content for modules. Many [let]
   below should not be altered since they force evaluation order.
*)

let str_global_with_key k key r =
  match find_custom_opt r with
  | Some custom_str when to_inline r -> custom_str
  | _ -> Common.pp_global_with_key k key r

let str_global k r = str_global_with_key k (repr_of_r r) r

let pp_global_with_key k key r = str (str_global_with_key k key r)

let pp_global k r = str (str_global k r)
(*
let pp_lowercase r = str (String.uncapitalize_ascii (str_global Type r))

let pp_uppercase r = str (String.capitalize_ascii (str_global Type r))
*)
let pp_global_name k r = str (Common.pp_global k r)

let pp_modname mp = str (Common.pp_module mp)

(* Check if a non-local inductive's Dnspace wrapper was merged with its inner struct.
   Returns true if the wrapper WAS merged (no pending declarations → use List<A>).
   Returns false if it was NOT merged (has pending declarations → use List::list<A>). *)
let is_merged_inductive (r : GlobRef.t) : bool =
  let base = str_global Type r in
  let wrapper_name = String.capitalize_ascii base in
  not (Hashtbl.mem unmerged_wrappers wrapper_name)

(* grammar from OCaml 4.06 manual, "Prefix and infix symbols" *)

let infix_symbols =
  ['=' ; '<' ; '>' ; '@' ; '^' ; ';' ; '&' ; '+' ; '-' ; '*' ; '/' ; '$' ; '%' ]
let operator_chars =
  [ '!' ; '$' ; '%' ; '&' ; '*' ; '+' ; '-' ; '.' ; '/' ; ':' ; '<' ; '=' ; '>' ; '?' ; '@' ; '^' ; '|' ; '~' ]

(* infix ops in OCaml, but disallowed by preceding grammar *)

let builtin_infixes =
  [ "::" ; "," ]

let substring_all_opchars s start stop =
  let rec check_char i =
    if i >= stop then true
    else
      List.mem s.[i] operator_chars && check_char (i+1)
  in
  check_char start

let is_infix r =
  match find_custom_opt r with
  | Some s when to_inline r ->
      let len = String.length s in
      len >= 3 &&
      (* parenthesized *)
      (s.[0] == '(' && s.[len-1] == ')' &&
         let inparens = String.trim (String.sub s 1 (len - 2)) in
         let inparens_len = String.length inparens in
         (* either, begins with infix symbol, any remainder is all operator chars *)
         (List.mem inparens.[0] infix_symbols && substring_all_opchars inparens 1 inparens_len) ||
         (* or, starts with #, at least one more char, all are operator chars *)
         (inparens.[0] == '#' && inparens_len >= 2 && substring_all_opchars inparens 1 inparens_len) ||
         (* or, is an OCaml built-in infix *)
         (List.mem inparens builtin_infixes))
  | _ -> false

let get_infix r =
  let s = find_custom r in
  String.sub s 1 (String.length s - 2)

let get_ind = let open GlobRef in function
  | IndRef _ as r -> r
  | ConstructRef (ind,_) -> IndRef ind
  | _ -> assert false

let kn_of_ind = let open GlobRef in function
  | IndRef (kn,_) -> MutInd.user kn
  | _ -> assert false

let pp_one_field r i = function
  | Some r' -> pp_global_with_key Term (kn_of_ind (get_ind r)) r'
  | None -> pp_global Type (get_ind r) ++ str "__" ++ int i

let pp_field r fields i = pp_one_field r i (List.nth fields i)

let pp_fields r fields = List.map_i (pp_one_field r) 0 fields

(* ============================================================================
   Helper functions to reduce code duplication
   ============================================================================ *)

(* Check if a type name is already qualified (contains ::) *)
let is_qualified_name name_str = String.contains name_str ':'

(* Check if a GlobRef is a record type (not a regular inductive).
   Records don't get wrapped in namespace structs, so they keep their original case. *)
let is_record_inductive r =
  match r with
  | GlobRef.IndRef _ -> Table.get_record_fields r <> []
  | _ -> false

(* Check if a GlobRef refers to a local inductive (defined in current module scope).
   Local inductives don't need namespace qualification (e.g., List::list vs just list). *)
let is_local_inductive r =
  List.exists (Environ.QGlobRef.equal Environ.empty_env r) (get_local_inductives ())

(* Get the appropriate name for an inductive reference.
   - Local inductives: original name directly (e.g., "list", "EvenTree")
   - Non-local inductives: capitalized name (e.g., "List", "Nat")
   Returns (name_pp, needs_namespace) where:
   - name_pp is the printed name
   - needs_namespace indicates if this is a non-local inductive (capitalized) *)
let inductive_name_info r =
  match r with
  | GlobRef.IndRef _ when is_eponymous_record_global r ->
      (* Eponymous record: merged into module struct, no nested namespace.
         Check this FIRST because local inductives can also be eponymous.
         Use pp_global_name to get just the base name, not the qualified path. *)
      (str (String.capitalize_ascii (Common.pp_global_name Type r)), false)
  | GlobRef.IndRef _ when is_local_inductive r ->
      (* Local inductive: use lowercase name directly, no namespace *)
      (pp_global Type r, false)
  | GlobRef.IndRef _ ->
      (* Non-local inductive: capitalize for namespace struct name *)
      (str (String.capitalize_ascii (str_global Type r)), true)
  | _ ->
      (* Non-inductive: use as-is, no namespace *)
      (pp_global Type r, false)

(* Format an inductive type name for type references.
   Non-local inductives use capitalized name directly (e.g., "List", "Nat").
   Local inductives use original Rocq name (e.g., "list", "EvenTree").
   EXCEPTION 1: Eponymous records (module M with record M) use capitalized name.
   EXCEPTION 2: Regular records (not eponymous) keep their original case. *)
let pp_inductive_type_name r =
  let result = match r with
  | GlobRef.IndRef _ when is_eponymous_record_global r ->
      (* Eponymous record: use capitalized name directly (merged into module struct)
         Check this FIRST because local inductives can also be eponymous.
         Use pp_global_name to get just the base name, not the qualified path. *)
      str (String.capitalize_ascii (Common.pp_global_name Type r))
  | GlobRef.IndRef _ when is_record_inductive r ->
      (* Regular records: keep original case (no namespace wrapper) *)
      pp_global Type r
  | GlobRef.IndRef _ when is_local_inductive r ->
      (* Local inductive: use original name directly *)
      pp_global Type r
  | GlobRef.IndRef _ when is_enum_inductive r ->
      (* Enum inductive: use original name directly (no namespace wrapper).
         If already module-qualified (e.g., "Outer::color"), use as-is. *)
      let name = str_global Type r in
      str name
  | GlobRef.IndRef _ ->
      let base = str_global Type r in
      if is_qualified_name base then
        (* Already qualified (e.g., C::t from module parameter): use as-is *)
        str base
      else if is_merged_inductive r then
        (* Merged non-local inductive: use capitalized name directly *)
        str (String.capitalize_ascii base)
      else
        (* Unmerged non-local inductive: Wrapper::inner *)
        let wrapper = String.capitalize_ascii base in
        str (wrapper ^ "::" ^ base)
  | _ ->
      (* Non-inductive: use as-is *)
      pp_global Type r
  in
  result

(* Add typename prefix for dependent types in template contexts.
   C++ requires 'typename' keyword when accessing nested types in templates. *)
let typename_prefix_for name_str =
  if !in_template_struct && is_qualified_name name_str then
    str "typename "
  else
    mt ()

(* Add struct qualification prefix if needed.
   When generating out-of-struct member function definitions, we need to qualify
   types that belong to the current struct. *)
let struct_qualifier_for r name_str =
  match !current_struct_name with
  | Some struct_name when not (is_qualified_name name_str) ->
      (* Enum types at global scope need no struct qualification.
         Enums inside structs need it. *)
      if Table.is_enum_inductive r then
        (if Hashtbl.mem global_scope_enum_table r then
           mt ()
         else
           let full_path = Pp.string_of_ppcmds (GlobRef.print r) in
           let struct_name_str = Pp.string_of_ppcmds struct_name in
           let struct_name_dotted = Str.global_replace (Str.regexp_string "::") "." struct_name_str in
           if Common.contains_substring full_path struct_name_dotted then
             struct_name ++ str "::"
           else
             mt ())
      else begin
        let full_path = Pp.string_of_ppcmds (GlobRef.print r) in
        let struct_name_str = Pp.string_of_ppcmds struct_name in
        (* Normalize C++ :: separators to dots for comparison with Rocq paths *)
        let struct_name_dotted = Str.global_replace (Str.regexp_string "::") "." struct_name_str in
        (* Only qualify if the type belongs to the current struct *)
        if Common.contains_substring full_path struct_name_dotted then
          struct_name ++ str "::"
        else
          mt ()
      end
  | _ -> mt ()

(* Check if a global function needs :: prefix to avoid name collision.
   When generating out-of-struct definitions, we add :: to call external functions
   rather than recursing into the struct's own member. *)
let needs_global_qualifier x =
  match !current_struct_name with
  | Some struct_name ->
      let name_str = str_global Term x in
      if is_qualified_name name_str then false  (* Already qualified *)
      else
        let full_path = Pp.string_of_ppcmds (GlobRef.print x) in
        let struct_name_str = Pp.string_of_ppcmds struct_name in
        (* Normalize C++ :: separators to dots for comparison with Rocq paths *)
        let struct_name_dotted = Str.global_replace (Str.regexp_string "::") "." struct_name_str in
        if Common.contains_substring full_path struct_name_dotted then false
        else
          (* Fallback: check ModPath equality for renamed modules (e.g., Coq_Pos).
             When a module is renamed (modfstlev_rename), the C++ struct name differs
             from the Rocq path, so string comparison fails. Use ModPath comparison instead. *)
          (match !current_struct_mp with
          | Some struct_mp -> not (ModPath.equal (modpath_of_r x) struct_mp)
          | None -> true)
  | None -> false

(* ============================================================================
   Cache-backed name resolution helpers
   ============================================================================
   These query the pre-computed Name_resolution cache, falling back to the
   original logic when the cache doesn't have an entry (e.g., for local
   inductives discovered during rendering). *)

(* ============================================================================
   Cache-backed name resolution helpers
   ============================================================================
   These query the pre-computed Name_resolution cache for classification
   information (eponymous, enum, record, merged status).  The actual display
   name rendering is still done by the original functions (pp_inductive_type_name,
   inductive_name_info, etc.) since they depend on the visibility context which
   is only available during rendering.

   The cache accelerates boolean queries that cpp.ml uses frequently to decide
   HOW to render a name, while the original functions produce the actual name. *)

(* Cache-backed is_eponymous_record check — avoids hashtable lookup. *)
let is_eponymous_record_cached (r : GlobRef.t) : bool =
  match !name_cache with
  | Some cache -> Name_resolution.is_eponymous cache r
  | None -> is_eponymous_record_global r

(* Cache-backed is_global_scope_enum check — avoids hashtable lookup. *)
let is_global_scope_enum_cached (r : GlobRef.t) : bool =
  match !name_cache with
  | Some cache -> Name_resolution.is_global_scope_enum cache r
  | None -> Hashtbl.mem global_scope_enum_table r

(* Cache-backed is_merged_inductive check — avoids hashtable lookup. *)
let is_merged_inductive_cached (r : GlobRef.t) : bool =
  match !name_cache with
  | Some cache ->
    (match Name_resolution.resolve_type cache r with
     | Some rtn -> rtn.Name_resolution.rtn_is_merged
     | None -> is_merged_inductive r)
  | None -> is_merged_inductive r

(* Cache-backed inductive classification queries. *)
let get_ind_kind_cached (r : GlobRef.t) : Minicpp.cpp_ind_kind option =
  match !name_cache with
  | Some cache -> Name_resolution.get_ind_kind cache r
  | None -> None

let is_enum_cached (r : GlobRef.t) : bool =
  match get_ind_kind_cached r with
  | Some IK_Enum -> true
  | Some _ -> false
  | None -> is_enum_inductive r

let is_record_cached (r : GlobRef.t) : bool =
  match get_ind_kind_cached r with
  | Some (IK_Record _ | IK_Eponymous _) -> true
  | Some _ -> false
  | None -> is_record_inductive r

(* For display names, delegate to original functions — they need visibility context.
   These are thin wrappers for now; they become useful when we have more context. *)
let pp_inductive_type_name_cached r = pp_inductive_type_name r
let inductive_name_info_cached r = inductive_name_info r
let wrapper_qualify_name_cached r name = wrapper_qualify_name r name

(* Look up method info for a function reference.
   Checks both local method_candidates and global method_registry.
   Returns Some this_pos if the function is a method, None otherwise. *)
let lookup_method_this_pos n =
  (* First check local method_candidates *)
  let local_result = List.find_map (fun (r', _, _, pos) ->
    if Environ.QGlobRef.equal Environ.empty_env n r' then Some pos else None
  ) !method_candidates in
  match local_result with
  | Some pos -> Some pos
  | None ->
    (* Fall back to global registry for cross-module methods *)
    match is_registered_method n with
    | Some (_, pos) -> Some pos
    | None -> None

(* Helper module for tracking variable names *)
module IdSet = Set.Make(Names.Id)

(* Check if a lambda actually needs to capture variables from enclosing scope.
   A lambda needs [&] capture if its body references variables that are:
   - Not lambda parameters
   - Not locally declared within the lambda body
   - 'this' pointer (always needs capture in a lambda)
   Returns true if capture is needed, false if [] can be used.

   Also checks recursively: if a nested lambda captures from the outer lambda's scope,
   that counts as the outer lambda needing capture. *)
let rec lambda_needs_capture (params : (Minicpp.cpp_type * Names.Id.t option) list)
                              (body : Minicpp.cpp_stmt list) : bool =
  let open Minicpp in

  (* Collect parameter names *)
  let param_names = List.fold_left (fun acc (_, id_opt) ->
    match id_opt with Some id -> IdSet.add id acc | None -> acc
  ) IdSet.empty params in

  (* Track if 'this' is used - it always requires capture *)
  let uses_this = ref false in

  (* Collect all variable references and local declarations from expressions and statements *)
  let rec collect_from_expr (refs, decls) e =
    match e with
    | CPPvar id -> (IdSet.add id refs, decls)
    (* CPPvar' removed — all vars now use CPPvar *)
    | CPPthis -> uses_this := true; (refs, decls)  (* 'this' requires capture *)
    | CPPfun_call (f, args) ->
        let acc = collect_from_expr (refs, decls) f in
        List.fold_left collect_from_expr acc args
    | CPPnamespace (_, e') -> collect_from_expr (refs, decls) e'
    | CPPderef e' -> collect_from_expr (refs, decls) e'
    | CPPmove e' -> collect_from_expr (refs, decls) e'
    | CPPforward (_, e') -> collect_from_expr (refs, decls) e'
    | CPPlambda (inner_params, _, inner_body, _) ->
        (* For nested lambdas, don't count their parameters or local vars as our refs.
           But DO check if the nested lambda itself captures from OUR scope. *)
        let inner_param_names = List.fold_left (fun acc (_, id_opt) ->
          match id_opt with Some id -> IdSet.add id acc | None -> acc
        ) IdSet.empty inner_params in
        let (inner_refs, inner_decls) = List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) inner_body in
        (* Variables referenced in inner lambda that aren't its own params/locals
           might be captured from our scope *)
        let inner_free = IdSet.diff inner_refs (IdSet.union inner_param_names inner_decls) in
        (IdSet.union refs inner_free, decls)
    | CPPoverloaded exprs -> List.fold_left collect_from_expr (refs, decls) exprs
    | CPPstructmk (_, _, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPstruct (_, _, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPstruct_id (_, _, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPget (e', _) -> collect_from_expr (refs, decls) e'
    | CPPget' (e', _) -> collect_from_expr (refs, decls) e'
    | CPPparray (arr, e') ->
        let acc = Array.fold_left (fun a e -> collect_from_expr a e) (refs, decls) arr in
        collect_from_expr acc e'
    | CPPnew (_, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPshared_ptr_ctor (_, e') -> collect_from_expr (refs, decls) e'
    | CPPunique_ptr_ctor (_, e') -> collect_from_expr (refs, decls) e'
    | CPPmember (e', _) -> collect_from_expr (refs, decls) e'
    | CPParrow (e', _) -> collect_from_expr (refs, decls) e'
    | CPPmethod_call (obj, _, args) ->
        let acc = collect_from_expr (refs, decls) obj in
        List.fold_left collect_from_expr acc args
    | CPPqualified (e', _) -> collect_from_expr (refs, decls) e'
    | CPPrequires (_, constraints, _) ->
        List.fold_left (fun acc (e', _) -> collect_from_expr acc e') (refs, decls) constraints
    | CPPbinop (_, lhs, rhs) ->
        collect_from_expr (collect_from_expr (refs, decls) lhs) rhs
    (* Leaf expressions: no variables to collect *)
    | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPmk_unique _ | CPPstring _
    | CPPuint _ | CPPfloat _ | CPPconvertible_to _ | CPPabort _ | CPPenum_val _ | CPPraw _ ->
        (refs, decls)

  and collect_from_stmt (refs, decls) stmt =
    match stmt with
    (* Simple statements *)
    | Sreturn None -> (refs, decls)
    | Sreturn (Some e) -> collect_from_expr (refs, decls) e
    | Sexpr e -> collect_from_expr (refs, decls) e

    (* Declarations and assignments *)
    | Sdecl (id, _) -> (refs, IdSet.add id decls)
    | Sasgn (id, _, e) ->
        let (refs', decls') = collect_from_expr (refs, decls) e in
        (refs', IdSet.add id decls')

    (* Control flow *)
    | Sif (cond, then_stmts, else_stmts) ->
        List.fold_left collect_from_stmt
          (List.fold_left collect_from_stmt
             (collect_from_expr (refs, decls) cond)
             then_stmts)
          else_stmts

    | Sswitch (scrut, _, branches) ->
        List.fold_left (fun acc (_, stmts) ->
          List.fold_left collect_from_stmt acc stmts
        ) (collect_from_expr (refs, decls) scrut) branches

    | Scustom_case (_, scrut, _, branches, _) ->
        List.fold_left (fun (r, d) (branch_vars, _, stmts) ->
          let branch_decls = List.fold_left (fun acc (id, _) ->
            IdSet.add id acc
          ) d branch_vars in
          List.fold_left collect_from_stmt (r, branch_decls) stmts
        ) (collect_from_expr (refs, decls) scrut) branches

    (* Field mutation (for reuse optimization) *)
    | Sassign_field (obj, _, e) ->
        collect_from_expr (collect_from_expr (refs, decls) obj) e

    (* No variables to collect *)
    | Sthrow _ | Sassert _ | Sraw _ -> (refs, decls)
  in

  let (all_refs, local_decls) = List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) body in
  let bound_vars = IdSet.union param_names local_decls in
  let free_vars = IdSet.diff all_refs bound_vars in
  (* Lambda needs capture if it has free variables OR uses 'this' *)
  not (IdSet.is_empty free_vars) || !uses_this

(* Check if a cpp_expr contains any lambdas that need capture (have free variables).
   Used to determine if IIFE wrapping is needed for static inline initializers.
   Closed lambdas (with []) don't need IIFE wrapping. *)
and expr_contains_capturing_lambda (e : Minicpp.cpp_expr) : bool =
  let open Minicpp in
  match e with
  | CPPlambda (params, _, body, _) ->
      (* Check if this lambda needs capture, OR if any nested lambdas need capture *)
      lambda_needs_capture params body ||
      List.exists stmt_contains_capturing_lambda body
  | CPPfun_call (f, args) -> expr_contains_capturing_lambda f || List.exists expr_contains_capturing_lambda args
  | CPPnamespace (_, e') -> expr_contains_capturing_lambda e'
  | CPPderef e' -> expr_contains_capturing_lambda e'
  | CPPmove e' -> expr_contains_capturing_lambda e'
  | CPPforward (_, e') -> expr_contains_capturing_lambda e'
  | CPPoverloaded exprs -> List.exists expr_contains_capturing_lambda exprs
  | CPPstructmk (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPstruct (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPstruct_id (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPget (e', _) -> expr_contains_capturing_lambda e'
  | CPPget' (e', _) -> expr_contains_capturing_lambda e'
  | CPPparray (args, e') -> Array.exists expr_contains_capturing_lambda args || expr_contains_capturing_lambda e'
  | CPPnew (_, args) -> List.exists expr_contains_capturing_lambda args
  | CPPshared_ptr_ctor (_, e') -> expr_contains_capturing_lambda e'
  | CPPunique_ptr_ctor (_, e') -> expr_contains_capturing_lambda e'
  | CPPmember (e', _) -> expr_contains_capturing_lambda e'
  | CPParrow (e', _) -> expr_contains_capturing_lambda e'
  | CPPmethod_call (obj, _, args) -> expr_contains_capturing_lambda obj || List.exists expr_contains_capturing_lambda args
  | CPPqualified (e', _) -> expr_contains_capturing_lambda e'
  | CPPrequires (_, constraints, _) -> List.exists (fun (e', _) -> expr_contains_capturing_lambda e') constraints
  | CPPbinop (_, lhs, rhs) -> expr_contains_capturing_lambda lhs || expr_contains_capturing_lambda rhs
  | CPPvar _ | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPmk_unique _ | CPPstring _ | CPPuint _ | CPPfloat _ | CPPthis | CPPconvertible_to _ | CPPabort _ | CPPenum_val _ | CPPraw _ -> false

and stmt_contains_capturing_lambda (s : Minicpp.cpp_stmt) : bool =
  let open Minicpp in
  let any = List.exists stmt_contains_capturing_lambda in
  let expr = expr_contains_capturing_lambda in
  match s with
  (* Statements with expressions *)
  | Sreturn (Some e) | Sexpr e | Sasgn (_, _, e) -> expr e
  | Sreturn None -> false
  | Sassign_field (obj, _, e) -> expr obj || expr e

  (* Control flow *)
  | Sif (cond, then_s, else_s) -> expr cond || any then_s || any else_s
  | Sswitch (scrut, _, branches) ->
      expr scrut || List.exists (fun (_, stmts) -> any stmts) branches
  | Scustom_case (_, scrut, _, branches, _) ->
      expr scrut || List.exists (fun (_, _, stmts) -> any stmts) branches

  (* No lambdas possible *)
  | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ -> false

(* pretty printing c++ syntax *)
let try_cpp c o =
  try c
  with TODO -> o

let pp_tymod = function
  | TMconst -> str "const "
  | TMstatic -> str "static "
  | TMextern -> str "extern "

let std_angle label s =
  str (sn ()).ns ++ str "::" ++ str label ++ str "<" ++ s ++ str ">"

let cpp_angle label s = str label ++ str "<" ++ s ++ str ">"


type custom_case =
| CCscrut
| CCty
| CCbody of int
| CCty_arg of int
| CCbr_var of int * int
| CCbr_var_ty of int * int
(* | CCbr_rty of int *)
| CCstring of string
| CCarg of int

let is_digit c = c >= '0' && c <= '9'

(* Parses an integer starting at [i], returns (value, next_index) *)
let parse_number s i n =
  let rec aux j =
    if j < n && is_digit s.[j] then aux (j + 1) else j
  in
  let j = aux i in
  if j = i then None
  else
    let num_str = String.sub s i (j - i) in
    Some (int_of_string num_str, j)

(*
  The following functions parse custom placeholders in extraction syntax strings:
  - parse_custom_fixed: parses fixed placeholders like %scrut or %ty
  - parse_custom_single_arg: parses placeholders like %a0, %t12 (single argument)
  - parse_custom_double_arg: parses placeholders like %b0a1, %b10a20 (two arguments)
*)

(* Parses fixed custom placeholders like %scrut or %ty *)
let parse_custom_fixed esc cc s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start chunks_rev =
    if i >= n then
      let last_chunk = String.sub s start (n - start) in
      List.rev (CCstring last_chunk :: chunks_rev)
    else
      match s.[i], i + esc_len + 1 < n with
      | '%', true ->
        if esc = String.sub s (i+1) esc_len then
          let chunk = String.sub s start (i - start) in
          aux (i + esc_len + 1) (i + esc_len + 1) (cc :: CCstring chunk :: chunks_rev)
        else
          aux (i + 1) start chunks_rev
      | _ ->
        aux (i + 1) start chunks_rev
  in
  aux 0 0 []

(* Parses single-argument custom placeholders like %a0, %t12 *)
let parse_numbered_args esc f s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start acc =
    if i >= n then
      List.rev (if start < n then CCstring (String.sub s start (n - start)) :: acc else acc)
    else if s.[i] = '%' && i + esc_len < n &&
            String.sub s (i + 1) esc_len = esc then
      match parse_number s (i + 1 + esc_len) n with
      | Some (idx, j) ->
        let chunk = String.sub s start (i - start) in
        aux j j (f idx :: CCstring chunk :: acc)
      | None ->
        aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(* Parses double-argument custom placeholders like %b0a1, %b10a20 *)
let parse_custom_numbered_binders esc1 esc2 f s =
  let n = String.length s in
  let len1 = String.length esc1 in
  let len2 = String.length esc2 in
  let rec aux i start acc =
    if i >= n then
      List.rev (if start < n then CCstring (String.sub s start (n - start)) :: acc else acc)
    else if s.[i] = '%' &&
            i + len1 < n &&
            String.sub s (i + 1) len1 = esc1 then
      match parse_number s (i + 1 + len1) n with
      | Some (idx1, j) when j + len2 <= n && String.sub s j len2 = esc2 ->
        begin
          match parse_number s (j + len2) n with
          | Some (idx2, k) ->
            let chunk = String.sub s start (i - start) in
            aux k k (f idx1 idx2 :: CCstring chunk :: acc)
          | None ->
            aux (i + 1) start acc
        end
      | _ ->
        aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

let print_cpp_type_var vl i = (try pp_tvar (List.nth vl (pred i))
                              with Failure _ -> (str "T" ++ int i)) (* TODO: CHANGE *)

(* cleanup without parens bool *)
let rec pp_cpp_type par vl t =
  let rec pp_rec par = function
    | Tvar (i, None) -> print_cpp_type_var vl i
    | Tvar (_, Some id) -> Id.print id
    (* NEW: Tid for local type references (e.g., nested structs inside modules).
       These don't need GlobRef qualification, just simple Id references.
       Can be parameterized like generic types: Leaf<int>
       When generating out-of-struct definitions, prepend struct name. *)
    | Tid (id, []) ->
        (match !current_struct_name with
         | Some struct_name when not !in_struct_context -> struct_name ++ str "::" ++ Id.print id
         | _ -> Id.print id)
    | Tid (id, args) ->
        (match !current_struct_name with
         | Some struct_name when not !in_struct_context ->
             struct_name ++ str "::" ++ Id.print id ++ str "<" ++ pp_list (pp_rec false) args ++ str ">"
         | _ -> Id.print id ++ str "<" ++ pp_list (pp_rec false) args ++ str ">")
    | Tglob (r, tys, args) ->
        (* Erased type/prop/implicit markers (from Tdummy in the ML AST) should
           never reach the C++ output.  When they do survive — e.g. as a template
           argument of SigT<nat, dummy_prop> — render them as std::any. *)
        (match r with
        | GlobRef.VarRef id
          when (let name = Id.to_string id in
                name = "dummy_type" || name = "dummy_prop" || name = "dummy_implicit") ->
            str "std::any"
        | _ ->
        (match find_custom_opt r with
        | Some s when to_inline r ->
            let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
            let cmds = List.fold_left
            (fun prev curr -> match curr with
                              | CCstring s -> prev @ (parse_numbered_args "t" (fun i -> CCty_arg i) s)
                              | _ -> prev @ [curr]) [] cmds in
            pp_custom (Pp.string_of_ppcmds (GlobRef.print r) ^ " := " ^ s) (empty_env ()) None None tys [] args [] vl cmds
        | _ ->
            (* Non-custom cases *)
            let type_name = pp_inductive_type_name_cached r in
            let name_str = Pp.string_of_ppcmds type_name in
            (match tys with
            | [] ->
                typename_prefix_for name_str ++ struct_qualifier_for r name_str ++ type_name
            | l ->
                typename_prefix_for name_str ++ struct_qualifier_for r name_str ++
                type_name ++ str "<" ++ pp_list (pp_rec false) l ++ str ">")))

    | Tfun (d,c) -> std_angle "function" (pp_rec false c ++ pp_par true (pp_list (pp_rec false) d))
    | Tref t -> pp_rec false t ++ str "&"
    | Tmod (m, t) -> pp_tymod m ++ pp_rec false t
    | Tnamespace (r,t) ->
        (* DESIGN: Namespace-qualified types for inductive types.
           Rocq's inductives live in wrapper structs (e.g., type 'list' in struct 'List').
           Local inductives don't need namespace wrapping; non-local ones get the prefix.
           EXCEPTION: Eponymous records are merged into the module struct, so we use just
           the capitalized name without namespace qualification (CHT, not CHT::cHT). *)
        let (name, _needs_ns) = inductive_name_info_cached r in
        (* Check if inner type is Tglob with the same reference *)
        (match (r, t) with
         | GlobRef.IndRef _, Tglob (r', args, _) when Environ.QGlobRef.equal Environ.empty_env r r' ->
           let templates = match args with
             | [] -> mt ()
             | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">"
           in
           (* Skip prefix if type name already contains module path (::) *)
           let type_name_str = str_global Type r' in
           (* Check eponymous record FIRST because they can also be local *)
           if is_eponymous_record_cached r' then
             (* Eponymous record: use capitalized name directly, no namespace nesting.
                Use pp_global_name to get just the base name, not the qualified path. *)
             str (String.capitalize_ascii (Common.pp_global_name Type r')) ++ templates
           else if is_enum_cached r' then
             (* Enum types at global scope need no struct qualification.
                Enums inside structs (e.g., Comparison::cmp) need it. *)
             let qualifier =
               match !current_struct_name with
               | Some struct_name when not !in_struct_context ->
                   if is_global_scope_enum_cached r' then
                     mt ()
                   else
                     let full_path = Pp.string_of_ppcmds (GlobRef.print r') in
                     let struct_name_str = Pp.string_of_ppcmds struct_name in
                     let struct_name_dotted = Str.global_replace (Str.regexp_string "::") "." struct_name_str in
                     if Common.contains_substring full_path struct_name_dotted then
                       struct_name ++ str "::"
                     else
                       mt ()
               | _ -> mt ()
             in
             qualifier ++ str type_name_str ++ templates
           else if is_qualified_name type_name_str then
             (* Already qualified (e.g., C::t from module parameter): add typename if in template *)
             typename_prefix_for type_name_str ++ str type_name_str ++ templates
           else if is_merged_inductive_cached r' then
             (* Merged: use capitalized name directly *)
             name ++ templates
           else
             (* Unmerged: use Wrapper::inner<args> *)
             name ++ str "::" ++ str type_name_str ++ templates
         | _ ->
           (* Fallback: generic namespace-qualified type *)
           str "typename " ++ name ++ str "::" ++ pp_rec false t)
    | Tqualified (base_ty, nested_id) ->
        (* DESIGN: Template-dependent type access like 'typename M::Key::t'
           C++ templates require 'typename' to access nested types from dependent base types. *)
        let base_str = match base_ty with
          | Tglob (r, _, _) ->
            let type_name_str = str_global Type r in
            if is_qualified_name type_name_str then
              pp_rec false base_ty
            else
              let (ns_name, needs_ns) = inductive_name_info_cached r in
              if needs_ns && not (is_merged_inductive_cached r) then
                (* Unmerged: need wrapper prefix *)
                ns_name ++ str "::" ++ pp_rec false base_ty
              else
                pp_rec false base_ty
          | _ -> pp_rec false base_ty
        in
        str "typename " ++ base_str ++ str "::" ++ Id.print nested_id
    | Tvariant tys -> std_angle "variant" (pp_list (pp_rec false) tys)
    | Tshared_ptr t ->
        cpp_angle (sn ()).shared_ptr (pp_rec false t)
    | Tunique_ptr t ->
        cpp_angle (sn ()).unique_ptr (pp_rec false t)
    | Tvoid -> str "void"
    | Ttodo -> str "auto"
    | Tunknown -> str "UNKNOWN" (* TODO: BAD *)
    | Tany -> str "std::any"
  in
  h (pp_rec par t)

and pp_cpp_expr env args t =
  let apply st = pp_apply_cpp st args in
  match t with
  (* CPPvar' removed — all vars now use CPPvar *)
  | CPPvar id -> Id.print id
  | CPPglob (x, tys, Some ci) when ci.ci_inline <> None ->
    let custom = Option.get ci.ci_inline in
    let cmds = parse_numbered_args "t" (fun i -> CCty_arg i) custom in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print x) ^ " := " ^ custom) env None None tys [] [] [] [] cmds
  | CPPglob (x, _tys, _) when lookup_method_this_pos x <> None
    && (match is_registered_method x with
        | Some (epon_ref, _) ->
          (* Only use this-> for methods belonging to the current struct.
             Check if the method's eponymous type name matches current_struct_name.
             This prevents e.g. SigT::projT1 from being rendered as this->projT1()
             when generating code inside a different struct like Levenshtein. *)
          (match !current_struct_name with
           | Some sn ->
             let epon_name = Common.pp_global_name Type epon_ref in
             let sn_str = Pp.string_of_ppcmds sn in
             String.equal (String.capitalize_ascii epon_name) sn_str
           | None -> true)
        | None -> true) ->
    (* A bare reference to a method on the same struct (eta-reduced from \self. method self).
       Generate this->method() - a call to the method via this, not a function pointer. *)
    let method_name = Id.of_string (Common.pp_global_name Term x) in
    str "this->" ++ Id.print method_name ++ str "()"
  | CPPglob (x, _tys, _) when lookup_method_this_pos x <> None
    && (match is_registered_method x with
        | Some (epon_ref, _) ->
          (* Bare reference to a method on a DIFFERENT struct (used as a function value).
             Since C++ non-static member functions can't be passed as function pointers,
             wrap in a lambda that calls the method on its argument. *)
          (match !current_struct_name with
           | Some sn ->
             let epon_name = Common.pp_global_name Type epon_ref in
             let sn_str = Pp.string_of_ppcmds sn in
             not (String.equal (String.capitalize_ascii epon_name) sn_str)
           | None -> false)
        | None -> false) ->
    let method_name = Id.of_string (Common.pp_global_name Term x) in
    str "[](const auto &_x) { return _x->" ++ Id.print method_name ++ str "(); }"
  | CPPglob (x, tys, _) ->
    (* Determine the base name for a global reference *)
    let base_name = match x with
      | GlobRef.IndRef _ ->
        let (ns_name, needs_ns) = inductive_name_info_cached x in
        let type_name_str = str_global Type x in
        (* Check eponymous record FIRST because they can also be local *)
        if is_eponymous_record_cached x then
          (* Eponymous record: use capitalized name (merged into module struct).
             Use pp_global_name to get just the base name, not the qualified path. *)
          str (String.capitalize_ascii (Common.pp_global_name Type x))
        else if is_qualified_name type_name_str then
          (* Already qualified (e.g., C::t from module parameter): use as-is
             Do NOT lowercase - the qualifier (like module param C) should keep case *)
          str type_name_str
        else if needs_ns then
          if is_merged_inductive_cached x then
            (* Merged non-local inductive: use capitalized name directly *)
            ns_name
          else
            (* Unmerged non-local inductive: Wrapper::inner *)
            ns_name ++ str "::" ++ str type_name_str
        else
          (* Local inductive: use original name directly *)
          str type_name_str
      | GlobRef.VarRef _ ->
        (* Local variable reference - no prefix *)
        pp_global Term x
      | _ ->
        (* Check if this function is inside an eponymous template struct.
           If so, type args go on the struct name, not the function name. *)
        (match get_containing_eponymous_struct x, tys with
         | Some record_ref, _ :: _ ->
           (* Function inside eponymous template struct with type args:
              Generate StructName<int, ...>::template funcName<Args> for static methods
              We use placeholder types for the struct and actual args for the method. *)
           let struct_name = Common.pp_global_name Type record_ref in
           let func_name = Common.pp_global_name Term x in
           (* Get the number of template params for the struct *)
           let num_struct_params = match record_ref with
             | GlobRef.IndRef (kn, _) ->
               (match Table.get_ind_num_param_vars_opt kn with
                | Some n -> n
                | None -> 2)
             | _ -> 2
           in
           let placeholder_args = String.concat ", " (List.init num_struct_params (fun _ -> "int")) in
           let ty_args = pp_list (pp_cpp_type false []) tys in
           str (String.capitalize_ascii struct_name) ++ str "<" ++ str placeholder_args ++ str ">::template " ++ str func_name ++ str "<" ++ ty_args ++ str ">"
         | Some record_ref, [] ->
           (* Constant/function inside eponymous template struct with NO type args:
              This happens for non-parameterized constants like e_SUCCESS.
              Generate StructName<int, int>::constName as a workaround.
              We use 'int' as a placeholder type since the constant doesn't depend on the type params. *)
           let struct_name = Common.pp_global_name Type record_ref in
           let func_name = Common.pp_global_name Term x in
           (* Get the number of template params - use get_ind_num_param_vars_opt or default to 2 *)
           let num_params = match record_ref with
             | GlobRef.IndRef (kn, _) ->
               (match Table.get_ind_num_param_vars_opt kn with
                | Some n -> n
                | None -> 2)  (* Default to 2 params if not found *)
             | _ -> 2
           in
           let placeholder_args = String.concat ", " (List.init num_params (fun _ -> "int")) in
           str (String.capitalize_ascii struct_name) ++ str "<" ++ str placeholder_args ++ str ">::" ++ str func_name
         | None, _ ->
           (* Normal case: function not in eponymous struct *)
           let name = str_global Term x in
           let qualified_name = wrapper_qualify_name_cached x name in
           if qualified_name <> name then
             (* Name was qualified by wrapper module (e.g., Nat::div) *)
             str qualified_name
           else if needs_global_qualifier x then
             str "::" ++ pp_global Term x
           else
             pp_global Term x)
    in
    (* If this globref was rendered as a function accessor (Meyers singleton
       for template static data members), append () to call the accessor. *)
    (* If this globref was rendered as a function accessor (Meyers singleton
       for template static data members), append () to call the accessor.
       Uses modpath+label matching because functor application creates new
       constants with distinct canonical names. *)
    let is_accessor =
      let x_mp = modpath_of_r x in
      let x_lbl = label_of_r x in
      List.exists (fun (reg_mp, reg_lbl) ->
        Label.equal x_lbl reg_lbl &&
        (ModPath.equal x_mp reg_mp ||
         match Hashtbl.find_opt functor_app_sources x_mp with
         | Some source_mp -> ModPath.equal source_mp reg_mp
         | None -> false)
      ) !template_static_accessors
    in
    let base_name = if is_accessor
      then base_name ++ str "()"
      else base_name
    in
    (match tys, get_containing_eponymous_struct x with
    | [], _ -> apply base_name
    | _, Some _ -> apply base_name  (* Type args already handled in base_name *)
    | _ ->
      let ty_args = pp_list (pp_cpp_type false []) tys in
      apply base_name ++ str "<" ++ ty_args ++ str ">")
  | CPPnamespace (r, t) ->
      (* Use inductive_name_info to get proper namespace name *)
      let (name, _) = inductive_name_info_cached r in
      h (name ++ str "::" ++ pp_cpp_expr env args t)
  | CPPfun_call (CPPglob (n,tys, Some ci), ts) when ci.ci_inline <> None ->
    let s = Option.get ci.ci_inline in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
    let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args "t" (fun i -> CCty_arg i) s)
                      | _ -> prev @ [curr]) [] cmds in
    (* Compute expected argument types from the function's ML type *)
    let arg_types =
      try
        let ml_ty = Table.find_type n in
        (* Extract argument types from the ML function type *)
        let rec extract_arg_types = function
          | Miniml.Tarr (t1, t2) ->
            (* Don't include dummy types (like type class evidence) *)
            if Mlutil.isTdummy t1 then extract_arg_types t2
            else t1 :: extract_arg_types t2
          | _ -> []
        in
        let ml_arg_types = extract_arg_types ml_ty in
        (* Convert ML types to C++ types *)
        List.map (Translation.convert_ml_type_to_cpp_type env Refset'.empty []) ml_arg_types
      with _ -> []
    in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print n) ^ " := " ^ s) env None None tys [] (List.rev ts) arg_types [] cmds
  | CPPfun_call (CPPglob (n, tys, _), ts) when lookup_method_this_pos n <> None ->
    (* Transform function call to method call: f(a0, a1, ...) -> a[this_pos]->f(other_args)
       Handles both local method_candidates and cross-module registered methods.
       For methods with non-deducible template params (e.g., map's output element type),
       we include explicit type arguments, filtering out the inductive's own type vars
       since those are already known from the struct template. *)
    let method_name = Id.of_string (Common.pp_global_name Term n) in
    let this_pos = match lookup_method_this_pos n with Some p -> p | None -> 0 in
    let args_normal = List.rev ts in  (* Convert to normal order *)
    let (this_arg_opt, other_args) = Common.extract_at_pos this_pos args_normal in
    (match this_arg_opt with
     | Some this_arg ->
       let obj_s = pp_cpp_expr env args this_arg in
       let args_s = pp_list (pp_cpp_expr env args) other_args in
       (* Filter type args: remove the inductive's type params using positional
          information from the method registry. ind_tvar_positions contains the
          0-based indices into tys that correspond to the inductive's template
          params, which are already deducible from the receiver object. *)
       let ind_tvar_positions = lookup_method_ind_tvar_positions n in
       let filtered_tys = match tys with
         | [] -> []
         | _ ->
           List.filteri (fun i _ty -> not (List.mem i ind_tvar_positions)) tys
       in
       let (template_kw, ty_args_s) = match filtered_tys with
         | [] -> (mt (), mt ())
         | _ ->
           (* Use 'template' keyword for dependent template member calls.
              When the receiver type depends on an outer template parameter
              (e.g., shared_ptr<List<A>> where A is a template param),
              C++ requires: obj->template method<T>(...) *)
           (str "template ", str "<" ++ pp_list (pp_cpp_type false []) filtered_tys ++ str ">")
       in
       obj_s ++ str "->" ++ template_kw ++ Id.print method_name ++ ty_args_s ++ str "(" ++ args_s ++ str ")"
     | None ->
       (* Fallback - shouldn't happen for registered methods *)
       pp_cpp_expr env args (CPPglob (n, tys, None)) ++ str "()")
  | CPPfun_call (f, ts) ->
    let args_s = pp_list (pp_cpp_expr env args) (List.rev ts) in
    pp_cpp_expr env args f ++ str "(" ++ args_s ++ str ")"
  | CPPderef e ->
      str "*" ++ (pp_cpp_expr env args e)
  | CPPmove e ->
      str (sn ()).move ++ str "(" ++ (pp_cpp_expr env args e) ++ str ")"
  | CPPforward (ty, e) ->
      str (sn ()).forward ++ str "<" ++ pp_cpp_type false [] ty ++ str ">(" ++ (pp_cpp_expr env args e) ++ str ")"
  | CPPlambda (params, ret_ty, body, capture_by_value) ->
      (* Use [] for closed lambdas (no captured variables), [&] for ref capture, [=] for value capture *)
      let needs_capture = lambda_needs_capture params body in
      let capture_str = if not needs_capture then str "[](" else if capture_by_value then str "[=](" else str "[&](" in
      let (params_s, capture) =
        (match params with
        | [] -> str "void", capture_str
        | _ -> pp_list (fun (ty, id_opt) ->
            let id_s = match id_opt with None -> str "" | Some id -> Id.print id in
            (pp_cpp_type false [] ty) ++ spc () ++ id_s) (List.rev params), capture_str)
      in
      let body_s = pp_list_stmt (pp_cpp_stmt env args) body in
      begin match ret_ty with
      | Some ty ->
        h  (capture ++ params_s ++ str ") -> " ++ (pp_cpp_type false [] ty)) ++ str " {" ++ fnl () ++ body_s ++ fnl () ++ str "}"
      | None ->
        h (capture ++ params_s ++ str ")") ++ str " {" ++ fnl () ++ body_s ++ fnl () ++ str "}"
      end
  | CPPvisit -> str (sn ()).visit
  | CPPmk_shared t ->
      cpp_angle (sn ()).make_shared (pp_cpp_type false [] t)
  | CPPmk_unique t ->
      cpp_angle (sn ()).make_unique (pp_cpp_type false [] t)
  | CPPoverloaded ls ->
      let ls_s = pp_list_newline (pp_cpp_expr env args) ls in
      str (sn ()).overloaded ++ str " {" ++ fnl () ++ ls_s ++ fnl () ++ str "}"
  | CPPstructmk (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      let struct_name = match id with
        | GlobRef.IndRef _ when is_eponymous_record_cached id ->
            str (String.capitalize_ascii (Common.pp_global_name Type id))
        | _ -> pp_global Type id
      in
      struct_name ++  templates ++ str "::make(" ++ es_s ++ str ")"
  | CPPstruct (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      let struct_name = match id with
        | GlobRef.IndRef _ when is_eponymous_record_cached id ->
            str (String.capitalize_ascii (Common.pp_global_name Type id))
        | _ -> pp_global Type id
      in
      struct_name ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPstruct_id (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      Id.print id ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPget (e, id) ->
      (pp_cpp_expr env args e) ++ str "." ++ (Id.print id)
  | CPPget' (e, id) ->
      (pp_cpp_expr env args e) ++ str "->" ++ pp_global Type id
  | CPPstring s -> str ("\"" ^  (Pstring.to_string s) ^ "\"")
  | CPPparray (elems, _) -> str "{" ++ pp_list (pp_cpp_expr env args) (Array.to_list elems) ++ str "}"
  | CPPuint x ->
      (* Emit int literals with an explicit cast to the mapped C++ type for
         PrimInt63's [int].  A bare literal like [1] has type [int] in C++,
         which causes template-deduction failures when it is passed alongside
         a value whose type is the mapped type (e.g. [std::max(x, 1)] where
         [x] is [int64_t]).

         We use [Nametab.locate] to resolve PrimInt63's [int] to its
         [GlobRef.t], then [is_inline_custom] checks whether the user has
         registered a custom C++ type for it via
         [Crane Extract Inlined Constant int => "..."]. If so,
         [find_custom] retrieves that type string (e.g. ["int64_t"]) and we
         emit a functional-style cast like [int64_t(1)].  If [int] has no
         custom extraction or is not in scope, we fall back to the bare
         literal. *)
      let s = Uint63.to_string x in
      (try
        let gr = Nametab.locate (Libnames.qualid_of_string "int") in
        if is_inline_custom gr then
          let cpp_type = find_custom gr in
          str (cpp_type ^ "(" ^ s ^ ")")
        else str s
      with Not_found -> str s)
  | CPPfloat f -> str (Printf.sprintf "%h" (Float64.to_float f))
  | CPPrequires (ty_vars, exprs, type_reqs) ->
      let ty_vars_s = match ty_vars with [] -> mt () | _ ->
        str "(" ++ pp_list (fun (ty, id) -> (pp_cpp_type false [] ty) ++ spc () ++ Id.print id) ty_vars ++ str ") " in
      let type_reqs_s = prlist_with_sep fnl (fun ty ->
        str "  " ++ pp_cpp_type false [] ty ++ str ";") type_reqs in
      (* Use newlines without commas for requires clauses *)
      let exprs_s = prlist_with_sep fnl (fun (e1, e2) ->
        str "  { " ++ pp_cpp_expr env args e1 ++ str " } -> " ++ pp_cpp_expr env args e2 ++ str ";") exprs in
      str "requires " ++ ty_vars_s ++ str "{" ++ fnl () ++
        type_reqs_s ++
        (if type_reqs <> [] && exprs <> [] then fnl () else mt ()) ++
        exprs_s ++ fnl () ++ str "}"
  | CPPnew (ty, exprs) ->
      str "new " ++ pp_cpp_type false [] ty ++ str "(" ++ pp_list (pp_cpp_expr env args) exprs ++ str ")"
  | CPPshared_ptr_ctor (ty, expr) ->
      str (sn ()).shared_ptr ++ str "<" ++ pp_cpp_type false [] ty ++ str ">(" ++ pp_cpp_expr env args expr ++ str ")"
  | CPPunique_ptr_ctor (ty, expr) ->
      str (sn ()).unique_ptr ++ str "<" ++ pp_cpp_type false [] ty ++ str ">(" ++ pp_cpp_expr env args expr ++ str ")"
  | CPPthis -> str "this"
  | CPPmember (e, id) ->
      pp_cpp_expr env args e ++ str "." ++ Id.print id
  | CPParrow (e, id) ->
      pp_cpp_expr env args e ++ str "->" ++ Id.print id
  | CPPmethod_call (obj, method_name, call_args) ->
      pp_cpp_expr env args obj ++ str "->" ++ Id.print method_name ++
      str "(" ++ pp_list (pp_cpp_expr env args) call_args ++ str ")"
  | CPPqualified (e, id) ->
      pp_cpp_expr env args e ++ str "::" ++ Id.print id
  | CPPconvertible_to ty ->
      str "std::convertible_to<" ++ pp_cpp_type false [] ty ++ str ">"
  | CPPabort msg ->
      str "([&]() -> auto { throw " ++ str (sn ()).logic_error ++ str "(\"" ++ str msg ++ str "\"); })()"
  | CPPenum_val (ind, ctor) ->
      (* Generate EnumType::Constructor for enum class values.
         Use str_global for proper module qualification (e.g., Outer::color::Red). *)
      let full_name = str_global Type ind in
      str full_name ++ str "::" ++ Id.print ctor
  (* Low-level constructs for reuse optimization *)
  | CPPraw code -> str code
  | CPPbinop (op, lhs, rhs) ->
      str "(" ++ pp_cpp_expr env args lhs ++ str " " ++ str op ++ str " " ++ pp_cpp_expr env args rhs ++ str ")"
and pp_cpp_stmt env args = function
| Sreturn None -> str "return;"
| Sreturn (Some (CPPabort msg)) ->
    str "throw " ++ str (sn ()).logic_error ++ str "(\"" ++ str msg ++ str "\");"
| Sreturn (Some e) ->
    str "return " ++ pp_cpp_expr env args e ++ str ";"
| Sdecl (id, ty) -> (pp_cpp_type false [] ty) ++ str " " ++ Id.print id ++ str ";"
| Sasgn (id, Some ty, e) ->
    (pp_cpp_type false [] ty) ++ str " " ++ Id.print id ++ str " = " ++ (pp_cpp_expr env args e) ++ str ";"
| Sasgn (id, None, e) ->
    Id.print id ++ str " = " ++ (pp_cpp_expr env args e) ++ str ";"
| Sexpr e ->
    pp_cpp_expr env args e ++ str ";"
| Sthrow msg ->
    str "throw " ++ str (sn ()).logic_error ++ str "(\"" ++ str msg ++ str "\");"
| Sswitch (scrut, ind, branches) ->
    (* Generate switch statement for enum class matching.
       Use pp_global_name to get the unqualified base name. *)
    let base = Common.pp_global_name Type ind in
    let type_name = str base in
    let pp_branch (ctor, stmts) =
      str "case " ++ type_name ++ str "::" ++ Id.print ctor ++ str ": {" ++ fnl () ++
      pp_list_stmt (pp_cpp_stmt env args) stmts ++ fnl () ++
      str "}"
    in
    str "switch (" ++ pp_cpp_expr env args scrut ++ str ") {" ++ fnl () ++
    prlist_with_sep fnl pp_branch branches ++ fnl () ++
    str "}"
| Sassert (expr_str, comment_opt) ->
    (match comment_opt with
     | Some c -> str "// Precondition: " ++ str c ++ fnl () ++
                 str "assert(" ++ str expr_str ++ str ");"
     | None -> str "assert(" ++ str expr_str ++ str ");")
(* Reuse optimization constructs *)
| Sif (cond, then_stmts, else_stmts) ->
    str "if (" ++ pp_cpp_expr env args cond ++ str ") {" ++ fnl () ++
    pp_list_stmt (pp_cpp_stmt env args) then_stmts ++ fnl () ++
    str "} else {" ++ fnl () ++
    pp_list_stmt (pp_cpp_stmt env args) else_stmts ++ fnl () ++
    str "}"
| Sraw code -> str code
| Sassign_field (obj, field, e) ->
    pp_cpp_expr env args obj ++ str "." ++ Id.print field ++
    str " = " ++ pp_cpp_expr env args e ++ str ";"
| Scustom_case (typ,t,tyargs,cases,cmatch) ->
  let cmds = parse_custom_fixed "scrut" CCscrut cmatch in
  let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_custom_fixed "ty" CCty s)
                      | _ -> prev @ [curr]) [] cmds in
  let helper e f cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args e f s)
                      | _ -> prev @ [curr]) [] cmds in
  let cmds = helper "t" (fun i -> CCty_arg i) cmds in
  let cmds = helper "br" (fun i -> CCbody i) cmds in
  let helper2 e1 e2 f cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_custom_numbered_binders e1 e2 f s)
                      | _ -> prev @ [curr]) [] cmds in
  let cmds = helper2 "b" "a" (fun i j -> CCbr_var (i, j)) cmds in
  let cmds = helper2 "b" "t" (fun i j -> CCbr_var_ty (i, j)) cmds in
  pp_custom ("custom match for " ^ (Pp.string_of_ppcmds (pp_cpp_type false [] typ)) ^ " := " ^ cmatch) env (Some typ) (Some t) tyargs cases [] [] [] cmds

(* Check if a C++ type is concrete (can be used in any_cast).
   Type variables and unknown types are not concrete - we can't cast to them. *)
and is_concrete_cpp_type = function
  | Tvar _ -> false  (* Type variables - can't cast to these *)
  | Tunknown | Ttodo | Tany -> false
  | Tmod (_, inner) -> is_concrete_cpp_type inner
  | _ -> true

(* Check if a C++ expression is a method call that returns std::any.
   Returns true for methods of indexed inductives (GADTs) whose return type is erased.

   Method calls can appear as either:
   1. CPPmethod_call - explicit method call syntax (obj->method(args))
   2. CPPfun_call with a registered method - these are transformed to method call
      syntax at print time, but in the AST they're still function calls

   IMPORTANT: We only return true for methods registered as returning std::any.
   These are methods of indexed inductives (GADTs). Regular polymorphic methods
   (like fst) have type variables that become template parameters, not std::any. *)
and expr_is_any_returning_method = function
  | CPPmethod_call (CPPglob (n, _, _), _, _) -> method_returns_any n
  | CPPfun_call (CPPglob (n, _, _), _) when lookup_method_this_pos n <> None -> method_returns_any n
  | _ -> false

(* Wrap an expression with any_cast if needed.
   If the expression is a method call on an indexed inductive (GADT) that returns std::any,
   and the expected type is known and concrete, wrap with any_cast to extract the value.
   This is needed because indexed inductives have type-erased return types in C++. *)
and wrap_any_cast_if_needed expr expr_printed expected_ty vl =
  if expr_is_any_returning_method expr && is_concrete_cpp_type expected_ty then
    str (sn ()).any_cast ++ str "<" ++ pp_cpp_type false vl expected_ty ++ str ">(" ++ expr_printed ++ str ")"
  else
    expr_printed

and pp_custom custom env typ t tyargs cases args arg_types vl cmds =
  let pp cmd = match cmd with
    | CCstring s -> str s
    | CCscrut ->(match t with
        | Some t_expr ->
          let t_printed = pp_cpp_expr env [] t_expr in
          (* Append string literal suffix for custom inlined operations.
             Using C++ string literal operators: "hello"s (std) or "hello"_s (BDE). *)
          let t_printed = match t_expr with
            | CPPstring _ -> t_printed ++ str (sn ()).str_suffix
            | _ -> t_printed
          in
          (* Wrap scrutinee with any_cast if it's a method call returning std::any *)
          (match typ with
           | Some expected_ty -> wrap_any_cast_if_needed t_expr t_printed expected_ty vl
           | None -> t_printed)
        | None -> assert false)
    | CCty ->(match typ with
        | Some typ -> pp_cpp_type false vl typ
        | None -> assert false)
    | CCbody i -> (try
      let (_,_,ss) = List.nth cases i in
       pp_list_stmt (pp_cpp_stmt env []) ss
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound case body in"; print_endline custom; assert false)
    | CCty_arg i ->(try pp_cpp_type false vl (List.nth tyargs i)
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound type argument in"; print_endline custom; assert false)
    | CCbr_var (i, j) -> (try
      let (ids,_,_) = List.nth cases i in
      let (id,_) = List.nth ids j in
      Id.print id
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound case branch variable in"; print_endline custom; assert false)
    | CCbr_var_ty (i, j) -> (try
      let (ids,_,_) = List.nth cases i in
      let (_,ty) = List.nth ids j in
      pp_cpp_type false vl ty
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound case branch type argument in"; print_endline custom; assert false)
    | CCarg i -> (try
        let arg_expr = List.nth args i in
        let arg = pp_cpp_expr env [] arg_expr in
        (* Append string literal suffix for custom inlined operations.
           Using C++ string literal operators: "hello"s (std) or "hello"_s (BDE).
           This allows string literals to support operations like + (concatenation)
           or .length() without explicit std::string() wrapping. *)
        let arg = match arg_expr with
          | CPPstring _ -> arg ++ str (sn ()).str_suffix
          | _ -> arg
        in
        (* Wrap with any_cast if this is a method call returning std::any *)
        (match List.nth_opt arg_types i with
         | Some expected_ty -> wrap_any_cast_if_needed arg_expr arg expected_ty vl
         | None -> arg)
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound term argument in"; print_endline custom; assert false) in
  List.fold_left (fun prev c -> prev ++ pp c) (mt ()) cmds

let pp_template_type = function
  | TTtypename -> str "typename"
  | TTtypename_default _ -> str "typename"
  | TTfun (dom, cod) -> str "MapsTo<" ++ pp_cpp_type false [] cod  ++ str ", " ++ pp_list (pp_cpp_type false []) dom ++ str ">"
  | TTconcept (concept) -> pp_global Type concept

(* Print a complete template parameter including name and optional default *)
let pp_template_param (tt, id) =
  match tt with
  | TTtypename_default default_ty ->
    str "typename" ++ spc () ++ Id.print id ++ str " = " ++ pp_cpp_type false [] default_ty
  | _ -> pp_template_type tt ++ spc () ++ Id.print id

(* pp_cpp_field takes optional struct_name for printing constructors *)
let rec pp_cpp_field ?(struct_name : Pp.t option) env = function
| Fvar (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ Id.print id ++ str ";")
| Fvar' (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str ";")
| Ffundef (id, ret_ty, params, body) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) params
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
      h ((pp_cpp_type false [] ret_ty) ++ str " " ++ Id.print id ++ pp_par true params_s ++ str "{") ++ fnl () ++ body_s ++ str "}"
| Ffundecl (id, ret_ty, params) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) (List.rev params)
    in h ((pp_cpp_type false [] ret_ty) ++ str " " ++ Id.print id ++ pp_par true params_s) ++ str ";"
| Fmethod { mf_name; mf_tparams; mf_ret_type; mf_params; mf_body; mf_is_const; mf_is_static } ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) mf_params
    in
    let const_s = if mf_is_const then str " const" else mt () in
    let static_s = if mf_is_static then str "static " else mt () in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) mf_body in
    let template_s = match mf_tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list pp_template_param mf_tparams in
        str "template <" ++ args ++ str ">" ++ fnl ()
    in
    template_s ++
      h (static_s ++ (pp_cpp_type false [] mf_ret_type) ++ str " " ++ Id.print mf_name ++ pp_par true params_s ++ const_s ++ str " {") ++ fnl () ++ body_s ++ str "}"
| Fconstructor (params, init_list, is_explicit) ->
    let sname = match struct_name with Some s -> s | None -> str "UNKNOWN_STRUCT" in
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) params
    in
    let init_s = match init_list with
      | [] -> mt ()
      | _ -> str " : " ++ pp_list (fun (member, expr) ->
              Id.print member ++ str "(" ++ pp_cpp_expr env [] expr ++ str ")") init_list
    in
    let explicit_s = if is_explicit then str "explicit " else mt () in
    h (explicit_s ++ sname ++ pp_par true params_s ++ init_s ++ str " {}")
| Fnested_struct (id, fields) ->
    let fields_s = pp_cpp_fields_with_vis ~struct_name:(Id.print id) env fields in
    h (str "struct " ++ Id.print id ++ str " {") ++ fnl () ++ fields_s ++ fnl () ++ str "};"
| Fnested_using (id, ty) ->
    h (str "using " ++ Id.print id ++ str " = " ++ pp_cpp_type false [] ty ++ str ";")
| Fdeleted_ctor ->
    let sname = match struct_name with Some s -> s | None -> str "UNKNOWN_STRUCT" in
    h (sname ++ str "() = delete;")

(* Helper to print fields with visibility sections *)
and pp_cpp_fields_with_vis ?(struct_name : Pp.t option) env fields =
  (* Group consecutive fields by visibility *)
  let rec group_by_vis current_vis acc result = function
    | [] ->
        if acc = [] then List.rev result
        else List.rev ((current_vis, List.rev acc) :: result)
    | (fld, vis) :: rest ->
        if vis = current_vis then
          group_by_vis current_vis (fld :: acc) result rest
        else
          let result' = if acc = [] then result
                       else (current_vis, List.rev acc) :: result in
          group_by_vis vis [fld] result' rest
  in
  let groups = group_by_vis VPublic [] [] fields in
  (* Check if we need visibility labels (only if mixed or all private) *)
  let needs_labels = match groups with
    | [] -> false
    | [(VPublic, _)] -> false  (* All public - struct default is public *)
    | _ -> true  (* Mixed or all private *)
  in
  let pp_group (vis, flds) =
    if needs_labels then
      let vis_str = match vis with VPublic -> "public:" | VPrivate -> "private:" in
      str vis_str ++ fnl () ++
      pp_list_stmt (pp_cpp_field ?struct_name env) flds
    else
      pp_list_stmt (pp_cpp_field ?struct_name env) flds
  in
  prlist_with_sep fnl pp_group groups

let rec pp_cpp_decl env =
function
| Dtemplate (temps, cstr, decl) ->
    let args = pp_list pp_template_param temps in
    h (str "template <" ++ args ++ str ">")
    ++ (match cstr with
        | None -> fnl ()
        | Some c -> pp_cpp_expr env [] c ++ fnl ())
    ++ pp_cpp_decl env decl
| Dnspace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
    h (str "namespace " ++ str "{") ++ fnl () ++ ds ++ fnl () ++ str "};"
| Dnspace (Some id, decls) ->
    let struct_name_str = match id with
      | GlobRef.IndRef _ -> String.capitalize_ascii (str_global Type id)
      | _ -> string_of_ppcmds (pp_global Type id)
    in
    let has_pending = Hashtbl.mem pending_wrapper_decls struct_name_str in
    (* MERGE: When a Dnspace has a single Dstruct and no pending wrapper declarations,
       merge the inner struct into the wrapper.
       This eliminates the redundant nesting: struct Nat { struct nat { ... }; }
       becomes just struct Nat { ... }.
       When there ARE pending wrapper declarations (e.g., module functions like rev),
       keep the two-level structure so wrapper functions can reference the template class. *)
    (match decls, has_pending with
    | [Dstruct { ds_fields = fields; ds_tparams = []; _ }], false ->
      (* MERGE non-template: struct Nat { ... } *)
      let struct_name = str struct_name_str in
      let f_s = with_render_ctx
        ~setup:(fun () -> in_struct_context := true)
        (fun () -> pp_cpp_fields_with_vis ~struct_name env fields) in
      str "struct " ++ struct_name ++ str " {" ++ fnl ()
        ++ f_s ++ fnl () ++ str "};"
    | [Dstruct { ds_fields = fields; ds_tparams = temps; ds_constraint = cstr; _ }], false ->
      (* MERGE template: template<typename A> struct List { ... } *)
      let struct_name = str struct_name_str in
      let f_s = with_render_ctx
        ~setup:(fun () -> in_struct_context := true; in_template_struct := true)
        (fun () -> pp_cpp_fields_with_vis ~struct_name env fields) in
      let args = pp_list pp_template_param temps in
      h (str "template <" ++ args ++ str ">")
      ++ (match cstr with
          | None -> fnl ()
          | Some c -> pp_cpp_expr env [] c ++ fnl ())
      ++ str "struct " ++ struct_name ++ str " {" ++ fnl ()
        ++ f_s ++ fnl () ++ str "};"
    | _ ->
      (* No merge: keep wrapper struct (has pending decls or multiple children) *)
      let ds = with_render_ctx
        ~setup:(fun () -> in_struct_context := true)
        (fun () -> pp_list_stmt (pp_cpp_decl env) decls) in
      let pending_fwd = match Hashtbl.find_opt pending_wrapper_decls struct_name_str with
        | Some specs ->
          Hashtbl.remove pending_wrapper_decls struct_name_str;
          fnl () ++ specs
        | None -> mt ()
      in
      h (str "struct " ++ str struct_name_str ++ str " {") ++ fnl () ++ ds ++ pending_fwd ++ fnl () ++ str "};")
| Dfundef (ids, ret_ty, params, body) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) (List.rev params)
    in
    let base_name = prlist_with_sep (fun () -> str "::") (fun (n, tys) ->
      (match tys with
      | [] -> pp_global Type n
      | _ -> pp_global Type n ++ str "<" ++ (pp_list (pp_cpp_type false []) tys) ++ str ">")) ids
      in
    (* If generating out-of-struct definitions, prepend struct name.
       Skip for VarRef (lifted declarations like _foo_aux) which don't belong to the struct. *)
    let is_lifted = match ids with
      | (GlobRef.VarRef _, _) :: _ -> true
      | _ -> false in
    let name = match !current_struct_name with
      | Some struct_name when not !in_struct_context && not is_lifted -> struct_name ++ str "::" ++ base_name
      | _ -> base_name
      in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    (* DESIGN: Static member functions for struct context
       When a function is inside a struct (module), it needs to be static because:
       1. Structs don't have implicit 'this' for free functions
       2. Qualified names (Module::func) indicate out-of-line member definitions
       3. Template functions at module scope are static helpers

       Heuristics for detecting struct membership:
       - Multiple IDs: qualified name like MakeMap<K,V>::find indicates member
       - Non-empty tys: template function likely a member helper
       - in_struct_context: explicitly tracking struct nesting
       - current_struct_name set: generating out-of-struct definitions (no static) *)
    let is_qualified = List.length ids > 1 || (match ids with | [(_, tys)] when tys <> [] -> true | _ -> false) in
    let is_struct_member = is_qualified || !in_struct_context in
    let is_out_of_struct_def = match !current_struct_name with | Some _ -> not !in_struct_context | None -> false in
    let static_kw = if is_struct_member && not is_out_of_struct_def then str "static " else mt () in
      h (static_kw ++ (pp_cpp_type false [] ret_ty) ++ str " " ++ name ++ pp_par true params_s) ++ str "{" ++ body_s ++ str "}"
| Dfundecl (ids, ret_ty, params) ->
    let params_s =
      pp_list (fun (id, ty) ->
        match id with
        | Some id -> (pp_cpp_type false [] ty) ++ str " " ++ Id.print id
        | None -> pp_cpp_type false [] ty) (List.rev params) in
    let name = prlist_with_sep (fun () -> str "::") (fun (n, tys) ->
      (match tys with
      | [] -> pp_global Type n
      | _ -> pp_global Type n ++ str "<" ++ (pp_list (pp_cpp_type false []) tys) ++ str ">")) ids
      in
    (* Add static for struct member functions *)
    (* Check if qualified name (out-of-line definition) OR inside a struct context *)
    let is_qualified = List.length ids > 1 || (match ids with | [(_, tys)] when tys <> [] -> true | _ -> false) in
    let is_struct_member = is_qualified || !in_struct_context in
    let static_kw = if is_struct_member then str "static " else mt () in
    h (static_kw ++ (pp_cpp_type false [] ret_ty) ++ str " " ++ name ++ pp_par true params_s) ++ str ";"
| Dstruct { ds_ref = id; ds_fields = fields; ds_tparams = tparams; ds_constraint = cstr } ->
    (* Struct name for inductive types.
       Regular inductives use their original Rocq name.
       EXCEPTION 1: Records keep their original case.
       EXCEPTION 2: Eponymous records use the capitalized name directly.
       Check eponymous FIRST, then records, then default. *)
    let struct_name = match id with
      | GlobRef.IndRef _ when is_eponymous_record_cached id ->
          (* Use pp_global_name to get just the base name, not the qualified path. *)
          str (String.capitalize_ascii (Common.pp_global_name Type id))
      | GlobRef.IndRef _ when is_record_cached id ->
          (* Records keep original case - no namespace wrapper *)
          pp_global Type id
      | GlobRef.IndRef _ ->
          pp_global Type id
      | _ -> pp_global Type id
    in
    let f_s = match tparams with
      | [] -> pp_cpp_fields_with_vis ~struct_name env fields
      | _ -> with_render_ctx
        ~setup:(fun () -> in_template_struct := true)
        (fun () -> pp_cpp_fields_with_vis ~struct_name env fields)
    in
    let tmpl = match tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list pp_template_param tparams in
        h (str "template <" ++ args ++ str ">")
        ++ (match cstr with
            | None -> fnl ()
            | Some c -> pp_cpp_expr env [] c ++ fnl ())
    in
    tmpl ++ str "struct " ++ struct_name ++ str " {" ++ fnl () ++ f_s ++ fnl () ++ str "};"
| Dstruct_decl id ->
    str "struct " ++ pp_global Type id ++ str ";"
| Dusing (id, ty) ->
    str "using " ++ pp_global Type id ++ str " = " ++ pp_cpp_type false [] ty ++ str ";"
| Dasgn (id, ty, e) ->
    (* DESIGN: Static inline member variables for module constants
       In C++17, static data members can be defined inside the class with 'inline'.

       Why:
       - 'static': This is a class/struct member variable, not an instance variable
       - 'inline': Allows definition in header file without violating ODR (One Definition Rule)
       - Enables constant propagation by the compiler since definitions are available

       Without 'inline', multiple .cpp files including this header would cause linker errors
       due to duplicate symbol definitions.

       Note: When in_struct_context and the expression contains lambdas, we wrap the
       initializer in an IIFE (Immediately Invoked Function Expression) to allow
       nested lambdas to use [&] capture. This is necessary because:
       - C++ forbids capture-default in "non-local" lambdas
       - ALL lambdas directly in a static inline initializer are "non-local"
       - But by wrapping in []() { return expr; }(), inner lambdas are now "local" *)
    let expr_pp = pp_cpp_expr env [] e in
    if !in_template_struct then begin
      (* DESIGN: Static data members in template structs use lazy initialization.
         Template static inline members have unordered dynamic initialization relative
         to other inline variables, causing static init order issues when accessed from
         outside the template. Use a function with a local static (Meyers' singleton)
         to guarantee initialization on first use. *)
      (let mp = modpath_of_r id in
       let lbl = label_of_r id in
       template_static_accessors := (mp, lbl) :: !template_static_accessors);
      h (str "static const " ++ (pp_cpp_type false [] ty) ++ str "& " ++ pp_global Type id ++ str "() {") ++ fnl () ++
      str "  static const " ++ (pp_cpp_type false [] ty) ++ str " v = " ++ expr_pp ++ str ";" ++ fnl () ++
      str "  return v;" ++ fnl () ++
      str "}"
    end
    else begin
      let static_kw = if !in_struct_context then str "static inline " else mt () in
      (* Wrap in IIFE only when in struct context AND the expression contains lambdas.
         This is needed because C++ forbids capture-default [&] in non-local lambdas.
         If there are no lambdas, no wrapping is needed. *)
      let needs_iife = !in_struct_context && expr_contains_capturing_lambda e in
      let wrapped_expr = if needs_iife then
        str "[]() {" ++ fnl () ++ str "return " ++ expr_pp ++ str ";" ++ fnl () ++ str "}()"
      else
        expr_pp
      in
      h (static_kw ++ (pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str " = " ++ wrapped_expr ++ str ";")
    end
| Ddecl (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str ";")
| Dconcept (id, cstr) ->
    (* For hoisted concepts, use only the simple base name without module qualification *)
    let simple_name = Common.pp_global_name Type id in
    (* Extract just the last component after :: if present *)
    let last_component = match String.rindex_opt simple_name ':' with
      | Some idx when idx > 0 && idx < String.length simple_name - 1 && simple_name.[idx-1] = ':' ->
          String.sub simple_name (idx + 1) (String.length simple_name - idx - 1)
      | _ -> simple_name
    in
    h (str "concept " ++ str last_component ++ str " = " ++ pp_cpp_expr env [] cstr ++ str ";")
| Dstatic_assert (e, so) ->
    (match so with
    | None -> h (str "static_assert(" ++ pp_cpp_expr env [] e ++ str ");")
    | Some s -> h (str "static_assert(" ++ pp_cpp_expr env [] e ++ str ", \"" ++ str s ++ str "\");"))
| Denum { de_ref = name; de_ctors = ctors; _ } ->
    let struct_name = match name with
      | GlobRef.IndRef _ ->
          str (Common.pp_global_name Type name)
      | _ -> pp_global Type name
    in
    let ctors_s = prlist_with_sep (fun () -> str "," ++ fnl () ++ str "  ")
      (fun id -> Id.print id) ctors in
    str "enum class " ++ struct_name ++ str " {" ++ fnl () ++ str "  " ++ ctors_s ++ fnl () ++ str "};"

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let pp_type par vl t =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] t in
  pp_cpp_type par vl cty

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let cut2 () = brk (0,-100000) ++ brk (0,0)

let pp_cpp_ind kn ind =
  let names =
  Array.mapi (fun i p -> GlobRef.IndRef (kn,i))
    ind.ind_packets
  in
  let cnames =
    Array.mapi
      (fun i p ->
         Array.mapi (fun j _ -> GlobRef.ConstructRef ((kn,i),j+1))
           p.ip_types)
      ind.ind_packets in
  match ind.ind_kind with
  | Record fields | TypeClass fields -> mt ()
  | _ ->
  let rec pp i =
    if i >= Array.length ind.ind_packets then mt ()
    else
      let ip = (kn,i) in
      let p = ind.ind_packets.(i) in
      if is_custom (GlobRef.IndRef ip) then pp (i+1)
      else if is_enum_cached (GlobRef.IndRef ip) then pp (i+1)  (* Enums have no .cpp body *)
      else
        (* Compute parameter-only type vars (same as in pp_cpp_ind_header) *)
        let param_sign = List.firstn ind.ind_nparams p.ip_sign in
        let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
        let param_vars = List.firstn num_param_vars p.ip_vars in
        pp_cpp_decl (empty_env ()) (gen_ind_cpp param_vars names.(i) cnames.(i) p.ip_types) ++ pp (i+1)
  in
  pp 0

let pp_tydef ids name def =
  let templates = match ids with
  | [] -> mt ()
  | _ -> str "template <" ++
          List.fold_left (fun s v -> s ++ v) (mt ())
            (List.mapi (fun i v -> if i = 0 then str "typename " ++ Id.print v else str ", typename " ++ Id.print v) ids)
          ++ str "> " in
  hov 2 (templates ++ str "using " ++ name ++ def ++ str ";")

let pp_decl = function
    | Dtype (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_eponymous_record_projection r ->
          (* Skip - this is a projection for an eponymous record merged into module struct *)
          mt ()
    | Dterm (r,_,_) when is_suppressed_projection r -> mt ()
    | Dind (kn,i) -> mt ()  (* Inductives are fully defined in headers *)
    | Dtype (r, l, t) -> mt ()
    | Dterm (r, a, Tglob (ty, args,e)) when is_monad ty ->
          let defs = List.filter (fun (_,_,l) -> l == []) (gen_dfuns (Array.of_list [r], Array.of_list [a], Array.of_list [Miniml.Tglob (ty, args,e)])) in
          pp_list_stmt (fun(ds, env, _) -> pp_cpp_decl env ds) defs
    | Dterm (r, _, _) when List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r') !method_candidates ->
          (* Skip - this function is generated as a method on the eponymous type *)
          mt ()
    | Dterm (r, _, _) when is_registered_method r <> None ->
          (* Skip - this function is registered as a method in another module *)
          mt ()
    | Dterm (r, a, t) when is_typeclass_instance a t ->
          (* Type class instances: fully defined in header, skip in implementation *)
          mt ()
    | Dterm (r, a, t) ->
        let (ds, env, tvars) = gen_decl_for_pp r a t in
        begin match ds, tvars with
        | Some ds , [] -> pp_cpp_decl env ds
        | _ , _ -> mt ()
        end
    | Dfix (rv,defs,typs) ->
          let (rv, defs, typs) = filter_dfix rv defs typs in
          if Array.length rv = 0 then mt ()
          else
          let defs = List.filter (fun (_,_,l) -> l == []) (gen_dfuns (rv, defs, typs)) in
          pp_list_stmt (fun(ds, env, _) -> pp_cpp_decl env ds) defs

let pp_cpp_ind_header kn ind =
  let names =
  Array.mapi (fun i p -> GlobRef.IndRef (kn,i))
    ind.ind_packets
  in
  let cnames =
    Array.mapi
      (fun i p ->
         Array.mapi (fun j _ -> GlobRef.ConstructRef ((kn,i),j+1))
           p.ip_types)
      ind.ind_packets in
  match ind.ind_kind with
  | TypeClass fields ->
      (* Type classes become C++ concepts *)
      (* Skip if concepts have been hoisted or we're inside a struct *)
      if !in_struct_context || !concepts_hoisted then mt ()
      else pp_cpp_decl (empty_env ()) (gen_typeclass_cpp names.(0) fields ind.ind_packets.(0))
  | Record fields ->
      (* Check if this is an eponymous record being merged into module struct *)
      let ind_ref = names.(0) in
      (match !eponymous_record with
      | Some (epon_ref, _, _) when Environ.QGlobRef.equal Environ.empty_env ind_ref epon_ref ->
          mt ()  (* Skip - merged into module struct *)
      | _ ->
          pp_cpp_decl (empty_env ()) (gen_record_cpp names.(0) fields ind.ind_packets.(0)))
  | _ ->
    (* DESIGN: Mutual inductive support with forward declarations
       Rocq supports mutually recursive inductive types. In C++, this requires:
       1. Forward declarations so each struct can reference the others
       2. Full definitions immediately after

       Non-parameterized example:
         struct Tree;  // forward decl
         struct Node;  // forward decl
         struct Tree { ... Node usage ... };
         struct Node { ... Tree usage ... };

       Parameterized example (tree A / forest A):
         template <typename A> struct tree;    // forward decl
         template <typename A> struct forest;  // forward decl
         template <typename A> struct tree { ... forest<A> usage ... };
         template <typename A> struct forest { ... tree<A> usage ... };

       The forward declaration must carry the same template parameters as the
       full definition; a plain [struct tree;] followed by
       [template <typename A> struct tree { ... }] is a C++ error
       ("redefinition as different kind of symbol"). *)
    let is_mutual = Array.length ind.ind_packets > 1 in
    let forward_decls =
      if is_mutual then
        let rec fwd i =
          if i >= Array.length ind.ind_packets then mt ()
          else
            let ip = (kn,i) in
            if is_custom (GlobRef.IndRef ip) then fwd (i+1)
            else
              let p = ind.ind_packets.(i) in
              (* Compute template parameters the same way as the full
                 definition (see param_vars below at the struct gen site).
                 Parameters (before the colon) become template params;
                 indices (after the colon) are erased. *)
              let param_sign = List.firstn ind.ind_nparams p.ip_sign in
              let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
              let param_vars = List.firstn num_param_vars p.ip_vars in
              (* Use the same name as the struct definition (see Dstruct
                 printing below) so forward declarations match their definitions. *)
              let name = pp_global Type names.(i) in
              let tmpl = match param_vars with
                | [] -> mt ()
                | vars ->
                  str "template <"
                  ++ prlist_with_sep (fun () -> str ", ")
                       (fun v -> str "typename " ++ Id.print v) vars
                  ++ str "> "
              in
              tmpl ++ str "struct " ++ name ++ str ";" ++ fnl () ++ fwd (i+1)
        in
        fwd 0
      else mt ()
    in
    (* Helper to find method candidates from current_structure_decls for a given inductive.
       IMPORTANT: Skip functions whose signatures reference type aliases (Dtype) from the
       same module. This prevents issues like `heap_delete_max : tree -> priqueue` becoming
       a method on `tree`, where `priqueue` is a type alias not visible from inside `tree`. *)
    let find_methods_for_inductive ind_ref =
      let ind_modpath = modpath_of_r ind_ref in
      (* First, collect all type aliases (Dtype) defined in the same module.
         These are types like `priqueue := list tree` that become `using` declarations.
         Methods on nested inductives can't reference these (visibility issue). *)
      let module_type_aliases = ref [] in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dtype (r, _, _)) when ModPath.equal (modpath_of_r r) ind_modpath ->
            module_type_aliases := r :: !module_type_aliases
        | _ -> ()
      ) !current_structure_decls;
      (* Collect all inductives that come AFTER ind_ref in declaration order.
         Methods that reference these would cause forward declaration issues since
         the method body pattern-matches on variants that aren't defined yet. *)
      let forward_inductives = ref [] in
      let seen_current = ref false in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dind (fwd_kn, fwd_ind)) ->
          Array.iteri (fun j _p ->
            let fwd_ref = GlobRef.IndRef (fwd_kn, j) in
            if Environ.QGlobRef.equal Environ.empty_env fwd_ref ind_ref then
              seen_current := true
            else if !seen_current then
              forward_inductives := fwd_ref :: !forward_inductives
          ) fwd_ind.ind_packets
        | _ -> ()
      ) !current_structure_decls;
      (* Check if a type references any of the excluded references (type aliases or forward inductives) *)
      let excluded_refs = !module_type_aliases @ !forward_inductives in
      let rec refs_excluded ty =
        match ty with
        | Miniml.Tglob (r, args, _) ->
            List.exists (Environ.QGlobRef.equal Environ.empty_env r) excluded_refs ||
            List.exists refs_excluded args
        | Miniml.Tarr (t1, t2) -> refs_excluded t1 || refs_excluded t2
        | Miniml.Tmeta {contents = Some t} -> refs_excluded t
        | _ -> false
      in
      (* Check if function comes from the same Rocq module as the inductive *)
      let same_module r = ModPath.equal (modpath_of_r r) ind_modpath in
      let methods = ref [] in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dterm (r, body, ty)) ->
          (* Skip if function signature references an excluded type (alias or forward inductive) *)
          if same_module r && not (refs_excluded ty) && Method_registry.body_safe_for_method body then
            (match Method_registry.find_epon_arg_pos ind_ref ty with
            | Some (pos, ind_tvar_positions) ->
              methods := (r, body, ty, pos) :: !methods;
              register_method r ind_ref pos ~ind_tvar_positions ();
              Method_registry.add_candidate (get_method_registry ()) ind_ref (r, body, ty, pos)
            | None -> ())
        | SEdecl (Dfix (rv, defs, typs)) ->
          Array.iteri (fun i r ->
            let ty = typs.(i) in
            (* Skip if function signature references an excluded type (alias or forward inductive) *)
            if same_module r && not (refs_excluded ty) && Method_registry.body_safe_for_method defs.(i) then begin
              let body = defs.(i) in
              match Method_registry.find_epon_arg_pos ind_ref ty with
              | Some (pos, ind_tvar_positions) ->
                methods := (r, body, ty, pos) :: !methods;
                register_method r ind_ref pos ~ind_tvar_positions ();
                Method_registry.add_candidate (get_method_registry ()) ind_ref (r, body, ty, pos)
              | None -> ()
            end
          ) rv
        | _ -> ()
      ) !current_structure_decls;
      !methods
    in
    let rec pp i =
      if i >= Array.length ind.ind_packets then mt ()
      else
        let ip = (kn,i) in
        let p = ind.ind_packets.(i) in
        if is_custom (GlobRef.IndRef ip) then pp (i+1)
        else
          (* Get method candidates: first check if set via SEmodule processing,
             otherwise find from sibling declarations in current_structure_decls.
             IMPORTANT: Only use find_methods_for_inductive for top-level inductives.
             For inductives nested inside modules, only the eponymous type gets methods.
             This prevents issues like tree inside Priqueue getting methods that return
             priqueue (a sibling type alias not visible from inside tree). *)
          let ind_ref = GlobRef.IndRef ip in
          (* Check if ind_ref appears inside any SEmodule in current_structure_decls.
             This detects when an inductive is declared inside a submodule. *)
          let is_inside_submodule_decl =
            let rec find_in_module_expr = function
              | MEstruct (_, sel') ->
                  List.exists (fun (_l', se') ->
                    match se' with
                    | SEdecl (Dind (kn', ind')) ->
                        let rec check_packets i' =
                          if i' >= Array.length ind'.ind_packets then false
                          else
                            let r = GlobRef.IndRef (kn', i') in
                            Environ.QGlobRef.equal Environ.empty_env r ind_ref || check_packets (i' + 1)
                        in
                        check_packets 0
                    | _ -> false
                  ) sel'
              | MEfunctor (_, _, me) -> find_in_module_expr me
              | MEapply (me, _) -> find_in_module_expr me
              | MEident _ -> false
            in
            List.exists (fun (_l, se) ->
              match se with
              | SEmodule m -> find_in_module_expr m.ml_mod_expr
              | _ -> false
            ) !current_structure_decls
          in
          let methods = match !eponymous_type_ref with
            | Some epon_ref when Environ.QGlobRef.equal Environ.empty_env ind_ref epon_ref ->
                !method_candidates
            | _ when not !in_struct_context && not is_inside_submodule_decl ->
                (* For top-level inductives only, find methods from sibling declarations *)
                find_methods_for_inductive ind_ref
            | _ ->
                (* Inside a module, non-eponymous inductives don't get methods *)
                []
          in
          (* Also include method candidates from the registry (e.g., Nat::add from
             Corelib.Init.Nat for nat defined in Corelib.Init.Datatypes).
             Deduplicate: skip any that are already in the methods list. *)
          let methods =
            let reg_candidates = Method_registry.get_candidates (get_method_registry ()) ind_ref in
            if reg_candidates = [] then methods
            else
              let existing = List.map (fun (r, _, _, _) -> r) methods in
              let new_methods = List.filter (fun (r, _, _, _) ->
                not (List.exists (Environ.QGlobRef.equal Environ.empty_env r) existing)
              ) reg_candidates in
              methods @ new_methods
          in
          (* Compute parameter-only type vars.
             Parameters (before the colon) become template params.
             Indices (after the colon) are erased.
             ind.ind_nparams gives the number of Rocq parameters.
             p.ip_sign covers all args (params + indices).
             Count Keep entries in the first nparams positions to get param type var count. *)
          let param_sign = List.firstn ind.ind_nparams p.ip_sign in
          let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
          let param_vars = List.firstn num_param_vars p.ip_vars in
          (* Register methods that return std::any (for indexed inductives).
             A method returns std::any if its ML return type becomes an unnamed Tvar
             (indicating type erasure) after C++ conversion. *)
          List.iter (fun (r, _body, ty, _pos) ->
            (* Get return type from ML type *)
            let rec get_return_type = function
              | Miniml.Tarr (_, t2) -> get_return_type t2
              | ret -> ret
            in
            let ret_ml = get_return_type ty in
            (* Convert to C++ type with param_vars as template params *)
            let ret_cpp = Translation.convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty param_vars ret_ml in
            (* Check if the return type is erased (Tany or unnamed Tvar) *)
            if Translation.type_is_erased ret_cpp then
              register_method_returns_any r
          ) methods;
          let decl = gen_ind_header_v2 ~is_mutual param_vars names.(i) cnames.(i) p.ip_types (List.rev methods) ind.ind_kind in
          (* DESIGN: Contextual wrapping for inductive definitions
             - If inside a struct/module: generate the inductive directly (no namespace wrapper)
             - If at module scope: wrap in a namespace struct (which becomes a struct via Dnspace)

             This allows inductives to nest naturally inside modules while maintaining
             proper scoping at the module level. *)
          let wrapped_decl = match decl with
            | Denum _ -> decl  (* Enums don't need namespace wrapper *)
            | _ ->
              if !in_struct_context then decl
              else Dnspace (Some names.(i), [decl])
          in
          pp_cpp_decl (empty_env ()) wrapped_decl ++ pp (i+1)
    in
    forward_decls ++ pp 0

let pp_hdecl = function
    | Dtype (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_eponymous_record_projection r ->
          (* Skip - this is a projection for an eponymous record merged into module struct *)
          mt ()
    | Dterm (r,_,_) when is_suppressed_projection r -> mt ()
    | Dind (kn,i) -> pp_cpp_ind_header kn i
    | Dtype (_, _, Miniml.Tdummy Miniml.Ktype) -> mt ()  (* Skip erased Type aliases *)
    | Dtype (r, l, t) -> (* TODO: Do for real sometime! *)
        let name = pp_global Type r in
        let l = rename_tvars keywords l in
        let ids, def =
          try
            let ids,s = find_type_custom r in
            pp_string_parameters ids, str " =" ++ spc () ++ str s
          with Not_found ->
            pp_parameters l,
            if t == Taxiom then str " (* AXIOM TO BE REALIZED *)"
            else str " =" ++ spc () ++ pp_type false l t
        in
        pp_tydef l name def
    | Dterm (r, a, Tglob (ty, args,e)) when is_monad ty ->
          let defs = (gen_dfuns_header (Array.of_list [r], Array.of_list [a], Array.of_list [Miniml.Tglob (ty, args,e)])) in
          pp_list_stmt (fun(ds, env) -> pp_cpp_decl env ds) defs
    | Dterm (r, _, _) when List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r') !method_candidates ->
          (* Skip - this function will be generated as a method on the eponymous type *)
          mt ()
    | Dterm (r, _, _) when is_registered_method r <> None ->
          (* Skip - this function is registered as a method in another module *)
          mt ()
    | Dterm (r, a, t) when is_typeclass_instance a t ->
          (* Type class instances: generate struct with static methods and static_assert *)
          let (ds_opt, class_ref_opt, type_args) = Translation.gen_instance_struct r a t in
          let struct_pp = match ds_opt with
            | Some ds -> pp_cpp_decl (empty_env ()) ds
            | None -> mt ()
          in
          (* Generate static_assert to verify the instance satisfies the concept.
             Skip for template instances (Dtemplate or Dstruct with tparams) —
             we can't instantiate a concept check without concrete types. *)
          let is_template = match ds_opt with
            | Some (Dtemplate _) -> true
            | Some (Dstruct { ds_tparams = _ :: _; _ }) -> true
            | _ -> false
          in
          let static_assert_pp = match class_ref_opt with
            | Some class_ref when not is_template ->
                let instance_name = pp_global Type r in
                let class_name = pp_global Type class_ref in
                let type_args_pp = match type_args with
                  | [] -> mt ()
                  | args ->
                      str ", " ++ prlist_with_sep (fun () -> str ", ")
                        (fun ty -> pp_cpp_type false [] (convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty)) args
                in
                fnl () ++ str "static_assert(" ++ class_name ++ str "<" ++ instance_name ++ type_args_pp ++ str ">);"
            | _ -> mt ()
          in
          struct_pp ++ static_assert_pp
    | Dterm (r, a, t) -> (* ADD CUSTOM for non-inlined *)
      let (ds, env, tvars) = gen_decl_for_pp r a t in
            begin match ds, tvars with
            | Some ds , [] ->
                (* For template structs, use full definitions instead of specs *)
                if !in_template_struct then
                  let (ds, env, _) = gen_decl r a t in pp_cpp_decl env ds
                else
                  let (ds, env) = gen_spec r a t in pp_cpp_decl env ds
            | Some ds , _::_ -> pp_cpp_decl env ds
            | None , _ ->
                if !in_template_struct then
                  let (ds, env, _) = gen_decl r a t in pp_cpp_decl env ds
                else
                  let (ds, env) = gen_spec r a t in pp_cpp_decl env ds
            end
    | Dfix (rv,defs,typs) ->
          let (rv, defs, typs) = filter_dfix rv defs typs in
          if Array.length rv = 0 then mt ()
          else
          (* For template structs, generate full definitions inline, not just declarations *)
          if !in_template_struct then
            pp_list_stmt (fun(ds, env, _) ->  pp_cpp_decl env ds) (gen_dfuns (rv, defs, typs))
          else
            pp_list_stmt (fun(ds, env) ->  pp_cpp_decl env ds) (gen_dfuns_header (rv, defs, typs))

(* Like pp_hdecl but always generates forward declarations (specs), even for
   template functions. Used for wrapper struct injection into Dnspace structs
   where the full definitions are emitted later to avoid forward reference issues. *)
let pp_hdecl_spec_only = function
    | Dtype (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_eponymous_record_projection r -> mt ()
    | Dterm (r,_,_) when is_suppressed_projection r -> mt ()
    | Dind (kn,i) -> pp_cpp_ind_header kn i
    | Dtype (_, _, Miniml.Tdummy Miniml.Ktype) -> mt ()  (* Skip erased Type aliases *)
    | Dtype (r, l, t) ->
        let name = pp_global Type r in
        let l = rename_tvars keywords l in
        let ids, def =
          try
            let ids,s = find_type_custom r in
            pp_string_parameters ids, str " =" ++ spc () ++ str s
          with Not_found ->
            pp_parameters l,
            if t == Taxiom then str " (* AXIOM TO BE REALIZED *)"
            else str " =" ++ spc () ++ pp_type false l t
        in
        pp_tydef l name def
    | Dterm (r, _, _) when List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r') !method_candidates -> mt ()
    | Dterm (r, _, _) when is_registered_method r <> None -> mt ()
    | Dterm (r, a, Tglob (ty, args,e)) when is_monad ty -> mt () (* skip monadic for spec *)
    | Dterm (r, a, t) when is_typeclass_instance a t -> mt () (* skip typeclasses for spec *)
    | Dterm (r, a, t) ->
        (* Use gen_decl_for_pp to get the same signature as the full definition,
           then convert to a spec. This ensures forward declarations match
           out-of-line definitions, including concept-constrained template params. *)
        let (ds, env, tvars) = gen_decl_for_pp r a t in
        begin match ds, tvars with
        | Some ds, _::_ ->
            pp_cpp_decl env (Translation.decl_to_spec ds)
        | _ ->
            let (ds, env) = gen_spec r a t in pp_cpp_decl env ds
        end
    | Dfix (rv,defs,typs) ->
          let (rv, defs, typs) = filter_dfix rv defs typs in
          if Array.length rv = 0 then mt ()
          else
            (* Generate specs derived from the full definition signatures (gen_dfuns_spec)
               to ensure forward declarations match the out-of-line definitions,
               including concept-constrained template parameters. *)
            pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) (gen_dfuns_spec (rv, defs, typs))


let pp_spec = function
  | Sval (r,_,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) -> pp_cpp_ind_header kn i
  | Sval (r,b,t) ->
        let (ds, env) = gen_spec r b t in
        (*let _ = print_endline (Pp.string_of_ppcmds (pp_type false [] t)) in*)
        pp_cpp_decl env ds
  | Stype (_,_,Some (Miniml.Tdummy Miniml.Ktype)) -> mt ()  (* Skip erased Type aliases *)
  | Stype (r,vl,ot) -> (* TODO: maybe do for real? but is is necessary? *)
      let name = pp_global_name Type r in
      let l = rename_tvars keywords vl in
      let ids, def =
        try
          let ids, s = find_type_custom r in
          pp_string_parameters ids, str " =" ++ spc () ++ str s
        with Not_found ->
          let ids = pp_parameters l in
          match ot with
            | None -> ids, mt ()
            | Some Taxiom -> ids, str " (* AXIOM TO BE REALIZED *)"
            | Some t -> ids, str " =" ++ spc () ++ pp_type false l t
      in
        pp_tydef l name def

(* Parse a custom type template string (e.g., "std::optional<%t0>", "std::vector<%t0>",
   "std::pair<%t0,%t1>") and recursively qualify type arguments using the provided
   qualify_type function.

   This allows any parametric custom type to have its inner type arguments properly
   qualified with "typename M::" when used in module signature requires clauses. *)
let qualify_custom_template custom_str args qualify_type =
  let len = String.length custom_str in
  let rec parse i result =
    if i >= len then result
    else if i <= len - 3 && custom_str.[i] = '%' && custom_str.[i+1] = 't' then
      (* Found %tN - extract the number *)
      let digit_start = i + 2 in
      let rec find_digit_end j =
        if j < len && (custom_str.[j] >= '0' && custom_str.[j] <= '9')
        then find_digit_end (j + 1)
        else j
      in
      let digit_end = find_digit_end digit_start in
      if digit_end > digit_start then
        (* Found a number - parse it *)
        let num_str = String.sub custom_str digit_start (digit_end - digit_start) in
        let idx = int_of_string num_str in
        if idx < List.length args then
          (* Substitute with recursively qualified type *)
          parse digit_end (result ++ qualify_type (List.nth args idx))
        else
          (* Index out of bounds - keep as literal (shouldn't happen) *)
          parse digit_end (result ++ str (String.sub custom_str i (digit_end - i)))
      else
        (* No number after %t - keep as literal *)
        parse (i + 1) (result ++ str (String.make 1 custom_str.[i]))
    else
      (* Regular character - find next % or end of string *)
      let rec find_next j =
        if j >= len then len
        else if custom_str.[j] = '%' then j
        else find_next (j + 1)
      in
      let next = find_next (i + 1) in
      parse next (result ++ str (String.sub custom_str i (next - i)))
  in
  parse 0 (mt ())

let rec pp_specif = function
  | (_,Spec (Sval _ as s)) -> pp_spec s
  | (l,Spec s) ->
     (match Common.get_duplicate (top_visible_mp ()) l with
      | None -> pp_spec s
      | Some ren -> pp_spec s (*
         hov 1 (str ("module "^ren^" : sig") ++ fnl () ++ pp_spec s) ++
         fnl () ++ str "end" ++ fnl () ++
         str ("include module type of struct include "^ren^" end") *))
  | (l,Smodule mt) ->
      let def = pp_module_type [] mt in
      def ++
      (match Common.get_duplicate (top_visible_mp ()) l with
       | None -> Pp.mt ()
       | Some ren ->
         fnl ())
  | (l,Smodtype mt) ->
      let def = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " =" ++ fnl () ++ def) ++
      (match Common.get_duplicate (top_visible_mp ()) l with
       | None -> Pp.mt ()
       | Some ren -> fnl () ++ str ("module type "^ren^" = ") ++ name)

(* DESIGN: Convert Rocq specifications to C++ concept requirements

   Rocq module types specify what operations/types are available on a module.
   In C++, this becomes a concept with 'requires' clauses checking:
   - Function signatures exist
   - Type aliases are defined

   Examples:
   - Sval (foo : int → int) becomes: requires { foo(std::declval<int>()) } -> std::same_as<int>;
   - Stype (Key) becomes: requires { typename M::Key; };

   This enables compile-time checking that modules satisfy their type signatures. *)
and ml_type_has_tvar = function
  | Miniml.Tvar _ | Miniml.Tvar' _ -> true
  | Miniml.Tunknown -> true
  | Miniml.Tarr (t1, t2) -> ml_type_has_tvar t1 || ml_type_has_tvar t2
  | Miniml.Tglob (_, args, _) -> List.exists ml_type_has_tvar args
  | Miniml.Tmeta { contents = Some t } -> ml_type_has_tvar t
  | Miniml.Tmeta { contents = None } -> true
  | _ -> false

and pp_spec_as_requirement modtype_refs = function
  | Sval (r,_,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) ->
      (* Generate typename requirement for the inductive type *)
      let name = pp_global_name Type (GlobRef.IndRef (kn, 0)) in
      str "typename M::" ++ name ++ str ";" ++ fnl ()
  | Sval (r,_,t) when ml_type_has_tvar t ->
      (* Skip polymorphic specs (auto-generated eliminators like t_rect/t_rec)
         since their type variables can't be expressed in a simple requires clause *)
      mt ()
  | Sval (r,b,t) ->
      (* Generate requires clause for a function/value *)
      let name = pp_global_name Term r in
      (* Check if it's a function by looking at the type *)
      let rec get_function_parts = function
        | Tarr (arg, rest) ->
            let (args, ret) = get_function_parts rest in
            (arg :: args, ret)
        | ret_ty -> ([], ret_ty)
      in
      let (args, ret_ty) = get_function_parts t in
      let cpp_ret = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ret_ty in
      (* Determine stdlib namespace prefix based on configuration *)
      let stdlib_ns = (sn ()).ns ^ "::" in
      let same_as = (sn ()).same_as in
      let declval = (sn ()).declval in
      let convertible_to = (sn ()).convertible_to in
      (* Helper to qualify type names with M:: *)
      let rec qualify_type = function
        | Tglob (r, [], _) when not (is_custom r) ->
            str "typename M::" ++ pp_global Type r
        | Tglob (r, args, _) when not (is_custom r) ->
            pp_global Type r ++ str "<" ++ prlist_with_sep (fun () -> str ", ") qualify_type args ++ str ">"
        | Tglob (r, args, _) ->
            (match find_custom_opt r with
            | Some custom_str ->
                if String.contains custom_str '%' then
                  (* Parametric custom type - recursively qualify type arguments *)
                  qualify_custom_template custom_str args qualify_type
                else
                  str custom_str
            | None ->
                (* This shouldn't happen due to earlier guards, but handle gracefully *)
                pp_cpp_type false [] (Tglob (r, args, [])))
        | Tshared_ptr ty ->
            str stdlib_ns ++ str "shared_ptr<" ++ qualify_type ty ++ str ">"
        | Tunique_ptr ty ->
            str stdlib_ns ++ str "unique_ptr<" ++ qualify_type ty ++ str ">"
        | Tvariant tys ->
            str stdlib_ns ++ str "variant<" ++ prlist_with_sep (fun () -> str ", ") qualify_type tys ++ str ">"
        | Tnamespace (r, ty) ->
            (* Tnamespace wraps types from other modules.
               If the type is defined in THIS module type, recurse to get M:: qualification.
               Otherwise (external type like 'comparison'), render as-is. *)
            if List.exists (Environ.QGlobRef.equal Environ.empty_env r) modtype_refs
            then qualify_type ty
            else pp_cpp_type false [] ty
        | ty -> pp_cpp_type false [] ty
      in
      if args = [] then
        (* Non-function values need a disjunctive concept check because the
           C++ representation differs depending on whether the implementing
           module is a template struct or not:

           - Non-template structs use plain static data members:
               static inline const T empty = ...;
             Here M::empty is a value expression, and M::empty() won't compile.

           - Template structs use Meyers singleton accessors:
               static const T& empty() { static const T v = ...; return v; }
             This is needed because C++17 template static inline data members
             have "unordered" dynamic initialization, which can cause segfaults
             when one static member references another during init.
             Here M::empty() returns the value, but M::empty without parens
             refers to the function itself (a function pointer, not convertible
             to T).

           The concept is generated from the module type signature, which just
           says "val empty : t" — it doesn't know which form the implementation
           will use, since that depends on whether the implementing module
           becomes a template struct (functor with parameters) or a plain struct.
           Both can satisfy the same module type, so the concept must accept
           both forms via a disjunction. *)
        let qualified_ret = qualify_type cpp_ret in
        str "requires (" ++ fnl () ++
        str "  requires { { M::" ++ name ++ str " } -> " ++ str convertible_to ++ str "<" ++ qualified_ret ++ str ">; } ||" ++ fnl () ++
        str "  requires { { M::" ++ name ++ str "() } -> " ++ str convertible_to ++ str "<" ++ qualified_ret ++ str ">; }" ++ fnl () ++
        str ");" ++ fnl ()
      else
        (* For functions, generate requires expression with parameters and return type *)
        let cpp_args = List.map (convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty []) args in
        (* Generate: { M::name(std::declval<arg1>(), ...) } -> std::same_as<ret_ty>; *)
        let declvals = List.map (fun arg_ty ->
          str declval ++ str "<" ++ qualify_type arg_ty ++ str ">()"
        ) cpp_args in
        let call_expr = str "M::" ++ name ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity declvals ++ str ")" in
        str "{ " ++ call_expr ++ str " } -> " ++ str same_as ++ str "<" ++ qualify_type cpp_ret ++ str ">;" ++ fnl ()
  | Stype (r,vl,ot) ->
      (* Generate requires clause for a type *)
      let name = pp_global_name Type r in
      str "typename M::" ++ name ++ str ";" ++ fnl ()

and pp_module_type params = function
  | MTident kn ->
      (* Reference to a concept name *)
      pp_modname kn
  | MTfunsig (mbid, mt, mt') ->
      (* DESIGN: Functor type signatures
         For a functor taking parameter Param of type MT returning MT',
         we just generate MT' since the template parameters are handled
         separately in pp_structure_elem.

         Example: module MakeMap(Key: OrderedType)(Value: BaseType) : SigName
         becomes: template<OrderedType Key, BaseType Value> struct MakeMap { ... };
         (parameter concepts are in template params, body type is pp_module_type) *)
      pp_module_type (MPbound mbid :: params) mt'
  | MTsig (mp, sign) ->
      (* DESIGN: Module type signatures become concept definitions
         Each Sval/Stype specification becomes a requires clause that checks
         the module parameter satisfies the expected interface.

         The signature { type Key; val find : Key -> Value } becomes:
         template<typename M> concept SigName = requires {
           typename M::Key;
           M::find(std::declval<M::Key>()) -> std::same_as<...>;
         }; *)
      push_visible mp params;
      (* Collect GlobRefs of types/inductives defined in this module type.
         These are the types that should be qualified with M:: in the concept body.
         Types from other modules (e.g., comparison from Datatypes) should NOT
         be qualified with M::. *)
      let modtype_refs = List.fold_left (fun acc (_label, specif) ->
        match specif with
        | Spec (Stype (r, _, _)) -> r :: acc
        | Spec (Sind (kn, _)) -> GlobRef.IndRef (kn, 0) :: acc
        | _ -> acc
      ) [] sign in
      let pp_req (_label, specif) = match specif with
        | Spec s -> pp_spec_as_requirement modtype_refs s
        | Smodule _ -> mt () (* TODO: nested modules *)
        | Smodtype _ -> mt () (* TODO: nested module types *)
      in
      let reqs = List.map pp_req sign in
      let reqs = List.filter (fun p -> not (Pp.ismt p)) reqs in
      pop_visible ();
      if List.is_empty reqs then mt ()
      else prlist identity reqs
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      (* TODO: handle with type constraints properly *)
      pp_module_type [] mt
  | MTwith(mt,ML_With_module(idl,mp)) ->
      (* TODO: handle with module constraints properly *)
      pp_module_type [] mt

let rec pp_structure_elem ~is_header f = function
  | (l,SEdecl d) ->
     (match Common.get_duplicate (top_visible_mp ()) l with
      | None -> f d
      | Some ren ->
         v 1 (str ("namespace " ^ ren ^ " {") ++ fnl () ++ f d) ++
         fnl () ++ str "};")
  | (l,SEmodule m) ->
      (* DESIGN: Module generation - three cases
         1. Regular modules → struct ModuleName { members };
         2. Functors → template<Concept P1, Concept P2> struct Functor { members };
         3. Module applications → using Result = Functor<Arg1, Arg2>;

         This enables:
         - Type parameters via template arguments
         - Compile-time checking via concepts
         - Proper scoping and visibility of module members *)
      let mp = MPdot (top_visible_mp (), l) in
      let name = pp_modname mp in
      (* NOTE: Previously we had an emptiness check here that called pp_module_expr
         BEFORE setting up context. This caused side effects (method registration)
         to happen with wrong context. We now handle emptiness within each case. *)
      (match m.ml_mod_expr with
         | MEfunctor _ ->
             (* DESIGN: Functor template generation
                For a functor taking multiple parameters:
                  module MakeMap(K: OrderedType)(V: BaseType) = ...
                Generate:
                  template<OrderedType K, BaseType V>
                  struct MakeMap { ... };

                Only generate in header - C++ templates require definitions in headers.
                Template instantiation happens automatically at compile time. *)
             if not is_header then mt () else
             let get_template_and_body = function
               | MEfunctor (mbid, mt, me) ->
                   let rec collect_params mbid mt me = match me with
                     | MEfunctor (mbid', mt', me') ->
                         let (params_rest, body) = collect_params mbid' mt' me' in
                         ((mbid, mt) :: params_rest, body)
                     | _ -> ([(mbid, mt)], me)
                   in
                   collect_params mbid mt me
               | _ -> ([], m.ml_mod_expr)
             in
             let (template_params, body) = get_template_and_body m.ml_mod_expr in
             let pp_template_param (mbid, mt) =
               let concept_name = pp_module_type [] mt in
               let param_name = pp_modname (MPbound mbid) in
               concept_name ++ str " " ++ param_name
             in
             let template_decl =
               str "template<" ++
               prlist_with_sep (fun () -> str ", ") pp_template_param template_params ++
               str ">"
             in
             (* Set context: we're inside a template struct *)
             let struct_body = with_render_ctx
               ~setup:(fun () -> in_struct_context := true; in_template_struct := true)
               (fun () -> pp_module_expr ~is_header f (List.map (fun (mbid, _) -> MPbound mbid) template_params) body) in
             template_decl ++ fnl () ++
             str "struct " ++ name ++ str " {" ++ fnl () ++
             struct_body ++
             str "};"
         | MEapply _ ->
             (* Module application: generate using declaration *)
             (* Only in header - it's a type alias *)
             if not is_header then mt () else
             (* Record the functor source for this applied module.
                This allows template_static_accessors to match across
                functor boundaries (e.g., NatWrapper → Wrapper). *)
             let rec get_base_functor_mp = function
               | MEapply (f, _) -> get_base_functor_mp f
               | MEident fmp -> Some fmp
               | _ -> None
             in
             (match get_base_functor_mp m.ml_mod_expr with
              | Some fmp -> Hashtbl.replace functor_app_sources mp fmp
              | None -> ());
             let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
             let using_decl = str "using " ++ name ++ str " = " ++ body ++ str ";" in
             (* Add static_assert for functor applications with known return types *)
             let rec get_concept_name = function
               | MTident kn -> Some (pp_modname kn)
               | MTwith(mt, _) -> get_concept_name mt
               | MTfunsig (_, mt, mt') -> get_concept_name mt'
               | MTsig _ -> None
             in
             let static_assert = match get_concept_name m.ml_mod_type with
             | Some concept_name ->
                 fnl () ++ str "static_assert(" ++ concept_name ++ str "<" ++ name ++ str ">);"
             | None -> mt ()
             in
             using_decl ++ static_assert
         | MEstruct (_mp, sel) ->
             (* Regular module: generate struct in header, member definitions in implementation *)
             let old_context = !in_struct_context in
             let old_struct_name = !current_struct_name in
             let old_struct_mp = !current_struct_mp in
             let old_eponymous = !eponymous_type_ref in
             let old_methods = !method_candidates in
             (* Save parent's eponymous_record BEFORE detecting for this module *)
             let old_eponymous_record = !eponymous_record in

             (* Clear eponymous state for this module - will be set if this module has one *)
             eponymous_type_ref := None;
             eponymous_record := None;

             (* Find eponymous inductive: an inductive with lowercase of module name *)
             let module_name_str = Pp.string_of_ppcmds name in
             let lowercase_module = String.lowercase_ascii module_name_str in
             List.iter (fun (_l, se) ->
               match se with
               | SEdecl (Dind (kn, ind)) ->
                 Array.iteri (fun i p ->
                   let ind_ref = GlobRef.IndRef (kn, i) in
                   let ind_name = Common.pp_global_name Type ind_ref in
                   if String.lowercase_ascii ind_name = lowercase_module then begin
                     match ind.ind_kind with
                     | TypeClass _ ->
                         (* Type classes become concepts, no eponymous handling *)
                         ()
                     | Record fields ->
                         (* Eponymous RECORD: merge into module struct to avoid name conflict *)
                         eponymous_record := Some (ind_ref, fields, p);
                         register_eponymous_record ind_ref
                     | _ ->
                         (* Eponymous INDUCTIVE: existing method generation behavior *)
                         eponymous_type_ref := Some ind_ref
                   end
                 ) ind.ind_packets
               | _ -> ()
             ) sel;

             method_candidates := [];

             (* Collect method candidates: functions that take eponymous type as any argument.
                Find the first argument that matches and record its position.
                Exclude functions with additional type variables beyond those in the eponymous type.
                IMPORTANT: Only include functions from the SAME Rocq module as the eponymous type.
                This ensures that stdlib's app (from Corelib.Init.Datatypes) becomes a method on list
                (also from Corelib.Init.Datatypes), but rev (from Stdlib.Lists.List) does not.

                We scan BOTH the current module's sel AND the parent structure's decls
                (current_structure_decls) to find methods. This handles the case where
                list and app are from the same Rocq module but extracted as siblings. *)
             (* Collect method candidates for BOTH eponymous inductives AND eponymous records.
                For inductives, methods are generated on the nested inductive struct.
                For records, methods are generated directly on the module struct (which has record fields merged). *)
             let epon_ref_opt = match !eponymous_type_ref, !eponymous_record with
               | Some r, _ -> Some r
               | _, Some (r, _, _) -> Some r
               | None, None -> None
             in
             (match epon_ref_opt with
             | Some epon_ref ->
               (* Get the module path of the eponymous type/record *)
               let epon_modpath = modpath_of_r epon_ref in
               (* Check if function comes from the same Rocq module as eponymous type/record *)
               let same_module r = ModPath.equal (modpath_of_r r) epon_modpath in
               (* Helper to process a single declaration *)
               let process_decl (_l, se) =
                 match se with
                 | SEdecl (Dterm (r, body, ty)) ->
                   (* Only consider functions from the same Rocq module as the eponymous type/record *)
                   if same_module r then
                     (match Method_registry.find_epon_arg_pos epon_ref ty with
                     | Some (pos, ind_tvar_positions) ->
                       method_candidates := (r, body, ty, pos) :: !method_candidates;
                       register_method r epon_ref pos ~ind_tvar_positions ();
                       Method_registry.add_candidate (get_method_registry ()) epon_ref (r, body, ty, pos)
                     | None -> ())
                 | SEdecl (Dfix (rv, defs, typs)) ->
                   (* Handle fixpoints similarly - only from same module *)
                   Array.iteri (fun i r ->
                     if same_module r then begin
                       let ty = typs.(i) in
                       let body = defs.(i) in
                       match Method_registry.find_epon_arg_pos epon_ref ty with
                       | Some (pos, ind_tvar_positions) ->
                         method_candidates := (r, body, ty, pos) :: !method_candidates;
                         register_method r epon_ref pos ~ind_tvar_positions ();
                         Method_registry.add_candidate (get_method_registry ()) epon_ref (r, body, ty, pos)
                       | None -> ()
                     end
                   ) rv
                 | _ -> ()
               in
               (* Scan current module's declarations *)
               List.iter process_decl sel;
               (* Also scan parent structure's declarations for sibling functions
                  from the same Rocq module (e.g., app next to List module) *)
               List.iter process_decl !current_structure_decls
             | None -> ());

             (* Save THIS module's detected eponymous_record for struct generation *)
             let this_eponymous_record = !eponymous_record in

             (* DESIGN: Type class concept hoisting
                Type classes inside modules must be hoisted to namespace scope because C++ concepts
                can only be declared at namespace or global scope, not inside structs.

                Before generating the module struct:
                1. Collect all type class inductives from the module
                2. Generate their concepts at the current scope (before the struct)
                3. Skip them when generating the struct body *)
             (* DESIGN: Concept-module name collision detection.
                Check if any type class concept inside this module has the same name
                as the module struct. When this happens, concepts are still hoisted
                (they must be at namespace/global scope), but the module body is emitted
                without a struct wrapper to avoid a name collision between the hoisted
                concept and the struct. *)
             let concept_simple_name_of ind_ref =
               let sn = Common.pp_global_name Type ind_ref in
               match String.rindex_opt sn ':' with
               | Some idx when idx > 0 && idx < String.length sn - 1
                             && sn.[idx-1] = ':' ->
                   String.sub sn (idx + 1) (String.length sn - idx - 1)
               | _ -> sn
             in
             let module_name_str_raw = Common.pp_module mp in
             let has_concept_collision = List.exists (fun (_l, se) ->
               match se with
               | SEdecl (Dind (kn, ind)) ->
                   List.exists (fun i ->
                     match ind.ind_kind with
                     | TypeClass _ ->
                         let ind_ref = GlobRef.IndRef (kn, i) in
                         String.equal (concept_simple_name_of ind_ref) module_name_str_raw
                     | _ -> false
                   ) (List.init (Array.length ind.ind_packets) Fun.id)
               | _ -> false
             ) sel in

             (* DESIGN: Type class concept hoisting
                Type classes inside modules must be hoisted to namespace scope because C++ concepts
                can only be declared at namespace or global scope, not inside structs.

                Before generating the module struct:
                1. Collect all type class inductives from the module
                2. Generate their concepts at the current scope (before the struct)
                3. Skip them when generating the struct body *)
             let typeclass_concepts = if is_header then
               List.concat_map (fun (_l, se) ->
                 match se with
                 | SEdecl (Dind (kn, ind)) ->
                     List.concat (List.init (Array.length ind.ind_packets) (fun i ->
                       match ind.ind_kind with
                       | TypeClass fields ->
                           let ind_ref = GlobRef.IndRef (kn, i) in
                           let packet = ind.ind_packets.(i) in
                           [pp_cpp_decl (empty_env ()) (Translation.gen_typeclass_cpp ind_ref fields packet)]
                       | _ -> []
                     ))
                 | _ -> []
               ) sel
             else [] in
             let typeclasses_pp = prlist_with_sep fnl (fun x -> x) typeclass_concepts in
             let typeclasses_pp = if typeclass_concepts = [] then mt () else typeclasses_pp ++ fnl () ++ fnl () in

             (* DESIGN: Module type concept hoisting
                Module types (SEmodtype) inside modules become C++ concepts, which can
                only be declared at namespace or global scope, not inside structs.
                Hoist them before the struct, similar to type class concepts. *)
             let modtype_concepts = if is_header then
               List.filter_map (fun (l, se) ->
                 match se with
                 | SEmodtype m ->
                     let def = pp_module_type [] m in
                     let modtype_name = str (Label.to_string l) in
                     let concept_pp =
                       str "template<typename M>" ++ fnl () ++
                       hov 1 (str "concept " ++ modtype_name ++ str " = requires {" ++ fnl () ++ def ++ str "};")
                     in
                     Some concept_pp
                 | _ -> None
               ) sel
             else [] in
             let modtypes_pp = prlist_with_sep fnl (fun x -> x) modtype_concepts in
             let modtypes_pp = if modtype_concepts = [] then mt () else modtypes_pp ++ fnl () ++ fnl () in

             (* When there's a concept collision, don't set struct context or
                struct name — the module body is emitted without a wrapper. *)
             let old_concepts_hoisted = !concepts_hoisted in
             if is_header && not has_concept_collision then
               in_struct_context := true
             else if not is_header && not has_concept_collision then begin
               (* Track struct name for qualification - combine with parent for nested modules *)
               current_struct_name := (match old_struct_name with
                 | Some parent -> Some (parent ++ str "::" ++ name)
                 | None -> Some name);
               current_struct_mp := Some mp
             end;
             (* Mark concepts as hoisted so TypeClass items in the body are skipped *)
             if is_header && typeclass_concepts <> [] then
               concepts_hoisted := true;
             begin
             let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
             (* Save method_candidates before restoring old state - need them for generating record methods *)
             let this_method_candidates = !method_candidates in
             in_struct_context := old_context;
             concepts_hoisted := old_concepts_hoisted;
             current_struct_name := old_struct_name;
             current_struct_mp := old_struct_mp;
             eponymous_type_ref := old_eponymous;
             eponymous_record := old_eponymous_record;  (* Restore PARENT's value *)
             method_candidates := old_methods;
             if is_header then
               (* Header: full struct definition *)
               (* For eponymous records: add template params, record fields, and methods *)
               let (template_decl, record_fields_pp, record_methods_pp) = match this_eponymous_record with
                 | Some (epon_ref, fields, packet) ->
                     (* Generate template parameters from record's type vars *)
                     let ty_vars = packet.ip_vars in
                     let template_str = if ty_vars = [] then mt () else
                       str "template<" ++
                       prlist_with_sep (fun () -> str ", ")
                         (fun v -> str "typename " ++ Id.print v) ty_vars ++
                       str ">" ++ fnl ()
                     in
                     (* Generate record fields *)
                     let field_list = List.combine fields packet.ip_types.(0) in
                     let pp_field (field_ref, field_ty) =
                       let field_name = match field_ref with
                         | Some r -> str (Common.pp_global_name Term r)
                         | None -> str "_field"
                       in
                       let cpp_ty = pp_cpp_type false ty_vars (convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty ty_vars field_ty) in
                       cpp_ty ++ spc () ++ field_name ++ str ";"
                     in
                     let fields_pp = prlist_with_sep fnl pp_field field_list ++ fnl () in
                     (* Generate methods from method candidates, filtering out record projections
                       since they have the same names as fields and are redundant *)
                     let non_projection_candidates = List.filter (fun (r, _, _, _) ->
                       not (Table.is_projection r)
                     ) (List.rev this_method_candidates) in
                     let method_fields = Translation.gen_record_methods epon_ref ty_vars non_projection_candidates in
                     (* Temporarily restore method_candidates so that method bodies can
                        recognize calls to other methods on the same struct *)
                     let methods_pp = if method_fields = [] then mt () else begin
                       let saved_methods = !method_candidates in
                       method_candidates := this_method_candidates;
                       let result = prlist_with_sep fnl (fun (fld, _vis) -> pp_cpp_field (empty_env ()) fld) method_fields ++ fnl () in
                       method_candidates := saved_methods;
                       result
                     end
                     in
                     (template_str, fields_pp, methods_pp)
                 | None -> (mt (), mt (), mt ())
               in
               if has_concept_collision then
                 (* Concept collision: the hoisted concept takes the module name,
                    so emit module body without a struct wrapper. *)
                 typeclasses_pp ++ modtypes_pp ++
                 record_fields_pp ++
                 record_methods_pp ++
                 body
               else begin
                 let struct_def = template_decl ++
                   str "struct " ++ name ++ str " {" ++ fnl () ++
                   record_fields_pp ++
                   record_methods_pp ++
                   body ++
                   str "};" in
                 (* For modules with type annotations, add static_assert *)
                 let rec get_concept_name = function
                   | MTident kn -> Some (pp_modname kn)
                   | MTwith(mt, _) -> get_concept_name mt  (* Extract base from 'with' clauses *)
                   | MTfunsig (_, mt, mt') -> get_concept_name mt'  (* Extract return type from functor sig *)
                   | MTsig _ -> None  (* Anonymous signature, no concept *)
                 in
                 let static_assert = match get_concept_name m.ml_mod_type with
                 | Some concept_name ->
                     fnl () ++ str "static_assert(" ++ concept_name ++ str "<" ++ name ++ str ">);"
                 | None -> mt ()
                 in
                 typeclasses_pp ++ modtypes_pp ++ struct_def ++ static_assert
               end
             else
               (* Implementation: just the member definitions (body is already processed) *)
               body
             end (* has_sibling_inductive_collision else branch *)
         | MEident _ ->
             (* Module alias: generate as is *)
             let body = with_render_ctx
               ~setup:(fun () ->
                 if is_header then
                   in_struct_context := true
                 else begin
                   current_struct_name := (match !current_struct_name with
                     | Some parent -> Some (parent ++ str "::" ++ name)
                     | None -> Some name);
                   current_struct_mp := Some mp
                 end)
               (fun () -> pp_module_expr ~is_header f [] m.ml_mod_expr) in
             if is_header then
               str "struct " ++ name ++ str " {" ++ fnl () ++ body ++ str "};"
             else
               body
        )
  | (l,SEmodtype m) ->
      (* Module types become concepts - only in header.
         When inside a struct context, concepts have been hoisted to namespace scope
         (see module type concept hoisting), so skip them here. *)
      if not is_header || !in_struct_context then mt () else
      let def = pp_module_type [] m in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      (* Generate a C++ concept with template parameter *)
      str "template<typename M>" ++ fnl () ++
      hov 1 (str "concept " ++ name ++ str " = requires {" ++ fnl () ++ def ++ str "};") ++
      (match Common.get_duplicate (top_visible_mp ()) l with
       | None -> mt ()
       | Some ren -> fnl () ++ str ("template<typename M> concept "^ren^" = ") ++ name ++ str "<M>;")

and pp_module_expr ~is_header f params = function
  | MEident mp ->
      (* Reference to a module name *)
      pp_modname mp
  | MEapply (me, me') ->
      (* Functor application: collect all arguments and generate single template instantiation *)
      let rec collect_args acc = function
        | MEapply (f, arg) -> collect_args (arg :: acc) f
        | base -> (base, acc)
      in
      let (base, args) = collect_args [me'] me in
      let base_pp = pp_module_expr ~is_header f [] base in
      let args_pp = prlist_with_sep (fun () -> str ", ") (pp_module_expr ~is_header f []) args in
      base_pp ++ str "<" ++ args_pp ++ str ">"
  | MEfunctor (mbid, mt, me) ->
      (* Functor body: just generate the body, template params are handled in pp_structure_elem *)
      pp_module_expr ~is_header f (MPbound mbid :: params) me
  | MEstruct (mp, sel) ->
      (* Module structure: generate struct members *)
      push_visible mp params;
      (* Track current structure's declarations for sibling access *)
      let old_structure_decls = !current_structure_decls in
      current_structure_decls := sel;
      (* Register all inductives defined in this module before processing declarations.
         This ensures that references to sibling inductives don't get namespace-qualified. *)
      let old_local_inductives = get_local_inductives () in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          (* Add all inductives in this mutual block *)
          Array.iteri (fun i _p -> add_local_inductive (GlobRef.IndRef (kn, i))) ind.ind_packets
        | _ -> ()
      ) sel;
      let try_pp_structure_elem l x =
        let px = pp_structure_elem ~is_header f x in
        if Pp.ismt px then l else px::l
      in
      (* We cannot use fold_right here due to side effects in pp_structure_elem *)
      let l = List.fold_left try_pp_structure_elem [] sel in
      let l = List.rev l in
      (* Restore previous local_inductives state for proper nesting *)
      clear_local_inductives ();
      List.iter add_local_inductive old_local_inductives;
      current_structure_decls := old_structure_decls;
      pop_visible ();
      if List.is_empty l then mt ()
      else
        v 1 (prlist_with_sep cut2 identity l) ++ fnl ()

let rec prlist_sep_nonempty sep f = function
  | [] -> mt ()
  | [h] -> f h
  | h::t ->
     let e = f h in
     let r = prlist_sep_nonempty sep f t in
     if Pp.ismt e then r
     else e ++ sep () ++ r

(* PERFORMANCE OPTIMIZATION: Process wrapper module function declarations in a SINGLE pass.

   This function generates both forward declarations and full definitions from a single
   code generation call per function, avoiding duplicate AST traversal and type conversion.

   APPROACH:
   1. Calls gen_decl_for_dfuns/gen_decl_for_pp ONCE per function
   2. Derives BOTH forward declaration and full definition from the same cpp_decl AST
   3. Renders each with appropriate global state (in_struct_context for forward declarations,
      current_struct_name for out-of-line definitions)

   PARAMETERS:
   - is_header: true for .h file rendering, false for .cpp
   - wrapper_name: struct name (e.g., "List", "ListDef") for qualifying out-of-line defs
   - func_sels: list of (Label.t * structure_elem) function declarations

   RETURNS: (specs_pp, defs_pp, lifted_pp)
   - specs_pp: Forward declarations to inject into Dnspace struct (rendered with in_struct_context=true)
   - defs_pp: Out-of-line definitions with WrapperName:: prefix (rendered with current_struct_name set)
   - lifted_pp: Template helper functions (e.g., _foo_aux from local fixpoints)

   RENDERING STRATEGY:
   - Template functions: forward declaration in .h, full definition in .h (templates require definitions in headers)
   - Non-template functions: forward declaration in .h, full definition in .cpp (normal C++ separation)

   The is_header parameter controls which definitions are generated via gen_dfuns_dual/gen_decl_for_pp_dual. *)
let pp_wrapper_module_dual ~is_header ~wrapper_mp wrapper_name func_sels =
  let is_method_candidate x = List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env x r') !method_candidates in

  (* PHASE 1: Code generation (the expensive part — do this ONCE per function)

     For each SEdecl entry, call the dual generation functions that produce
     both forward declaration and full definition from a single code generation pass:
     - Dterm → gen_decl_for_pp_dual
     - Dfix → gen_dfuns_dual

     These functions internally call gen_decl_for_dfuns/gen_decl_for_pp ONCE,
     then derive the forward declaration via decl_to_spec and return both.

     IMPORTANT: We collect raw (cpp_decl * env) pairs here, deferring rendering
     to Phase 3. This allows us to render forward declarations and definitions with
     different global state (in_struct_context vs current_struct_name).

     DFIX GROUPING: Multiple functions in a Dfix are kept as a group (list of declarations/definitions)
     so that in Phase 3 they can be rendered as a single block with pp_list_stmt
     (no blank lines between functions within the same Dfix). Between different
     SEdecl entries, blank line separators are used. *)
  let process_sel (_l, se) =
    match se with
    (* Skip cases: These function types are handled elsewhere or aren't rendered *)
    | SEdecl (Dterm (r,_,_)) when is_any_inline_custom r -> ([], [], [])
    | SEdecl (Dterm (r,_,_)) when is_eponymous_record_projection r -> ([], [], [])
    | SEdecl (Dterm (r,_,_)) when is_suppressed_projection r -> ([], [], [])
    | SEdecl (Dterm (r, _, _)) when is_method_candidate r -> ([], [], [])
    | SEdecl (Dterm (r, body, ty)) when is_registered_method r <> None ->
      (* Method already registered during pre-scan; ensure candidate body is available *)
      (match is_registered_method r with
       | Some (epon_ref, pos) ->
         let reg = get_method_registry () in
         let already = List.exists (fun (r', _, _, _) ->
           Environ.QGlobRef.equal Environ.empty_env r r'
         ) (Method_registry.get_candidates reg epon_ref) in
         if not already then
           Method_registry.add_candidate reg epon_ref (r, body, ty, pos)
       | None -> ());
      ([], [], [])
    | SEdecl (Dterm (r, _a, Tglob (ty, _args, _e))) when is_monad ty -> ([], [], [])
    | SEdecl (Dterm (r, a, t)) when is_typeclass_instance a t -> ([], [], [])

    (* DTERM: Single function declaration
       Call gen_decl_for_pp_dual ONCE to generate both forward declaration and full definition.
       Returns:
       - spec_opt: forward declaration (always generated)
       - def_opt: full definition (template → .h, non-template → .cpp)
       - lifted: template helper functions extracted during code gen *)
    | SEdecl (Dterm (r, a, t)) ->
      let (spec_opt, def_opt, _tvars) = gen_decl_for_pp_dual ~is_header r a t in
      let lifted = Translation.take_lifted_decls () in
      let specs = match spec_opt with Some s -> [s] | None -> [] in
      let defs = match def_opt with Some d -> [d] | None -> [] in
      (specs, defs, lifted)

    (* DFIX: Mutually recursive function group
       Call gen_dfuns_dual ONCE to generate forward declarations and definitions for all functions.
       The dual function calls gen_decl_for_dfuns once per function, then derives both
       forward declaration (via decl_to_spec) and full definition from the same cpp_decl AST.

       FILTERING: Skip inline custom, method candidates, globally registered methods,
       and eponymous projections.

       GROUPING: Keep all functions from this Dfix as a list so they can be
       rendered as a single block (no blank lines between them) in Phase 3. *)
    | SEdecl (Dfix (rv, defs, typs)) ->
      (* Ensure registered methods have their candidates in the registry *)
      Array.iteri (fun i r ->
        match is_registered_method r with
        | Some (epon_ref, pos) ->
          let reg = get_method_registry () in
          let already = List.exists (fun (r', _, _, _) ->
            Environ.QGlobRef.equal Environ.empty_env r r'
          ) (Method_registry.get_candidates reg epon_ref) in
          if not already then
            Method_registry.add_candidate reg epon_ref (r, defs.(i), typs.(i), pos)
        | None -> ()
      ) rv;
      let (rv, defs, typs) = filter_dfix rv defs typs in
      if Array.length rv = 0 then ([], [], [])
      else
        let results = gen_dfuns_dual ~is_header (rv, defs, typs) in
        let specs = List.map (fun (s, _, _) -> s) results in
        let defs_list = List.filter_map (fun (_, d, _) -> d) results in
        let lifted = List.concat_map (fun (_, _, l) -> l) results in
        (specs, defs_list, lifted)
    | _ -> ([], [], [])
  in

  (* PHASE 2: Collect results from all SEdecl entries

     Each SEdecl produces (specs, defs, lifted) where:
     - specs: list of (cpp_decl * env) for this SEdecl's forward declarations
     - defs: list of (cpp_decl * env) for this SEdecl's full definitions
     - lifted: list of cpp_decl for template helpers extracted during code gen

     For Dterm entries: specs/defs lists have 0-1 elements
     For Dfix entries: specs/defs lists may have multiple elements (one per function in the group) *)
  let all_results = List.map process_sel func_sels in
  let all_lifted = List.concat_map (fun (_, _, l) -> l) all_results in

  (* PHASE 3: Render cpp_decl ASTs with appropriate global state

     CRITICAL: We must render forward declarations and definitions separately with different global state:
     - Forward declarations: in_struct_context=true → renders as "static type func(...)" for injection into struct
     - Definitions: current_struct_name=Some "WrapperName" → renders as "WrapperName::func(...)" for out-of-line defs

     FORMATTING: We use:
     - pp_list_stmt within each SEdecl group (Dfix functions have no blank line between them)
     - prlist_sep_nonempty cut2 between different SEdecl entries (blank line separator)

     Example rendering (forward declarations for List module with 3 separate Dterm entries):
       concat(...)    ← SEdecl 1
                      ← blank line (cut2)
       fold_right(...) ← SEdecl 2
                      ← blank line (cut2)
       filter(...)    ← SEdecl 3

     Example rendering (forward declarations for Dfix with 2 functions):
       map(...)       ← function 1 in Dfix
       seq(...)       ← function 2 in Dfix (no blank line, rendered by pp_list_stmt)

     The render_sel_specs/render_sel_defs functions call pp_list_stmt per SEdecl,
     then prlist_sep_nonempty cut2 combines them with blank line separators. *)

  let render_sel_specs (specs, _, _) =
    match specs with
    | [] -> mt ()
    | _ -> pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) specs
  in
  let render_sel_defs (_, defs, _) =
    match defs with
    | [] -> mt ()
    | _ -> pp_list_stmt (fun (ds, env) -> pp_cpp_decl env ds) defs
  in

  (* Render forward declarations with in_struct_context=true
     This makes pp_cpp_decl render as "static type func(...)" for injection into Dnspace struct *)
  let specs_pp = with_render_ctx
    ~setup:(fun () -> in_struct_context := true)
    (fun () -> prlist_sep_nonempty cut2 render_sel_specs all_results) in

  (* Render definitions with current_struct_name set
     This makes pp_cpp_decl render as "WrapperName::func(...)" for out-of-line definitions.
     The Dfundef case in pp_cpp_decl checks current_struct_name and adds the
     "WrapperName::" prefix to the function name. *)
  let defs_pp = with_render_ctx
    ~setup:(fun () ->
      current_struct_name := Some (str wrapper_name);
      current_struct_mp := Some wrapper_mp)
    (fun () -> prlist_sep_nonempty cut2 render_sel_defs all_results) in

  (* Render lifted decls (template helpers like _foo_aux)
     These are template functions extracted from local fixpoints during gen_dfun.
     They only appear in .h files (templates require definitions in headers). *)
  let lifted_pp = if is_header then
    prlist_sep_nonempty cut2 (fun d -> pp_cpp_decl (empty_env ()) d) all_lifted
  else mt () in

  (specs_pp, defs_pp, lifted_pp)

let do_struct_with_decl_tracking ~is_header f s =
  (* Clear any stale lifted declarations from previous extraction passes.
     The extraction framework calls pp_struct/pp_hstruct multiple times
     (dry run, impl, intf) and lifted decls can leak between passes. *)
  ignore (Translation.take_lifted_decls ());
  (* Resolve std/bsl names once for this extraction pass *)
  init_std_names ();
  (* Build the method registry by scanning the entire structure BEFORE any
     code generation.  This replaces the old pre_register_methods_from_structure
     pre-pass and also computes returns_any information up front.
     The registry is stored in a module-level ref so that helper functions
     (is_registered_method, method_returns_any, etc.) can access it. *)
  method_registry := Some (Method_registry.create s);
  (* Run structure analysis: enum registration, inductive name collection,
     module classification, and topological sort — all in one pass. *)
  let analysis = Structure_analysis.analyze (get_method_registry ()) s in
  (* Populate cpp.ml hashtables from analysis results *)
  Hashtbl.clear global_inductive_names;
  List.iter (fun (name, mp) ->
    Hashtbl.replace global_inductive_names name mp
  ) analysis.inductive_names;
  Hashtbl.clear global_scope_enum_table;
  List.iter (fun r ->
    Hashtbl.replace global_scope_enum_table r ()
  ) analysis.global_scope_enums;
  (* Register wrapper modules in the wrapper_module_table *)
  List.iter (fun (mi : Structure_analysis.module_info) ->
    match mi.wrapper_name with
    | Some name -> Hashtbl.replace wrapper_module_table mi.modpath name
    | None -> ()
  ) analysis.sorted_modules;
  (* Convert analysis results to the format used by rendering passes *)
  let is_func_decl (_, se) = match se with
    | SEdecl (Dterm _ | Dfix _) -> true
    | _ -> false in
  let wrapper_names = List.map (fun (mi : Structure_analysis.module_info) ->
    ((mi.modpath, mi.sels), mi.wrapper_name)
  ) analysis.sorted_modules in
  (* ============================================================================
     COMBINED PASS: PERFORMANCE OPTIMIZATION TO ELIMINATE DUPLICATE CODE GENERATION
     ============================================================================

     This pass generates both forward declarations and full definitions from a SINGLE
     code generation call per wrapper module function.

     APPROACH:
     - Call pp_wrapper_module_dual which calls gen_decl_for_dfuns/gen_decl_for_pp ONCE per function
       → Generate both forward declaration AND full definition from the same cpp_decl AST (via decl_to_spec)
       → Store forward declarations in pending_wrapper_decls (for Dnspace injection in PASS 2)
       → Store definitions in deferred_defs_acc (for emission after PASS 2)
       → Expensive work (AST traversal, type conversion, escape analysis) happens only ONCE
     - PASS 2: Render type declarations (inductives)
       → Dnspace structs pick up forward declarations from pending_wrapper_decls
     - ASSEMBLY: Emit types + remaining_wrappers + main + deferred_lifted + deferred_defs

     ORDERING CONSTRAINTS:
     1. Combined pass BEFORE PASS 2: Dnspace structs (created during type rendering)
        need to consume pending_wrapper_decls
     2. Deferred definitions AFTER PASS 2: Template function bodies may reference types
        (like ListDef) defined in later structs. Full definitions are placed after
        all struct definitions where all types are visible.

     RENDERING SPLIT:
     - Template functions: forward declaration in .h, full definition in .h (templates require definitions in headers)
     - Non-template functions: forward declaration in .h, full definition in .cpp (normal C++ separation)

     The is_header parameter controls which definitions are generated by pp_wrapper_module_dual.
     For .h: template definitions only. For .cpp: non-template definitions only. *)

  let deferred_defs_acc = ref (mt ()) in
  let deferred_lifted_acc = ref (mt ()) in

  (* PASS 1: Process wrapper modules and generate code ONCE per function *)
  List.iter (fun ((mp, sel), wrapper_name) ->
    match wrapper_name with
    | Some name ->
      (* Set up visibility context for name resolution during code generation *)
      push_visible mp [];
      let func_sels = List.filter is_func_decl sel in
      let old_decls = !current_structure_decls in
      current_structure_decls := sel;

      (* CRITICAL CALL: pp_wrapper_module_dual generates code ONCE and returns:
         - p_specs: forward declarations to inject into Dnspace struct
         - p_defs: full out-of-line definitions with WrapperName:: prefix
         - p_lifted: template helper functions (e.g., _foo_aux from local fixpoints) *)
      let (p_specs, p_defs, p_lifted) = pp_wrapper_module_dual ~is_header ~wrapper_mp:mp name func_sels in

      current_structure_decls := old_decls;

      (* Store forward declarations in pending_wrapper_decls for Dnspace injection during PASS 2.
         When a Dnspace struct with matching name is rendered (e.g., struct List),
         it consumes the forward declarations from this table and injects them as member declarations. *)
      if not (Pp.ismt p_specs) then begin
        Hashtbl.replace pending_wrapper_decls name p_specs;
        Hashtbl.replace unmerged_wrappers name ()
      end;

      (* Accumulate definitions for emission AFTER PASS 2 (after all types are defined).
         Template definitions reference types that may be defined in later structs, so
         we defer their emission until all structs are complete. *)
      if not (Pp.ismt p_defs) then
        deferred_defs_acc := !deferred_defs_acc ++ cut2 () ++ p_defs;

      (* Accumulate lifted template helpers for emission AFTER PASS 2.
         These are template functions extracted from local fixpoints during gen_dfun.
         They must appear before the functions that use them, but after the functions
         that generated them (in case they reference types from those functions). *)
      if not (Pp.ismt p_lifted) then
        deferred_lifted_acc := !deferred_lifted_acc ++ cut2 () ++ p_lifted;

      pop_visible ()
    | None -> ()
  ) wrapper_names;
  let deferred_defs = !deferred_defs_acc in
  let deferred_lifted = !deferred_lifted_acc in
  (* Build the name resolution cache AFTER PASS 1 so that unmerged_wrappers
     and collision_wrapper_table are fully populated.  The cache pre-computes
     all C++ names so the pretty-printer can look them up directly. *)
  name_cache := Some (Name_resolution.create
    ~structure_analysis:analysis
    ~wrapper_modules:wrapper_module_table
    ~collision_wrappers:collision_wrapper_table
    ~global_scope_enums:global_scope_enum_table
    ~eponymous_records:global_eponymous_record_registry
    ~unmerged:unmerged_wrappers
    s);
  (* PASS 2: Render all modules. For wrapper modules, only render non-function
     declarations (inductives, types). For non-wrapper modules, render everything
     normally. Dnspace rendering picks up pending_wrapper_decls entries.

     IMPORTANT: We keep the same push_visible/pop_visible pattern as the original code.
     All modules push visibility, and for non-modular mode, visibility is only
     popped at the end. This ensures that when rendering the main module (e.g.,
     TopSort), references to imported module functions (e.g., map) are resolved
     correctly without spurious module qualification.

     Remaining standalone wrapper structs (not consumed by any Dnspace) are emitted
     just before the first non-wrapper module (main module). This ensures all types
     referenced by wrapper struct forward declarations are already defined, and all wrapper
     structs are defined before the main module references them. *)
  let ppl ((mp, sel), wrapper_name) =
    let old_decls = !current_structure_decls in
    current_structure_decls := sel;
    push_visible mp [];
    let p = match wrapper_name with
      | Some name ->
        (* Only render non-function declarations. Functions were pre-rendered
           and stored in pending_wrapper_decls for Dnspace injection. *)
        let type_sels = List.filter (fun x -> not (is_func_decl x)) sel in
        let type_pp = prlist_sep_nonempty cut2 f type_sels in
        (* If this wrapper module produced no type output (no Dnspace consumed
           its pending declarations), emit a standalone wrapper struct here.
           This preserves the topological sort order: standalone wrappers like
           Bool are emitted before types like Ascii that depend on them via
           inlined method bodies. *)
        if Pp.ismt type_pp && is_header then
          match Hashtbl.find_opt pending_wrapper_decls name with
          | Some specs ->
            Hashtbl.remove pending_wrapper_decls name;
            str "struct " ++ str name ++ str " {" ++ fnl () ++ specs ++ fnl () ++ str "};"
          | None -> mt ()
        else
          type_pp
      | None ->
        (* Check if this module has SEmodule children whose names collide with
           global inductives from other modules (e.g., BinNat has module N which
           collides with inductive N from BinNums). If so, wrap this module's
           output in a parent struct to disambiguate. *)
        (* Check if child module contains an eponymous inductive *)
        let child_has_eponymous_ind child_name se =
          match se with
          | SEmodule m ->
            (match m.ml_mod_expr with
             | MEstruct (_inner_mp, inner_sel) ->
               List.exists (fun (_l', se') ->
                 match se' with
                 | SEdecl (Dind (kn, ind)) ->
                   let found = ref false in
                   Array.iteri (fun i _p ->
                     let ind_ref = GlobRef.IndRef (kn, i) in
                     let ind_name = Common.pp_global_name Type ind_ref in
                     let ind_name_cap = String.capitalize_ascii ind_name in
                     if String.equal ind_name_cap child_name then found := true
                   ) ind.ind_packets;
                   !found
                 | _ -> false
               ) inner_sel
             | _ -> false)
          | _ -> false
        in
        (* Check if there's a sibling inductive in this module matching the given name *)
        let has_sibling_inductive child_name =
          List.exists (fun (_l', se') ->
            match se' with
            | SEdecl (Dind (kn, ind)) ->
              let found = ref false in
              Array.iteri (fun i _p ->
                let ind_ref = GlobRef.IndRef (kn, i) in
                let ind_name = Common.pp_global_name Type ind_ref in
                let ind_name_cap = String.capitalize_ascii ind_name in
                if String.equal ind_name_cap child_name then found := true
              ) ind.ind_packets;
              !found
            | _ -> false
          ) sel
        in
        let has_child_collision = is_modfile mp && List.exists (fun (l, se) ->
          match se with
          | SEmodule _ ->
            let child_name = String.capitalize_ascii (Label.to_string l) in
            (match Hashtbl.find_opt global_inductive_names child_name with
             | Some ind_mp ->
               let is_collision =
                 not (ModPath.equal ind_mp mp)
                 && not (child_has_eponymous_ind child_name se)
                 && not (has_sibling_inductive child_name)
               in
               is_collision
             | None -> false)
          | _ -> false
        ) sel in
        if has_child_collision then begin
          let parent_name = String.capitalize_ascii (string_of_modfile mp) in
          (* Identify which child modules collide with global inductives *)
          let is_colliding_child l se =
            let child_name = String.capitalize_ascii (Label.to_string l) in
            match Hashtbl.find_opt global_inductive_names child_name with
            | Some ind_mp ->
              not (ModPath.equal ind_mp mp)
              && not (child_has_eponymous_ind child_name se)
              && not (has_sibling_inductive child_name)
            | None -> false
          in
          (* Register colliding child module paths so references get parent qualification *)
          let register_decl_modpaths qualified inner_sel =
            List.iter (fun (_l', se') ->
              match se' with
              | SEdecl (Dterm (r, _, _)) ->
                let rmp = modpath_of_r r in
                Hashtbl.replace wrapper_module_table rmp qualified;
                Hashtbl.replace collision_wrapper_table rmp ()
              | SEdecl (Dfix (rn, _, _)) ->
                Array.iter (fun r ->
                  let rmp = modpath_of_r r in
                  Hashtbl.replace wrapper_module_table rmp qualified;
                  Hashtbl.replace collision_wrapper_table rmp ()
                ) rn
              | _ -> ()
            ) inner_sel
          in
          List.iter (fun (l, se) ->
            match se with
            | SEmodule m when is_colliding_child l se ->
              let vis_mp = MPdot (mp, l) in
              Hashtbl.replace wrapper_module_table vis_mp parent_name;
              Hashtbl.replace collision_wrapper_table vis_mp ();
              (match m.ml_mod_expr with
               | MEstruct (inner_mp, inner_sel) ->
                 Hashtbl.replace wrapper_module_table inner_mp parent_name;
                 Hashtbl.replace collision_wrapper_table inner_mp ();
                 register_decl_modpaths parent_name inner_sel
               | MEident alias_mp ->
                 Hashtbl.replace wrapper_module_table alias_mp parent_name;
                 Hashtbl.replace collision_wrapper_table alias_mp ()
               | _ -> ())
            | _ -> ()
          ) sel;
          (* Render: colliding child modules have their body rendered directly
             (functions as flat forward declarations), non-colliding entries render normally *)
          if is_header then begin
            let (non_colliding_pp, colliding_pp) = with_render_ctx
              ~setup:(fun () -> in_struct_context := true)
              (fun () ->
                let non_colliding = List.filter (fun (l, se) ->
                  match se with
                  | SEmodule se_inner -> not (is_colliding_child l (SEmodule se_inner))
                  | _ -> true
                ) sel in
                let non_colliding_pp = prlist_sep_nonempty cut2 f non_colliding in
                let colliding_pp = prlist_sep_nonempty cut2 (fun (_l, se) ->
                  match se with
                  | SEmodule m ->
                    (match m.ml_mod_expr with
                     | MEstruct (inner_mp, inner_sel) ->
                       push_visible inner_mp [];
                       let inner_func_sels = List.filter is_func_decl inner_sel in
                       let body = prlist_sep_nonempty cut2 f inner_func_sels in
                       pop_visible ();
                       body
                     | _ -> mt ())
                  | _ -> mt ()
                ) (List.filter (fun (l, se) -> is_colliding_child l se) sel) in
                (non_colliding_pp, colliding_pp)) in
            let body = if Pp.ismt non_colliding_pp then colliding_pp
              else if Pp.ismt colliding_pp then non_colliding_pp
              else non_colliding_pp ++ cut2 () ++ colliding_pp in
            str "struct " ++ str parent_name ++ str " {" ++ fnl () ++ body ++ fnl () ++ str "};"
          end else begin
            let (non_colliding_pp, colliding_pp) = with_render_ctx
              ~setup:(fun () ->
                current_struct_name := Some (str parent_name);
                current_struct_mp := Some mp)
              (fun () ->
                let non_colliding = List.filter (fun (l, se) ->
                  match se with
                  | SEmodule se_inner -> not (is_colliding_child l (SEmodule se_inner))
                  | _ -> true
                ) sel in
                let non_colliding_pp = prlist_sep_nonempty cut2 f non_colliding in
                let colliding_pp = prlist_sep_nonempty cut2 (fun (_l, se) ->
                  match se with
                  | SEmodule m ->
                    (match m.ml_mod_expr with
                     | MEstruct (inner_mp, inner_sel) ->
                       push_visible inner_mp [];
                       let body = prlist_sep_nonempty cut2 f inner_sel in
                       pop_visible ();
                       body
                     | _ -> mt ())
                  | _ -> mt ()
                ) (List.filter (fun (l, se) -> is_colliding_child l se) sel) in
                (non_colliding_pp, colliding_pp)) in
            let body = if Pp.ismt non_colliding_pp then colliding_pp
              else if Pp.ismt colliding_pp then non_colliding_pp
              else non_colliding_pp ++ cut2 () ++ colliding_pp in
            body
          end
        end else
          prlist_sep_nonempty cut2 f sel
    in
    current_structure_decls := old_decls;
    (if modular () then pop_visible ());
    p
  in
  (* Render all modules in topologically-sorted order.
     Standalone wrapper structs (not consumed by any Dnspace) are emitted inline
     by ppl above, preserving the dependency order from the topological sort. *)
  let rendered = List.map (fun wn -> (wn, ppl wn)) wrapper_names in
  (* Emit any remaining standalone wrapper structs that were not emitted inline.
     This handles wrappers whose pending declarations were consumed by a Dnspace
     struct during type rendering but still have unconsumed entries. *)
  let remaining_wrappers =
    if is_header then
      Hashtbl.fold (fun name specs acc ->
        let wrapper = str "struct " ++ str name ++ str " {" ++ fnl () ++ specs ++ fnl () ++ str "};" in
        acc ++ cut2 () ++ wrapper
      ) pending_wrapper_decls (mt ())
    else
      mt ()
  in
  Hashtbl.clear pending_wrapper_decls;
  (* Find insertion point: before the LAST non-wrapper entry (the main module).
     All other entries (wrapper and non-wrapper alike) go before remaining_wrappers. *)
  let rev_rendered = List.rev rendered in
  let (main_entry, pre_entries) = match rev_rendered with
    | (((_,_), None), p) :: rest -> (Some p, List.rev rest)
    | _ -> (None, rendered)  (* No main module found; shouldn't happen *)
  in
  let p_pre = prlist_sep_nonempty cut2 snd pre_entries in
  let p = match main_entry with
    | Some main_p ->
      prlist_sep_nonempty cut2 (fun x -> x) (List.filter (fun x -> not (Pp.ismt x)) [p_pre; remaining_wrappers; main_p])
    | None ->
      if Pp.ismt remaining_wrappers then p_pre
      else if Pp.ismt p_pre then remaining_wrappers
      else p_pre ++ cut2 () ++ remaining_wrappers
  in
  (* ============================================================================
     FINAL ASSEMBLY: Emit everything in the correct order
     ============================================================================

     OUTPUT ORDER:
     1. p                : Type declarations (inductives) + remaining_wrappers + main module
     2. deferred_lifted  : Template helpers from COMBINED PASS (wrapper module code gen)
     3. pass2_lifted_pp  : Template helpers from PASS 2 (main module code gen)
     4. deferred_defs    : Out-of-line function definitions from COMBINED PASS

     ORDERING RATIONALE:

     (1) Type declarations FIRST:
         All struct definitions (List, ListDef, etc.) must be complete before
         function definitions reference them.

     (2) deferred_lifted BEFORE pass2_lifted_pp:
         Lifted decls from wrapper modules (deferred_lifted) may be referenced by
         main module functions. They must be defined before pass2_lifted_pp which
         may call them.

     (3) pass2_lifted_pp BEFORE deferred_defs:
         Some wrapper module functions (deferred_defs) may call lifted helpers
         from the main module (pass2_lifted_pp). The helpers must be defined first.

     (4) deferred_defs LAST:
         Out-of-line definitions like "WrapperName::func(...)" reference both
         types (from p) and helpers (from deferred_lifted + pass2_lifted_pp).

     LIFTED DECLARATIONS EXPLAINED:
     When gen_dfun encounters a local fixpoint (nested recursive function),
     it extracts it as a separate template function (e.g., _foo_aux) via
     add_lifted_decl. These lifted functions are collected and must appear
     before the function that uses them.

     - deferred_lifted: Lifted from wrapper module functions during COMBINED PASS
     - pass2_lifted: Lifted from main module functions during PASS 2
       Example: If main module function "foo" has a local fixpoint, gen_dfun
       creates "_foo_aux" and stores it via add_lifted_decl. We collect it
       here via take_lifted_decls() and emit it before deferred_defs. *)

  let pass2_lifted = Translation.take_lifted_decls () in
  let pass2_lifted_pp = if is_header then
    prlist_sep_nonempty cut2 (fun d -> pp_cpp_decl (empty_env ()) d) pass2_lifted
  else mt () in

  (* For non-modular mode, pop remaining visible entries. *)
  (if not (modular ()) then
    repeat (List.length wrapper_names) pop_visible ());

  (* Emit everything in the correct order (see ordering rationale above) *)
  v 0 (p ++ deferred_lifted ++ pass2_lifted_pp ++ deferred_defs) ++ fnl ()

let do_struct f s =
  let ppl (mp,sel) =
    push_visible mp [];
    let p = prlist_sep_nonempty cut2 f sel in
    (* for monolithic extraction, we try to simulate the unavailability
       of [MPfile] in names by artificially nesting these [MPfile] *)
    (if modular () then pop_visible ()); p
  in
  let p = prlist_sep_nonempty cut2 ppl s in
  (if not (modular ()) then repeat (List.length s) pop_visible ());
  v 0 p ++ fnl ()

let pp_struct s = do_struct_with_decl_tracking ~is_header:false (pp_structure_elem ~is_header:false pp_decl) s
let pp_hstruct s = do_struct_with_decl_tracking ~is_header:true (pp_structure_elem ~is_header:true pp_hdecl) s

let pp_signature s = do_struct pp_specif s

let cpp_descr = {
  keywords = keywords;
  file_suffix = ".cpp";
  file_naming = file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  pp_hstruct = pp_hstruct;
  sig_suffix = Some ".h";
  sig_preamble = sig_preamble;
  pp_sig = pp_signature;
  pp_decl = pp_decl;
}
