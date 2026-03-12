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

(** Name resolution and qualification helpers for C++ code generation.

    This module contains all functions related to resolving and qualifying C++
    names for Rocq references: global names, inductive type names, struct
    qualifiers, typename prefixes, and cache-backed lookups. *)

open Pp
open Names
open Table
open Miniml
open Modutil
open Common
open Minicpp
open Cpp_state

(** {2 Global name printing} *)

(** Beware of the side-effects of [pp_global] and [pp_modname]. They are used to
    update table of content for modules. Many [let] below should not be altered
    since they force evaluation order. *)

let str_global_with_key k key r =
  match find_custom_opt r with
  | Some custom_str when to_inline r -> custom_str
  | _ -> Common.pp_global_with_key k key r

let str_global k r = str_global_with_key k (repr_of_r r) r

let pp_global_with_key k key r = str (str_global_with_key k key r)

let pp_global k r = str (str_global k r)

let pp_global_name k r = str (Common.pp_global k r)

let pp_modname mp = str (Common.pp_module mp)

(** Check if a non-local inductive's Dnspace wrapper was merged with its inner
    struct. Returns true if the wrapper WAS merged (no pending declarations →
    use List<A>). Returns false if it was NOT merged (has pending declarations →
    use List::list<A>). *)
let is_merged_inductive (r : GlobRef.t) : bool =
  let base = str_global Type r in
  let wrapper_name = String.capitalize_ascii base in
  not (Hashtbl.mem unmerged_wrappers wrapper_name)

(** grammar from OCaml 4.06 manual, "Prefix and infix symbols" *)

let infix_symbols =
  ['='; '<'; '>'; '@'; '^'; ';'; '&'; '+'; '-'; '*'; '/'; '$'; '%']

let operator_chars =
  [
    '!';
    '$';
    '%';
    '&';
    '*';
    '+';
    '-';
    '.';
    '/';
    ':';
    '<';
    '=';
    '>';
    '?';
    '@';
    '^';
    '|';
    '~';
  ]

(** infix ops in OCaml, but disallowed by preceding grammar *)

let builtin_infixes = ["::"; ","]

let substring_all_opchars s start stop =
  let rec check_char i =
    if i >= stop then
      true
    else
      List.mem s.[i] operator_chars && check_char (i + 1)
  in
  check_char start

let is_infix r =
  match find_custom_opt r with
  | Some s when to_inline r ->
    let len = String.length s in
    len >= 3
    (* parenthesized *)
    && s.[0] == '('
    && s.[len - 1] == ')'
    &&
    let inparens = String.trim (String.sub s 1 (len - 2)) in
    let inparens_len = String.length inparens in
    (* either, begins with infix symbol, any remainder is all operator chars *)
    List.mem inparens.[0] infix_symbols
    && substring_all_opchars inparens 1 inparens_len
    (* or, starts with #, at least one more char, all are operator chars *)
    || inparens.[0] == '#'
       && inparens_len >= 2
       && substring_all_opchars inparens 1 inparens_len
    ||
    (* or, is an OCaml built-in infix *)
    List.mem inparens builtin_infixes
  | _ -> false

let get_infix r =
  let s = find_custom r in
  String.sub s 1 (String.length s - 2)

let get_ind =
  let open GlobRef in
  function
    | IndRef _ as r -> r
    | ConstructRef (ind, _) -> IndRef ind
    | _ -> CErrors.anomaly (Pp.str "get_ind: expected IndRef or ConstructRef")

let kn_of_ind =
  let open GlobRef in
  function
    | IndRef (kn, _) -> MutInd.user kn
    | _ -> CErrors.anomaly (Pp.str "kn_of_ind: expected IndRef")

let pp_one_field r i = function
  | Some r' -> pp_global_with_key Term (kn_of_ind (get_ind r)) r'
  | None -> pp_global Type (get_ind r) ++ str "__" ++ int i

let pp_field r fields i = pp_one_field r i (List.nth fields i)

let pp_fields r fields = List.mapi (pp_one_field r) fields

(* ============================================================================
   Helper functions to reduce code duplication
   ============================================================================ *)

(** Check if a type name is already qualified (contains ::) *)
let is_qualified_name name_str = String.contains name_str ':'

(** Check if a GlobRef is a record type (not a regular inductive). Records don't
    get wrapped in namespace structs, so they keep their original case. *)
let is_record_inductive r =
  match r with
  | GlobRef.IndRef _ -> Table.get_record_fields r <> []
  | _ -> false

(** Check if a GlobRef refers to a local inductive (defined in current module
    scope). Local inductives don't need namespace qualification (e.g.,
    List::list vs just list). *)
let is_local_inductive r =
  List.exists
    (Environ.QGlobRef.equal Environ.empty_env r)
    (Translation.get_local_inductives ())

(** Get the appropriate name for an inductive reference.
    - Local inductives: original name directly (e.g., "list", "EvenTree")
    - Non-local inductives: capitalized name (e.g., "List", "Nat") Returns
      (name_pp, needs_namespace) where:
    - name_pp is the printed name
    - needs_namespace indicates if this is a non-local inductive (capitalized)
*)
let inductive_name_info r =
  match r with
  | GlobRef.IndRef _ when is_eponymous_record_global r ->
    (str (Common.pp_type_name_capitalized r), false)
  | GlobRef.IndRef _ when is_local_inductive r -> (pp_global Type r, false)
  | GlobRef.IndRef _ -> (str (String.capitalize_ascii (str_global Type r)), true)
  | _ -> (pp_global Type r, false)

(** Check if capitalizing an enum type name would collide with its parent
    module's struct name. Returns true if so. *)
let enum_name_collides_with_parent r =
  match r with
  | GlobRef.IndRef (kn, _) ->
    let base_name = Common.pp_global_name Type r in
    let capitalized = String.capitalize_ascii base_name in
    let parent_mp = Names.MutInd.modpath kn in
    ( match parent_mp with
    | Names.ModPath.MPdot (_, label) ->
      String.equal
        capitalized
        (String.capitalize_ascii (Names.Label.to_string label))
    | _ -> false )
  | _ -> false

(** Capitalize an enum type name, avoiding collision with parent module. *)
let capitalize_enum_name s r =
  if enum_name_collides_with_parent r then
    s
  else
    String.capitalize_ascii s

(** Same as capitalize_enum_name but for qualified names (capitalize last
    component). *)
let capitalize_enum_qualified s r =
  if enum_name_collides_with_parent r then
    s
  else
    Common.capitalize_last_component s

let pp_inductive_type_name r =
  let result =
    match r with
    | GlobRef.IndRef _ when is_eponymous_record_global r ->
      str (Common.pp_type_name_capitalized r)
    | GlobRef.IndRef _ when is_record_inductive r -> pp_global Type r
    | GlobRef.IndRef _ when is_enum_inductive r ->
      let base_name = Common.pp_global_name Type r in
      str (capitalize_enum_name base_name r)
    | GlobRef.IndRef _ when is_local_inductive r -> pp_global Type r
    | GlobRef.IndRef _ ->
      let base = str_global Type r in
      if is_qualified_name base then
        str base
      else if is_merged_inductive r then
        str (String.capitalize_ascii base)
      else
        let wrapper = String.capitalize_ascii base in
        str (wrapper ^ "::" ^ base)
    | _ -> pp_global Type r
  in
  result

(** Add typename prefix for dependent types in template contexts. C++ requires
    'typename' keyword when accessing nested types in templates. *)
let typename_prefix_for name_str =
  if render_ctx.rc_in_template && is_qualified_name name_str then
    str "typename "
  else
    mt ()

(** Add struct qualification prefix if needed. When generating out-of-struct
    member function definitions, we need to qualify types that belong to the
    current struct. *)
let struct_qualifier_for r name_str =
  match render_ctx.rc_struct_name with
  | Some struct_name when not render_ctx.rc_in_struct ->
    let struct_name_str = Pp.string_of_ppcmds struct_name in
    if
      Common.contains_substring
        name_str
        (Str.global_replace (Str.regexp_string "::") "::" struct_name_str ^ "::")
    then
      mt ()
    else if Table.is_enum_inductive r then
      if Hashtbl.mem global_scope_enum_table r then
        mt ()
      else
        let full_path = Pp.string_of_ppcmds (GlobRef.print r) in
        let struct_name_dotted =
          Str.global_replace (Str.regexp_string "::") "." struct_name_str
        in
        if Common.contains_substring full_path struct_name_dotted then
          struct_name ++ str "::"
        else
          mt ()
    else
      let full_path = Pp.string_of_ppcmds (GlobRef.print r) in
      let struct_name_dotted =
        Str.global_replace (Str.regexp_string "::") "." struct_name_str
      in
      let parent_struct_dotted =
        match String.rindex_opt struct_name_dotted '.' with
        | Some i -> String.sub struct_name_dotted 0 i
        | None -> struct_name_dotted
      in
      if
        Common.contains_substring full_path struct_name_dotted
        || is_qualified_name name_str
           && Common.contains_substring full_path parent_struct_dotted
      then
        struct_name ++ str "::"
      else
        mt ()
  | _ -> mt ()

(** Check if a global function needs :: prefix to avoid name collision. When
    generating out-of-struct definitions, we add :: to call external functions
    rather than recursing into the struct's own member. *)
let needs_global_qualifier x =
  match render_ctx.rc_struct_name with
  | Some struct_name ->
    let name_str = str_global Term x in
    if is_qualified_name name_str then
      false
    else
      let full_path = Pp.string_of_ppcmds (GlobRef.print x) in
      let struct_name_str = Pp.string_of_ppcmds struct_name in
      let struct_name_dotted =
        Str.global_replace (Str.regexp_string "::") "." struct_name_str
      in
      if Common.contains_substring full_path struct_name_dotted then
        false
      else (
        match
          render_ctx.rc_struct_mp
        with
        | Some struct_mp -> not (ModPath.equal (modpath_of_r x) struct_mp)
        | None -> true )
  | None -> false

(* ============================================================================
   Cache-backed name resolution helpers
   ============================================================================
   These query the pre-computed Name_resolution cache for classification
   information (eponymous, enum, record, merged status). The actual display name
   rendering is still done by the original functions (pp_inductive_type_name,
   inductive_name_info, etc.) since they depend on the visibility context which
   is only available during rendering.

   The cache accelerates boolean queries that cpp.ml uses frequently to decide
   HOW to render a name, while the original functions produce the actual
   name. *)

(** Higher-order helper to reduce cache-fallback pattern duplication. *)
let with_cache
    (cached_lookup : Name_resolution.t -> GlobRef.t -> 'a)
    (fallback : GlobRef.t -> 'a)
    (r : GlobRef.t) : 'a =
  match !name_cache with
  | Some cache -> cached_lookup cache r
  | None -> fallback r

(** Cache-backed is_eponymous_record check — avoids hashtable lookup. *)
let is_eponymous_record_cached : GlobRef.t -> bool =
  with_cache Name_resolution.is_eponymous is_eponymous_record_global

(** Cache-backed is_global_scope_enum check — avoids hashtable lookup. *)
let is_global_scope_enum_cached : GlobRef.t -> bool =
  with_cache Name_resolution.is_global_scope_enum (fun r ->
    Hashtbl.mem global_scope_enum_table r )

(** Cache-backed is_merged_inductive check — avoids hashtable lookup. *)
let is_merged_inductive_cached : GlobRef.t -> bool =
  with_cache
    (fun cache r ->
      match Name_resolution.resolve_type cache r with
      | Some rtn -> rtn.Name_resolution.rtn_is_merged
      | None -> is_merged_inductive r )
    is_merged_inductive

(** Cache-backed inductive classification queries. *)
let get_ind_kind_cached : GlobRef.t -> Minicpp.cpp_ind_kind option =
  with_cache Name_resolution.get_ind_kind (fun _ -> None)

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

(** For display names, delegate to original functions — they need visibility
    context. These are thin wrappers for now; they become useful when we have
    more context. *)
let pp_inductive_type_name_cached r = pp_inductive_type_name r

let inductive_name_info_cached r = inductive_name_info r

let wrapper_qualify_name_cached r name = wrapper_qualify_name r name

(** Look up method info for a function reference. Checks both local
    method_candidates and global method_registry. Returns Some this_pos if the
    function is a method, None otherwise. *)
let lookup_method_this_pos n =
  let local_result =
    List.find_map
      (fun (r', _, _, pos) ->
        if Environ.QGlobRef.equal Environ.empty_env n r' then
          Some pos
        else
          None )
      !method_candidates
  in
  match local_result with
  | Some pos -> Some pos
  | None ->
  match is_registered_method n with
  | Some (_, pos) -> Some pos
  | None -> None

(** Helper module for tracking variable names *)
module IdSet = Set.Make (Names.Id)
