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
open Common
open Minicpp
open Cpp_state

(** {2 Global name printing} *)

(** Beware of the side-effects of [pp_global] and [pp_modname]. They are used to
    update table of content for modules. Many [let] below should not be altered
    since they force evaluation order. *)

(** The name of a global reference: the replacement text of an inline custom
    mapping, otherwise as resolution settles it where the printer is.
    @param k  the extraction key category (e.g. [Type] or [Term])
    @param key the [KerName] used as the lookup key in the name table
    @param r  the global reference to name *)
let global_name_with_key k key r =
  match find_custom_opt r with
  | Some custom_str when to_inline r -> Cpp_name.foreign custom_str
  | _ -> Common.global_name_with_key k key r

(** {!global_name_with_key} using the default key. *)
let global_name k r = global_name_with_key k (repr_of_r r) r

(** {!global_name_with_key} as text. *)
let str_global_with_key k key r = Cpp_name.to_string (global_name_with_key k key r)

(** {!global_name} as text. *)
let str_global k r = Cpp_name.to_string (global_name k r)

(** {!global_name_with_key} as a document. *)
let pp_global_with_key k key r = Cpp_name.pp (global_name_with_key k key r)

(** {!global_name} as a document. *)
let pp_global k r = Cpp_name.pp (global_name k r)

(** The name a typeclass concept is declared and referenced under.  A concept
    may only appear at namespace scope, so it is hoisted out of every
    enclosing struct and carries no struct qualifier -- neither at its
    declaration nor at its uses.  A use in another file still names the file's
    namespace. *)
let concept_name r =
  let name =
    match Module_plan.concept_name r with
    | Some name -> name
    | None -> Common.pp_global_name Type r
  in
  match Common.file_qualifier Type r with
  | Some file -> Cpp_name.name [Cpp_name.Namespace file] name
  | None -> Cpp_name.unqualified name

(** {!concept_name} as text. *)
let concept_name_of_ref r = Cpp_name.to_string (concept_name r)

(** {!concept_name} as a document. *)
let pp_concept_name_of_ref r = Cpp_name.pp (concept_name r)

(** Pretty-print a global name (without custom mapping) as a Pp.t. *)
let pp_global_name k r = Cpp_name.pp (Common.global_name k r)

(** Pretty-print a module path as a Pp.t. *)
let pp_modname mp = Cpp_name.pp (Common.resolve_module mp)

let module_struct_name_of name =
  let raw = Cpp_name.pp name in
  let s = Pp.string_of_ppcmds raw in
  let escaped = Table.escape_reserved_struct_name s in
  if String.equal s escaped then raw else Pp.str escaped

let module_struct_name mp = module_struct_name_of (Common.resolve_module mp)

(** Check if a non-local inductive's Dnspace wrapper was merged with its inner
    struct. Returns true if the wrapper WAS merged (no pending declarations →
    use List<A>). Returns false if it was NOT merged (has pending declarations →
    use List::list<A>). *)
let is_merged_inductive (r : GlobRef.t) : bool =
  Ref.User.Tbl.mem promoted_inductives r || not (in_unmerged_wrapper r)

(** Extract the [IndRef] from an [IndRef] or [ConstructRef]. *)
let get_ind =
  let open GlobRef in
  function
    | IndRef _ as r -> r
    | ConstructRef (ind, _) -> IndRef ind
    | _ -> CErrors.anomaly (Pp.str "get_ind: expected IndRef or ConstructRef")

(** Extract the [KerName] from an [IndRef]. *)
let kn_of_ind =
  let open GlobRef in
  function
    | IndRef (kn, _) -> MutInd.user kn
    | _ -> CErrors.anomaly (Pp.str "kn_of_ind: expected IndRef")

(** Pretty-print a single record field, using the field ref if available.
    @param r  the inductive (or constructor) reference owning the record
    @param i  zero-based field index, used as a fallback suffix when no named
              field ref exists
    @return a [Pp.t] for the field name, either from its [GlobRef] or as
            [<type>_field<i>] *)
let pp_one_field r i = function
  | Some r' -> pp_global_with_key Term (kn_of_ind (get_ind r)) r'
  | None -> pp_global Type (get_ind r) ++ str "_field" ++ int i

(** Pretty-print the [i]-th record field.
    @param r      the inductive reference owning the record
    @param fields the list of optional field [GlobRef]s for the record
    @param i      zero-based index of the field to print *)
let pp_field r fields i = pp_one_field r i (List.nth fields i)

(* ============================================================================
   Helper functions to reduce code duplication
   ============================================================================ *)

(** [mp_encloses outer mp] is whether [mp] is [outer] itself or a module
    nested inside it. *)
let rec mp_encloses outer mp =
  ModPath.equal outer mp
  ||
  match mp with
  | Names.ModPath.MPdot (parent, _) -> mp_encloses outer parent
  | _ -> false

(** How the module a reference was declared in stands to the module the struct
    being rendered came from. *)
type mp_relation =
  | Member  (** declared in that module, or in one nested inside it *)
  | Ancestor  (** declared in a module that encloses it *)
  | Unrelated  (** neither encloses the other *)

(** [mp_relation_to ~struct_mp r] classifies [r] against [struct_mp].  The
    three cases are exhaustive and mutually exclusive, which is what says that
    a reference the struct does not contain and that does not contain the
    struct is simply not a member of it. *)
let mp_relation_to ~struct_mp r =
  let r_mp = modpath_of_r r in
  if mp_encloses struct_mp r_mp then Member
  else if mp_encloses r_mp struct_mp then Ancestor
  else Unrelated

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
  List.exists (globref_equal r) (Translation_state.get_local_inductives ())

let inductive_type r args es =
  let t = Tglob (r, args, es) in
  if is_local_inductive r then t else Tnamespace (r, t)

(** [String.capitalize_ascii] of the name's text: the first character of its
    outermost qualifier, or of its base when it has none. *)
let capitalize_initial n =
  let cap = String.capitalize_ascii in
  match n with
  | Cpp_name.Name {scopes = []; base} -> Cpp_name.unqualified (cap base)
  | Cpp_name.Name {scopes = Cpp_name.Global :: _; _} -> n
  | Cpp_name.Name {scopes = s :: rest; base} ->
    let s =
      match s with
      | Cpp_name.Namespace t -> Cpp_name.Namespace (cap t)
      | Cpp_name.Class t -> Cpp_name.Class (cap t)
      | Cpp_name.Parameter t -> Cpp_name.Parameter (cap t)
      | Cpp_name.Global -> Cpp_name.Global
    in
    Cpp_name.name (s :: rest) base
  | Cpp_name.Foreign text -> Cpp_name.foreign (cap text)

(** The name with its final component capitalized. *)
let capitalize_base = Cpp_name.map_base String.capitalize_ascii

(** A type's struct name is its own, capitalized: under separate
    extraction's full qualification that is the final component; otherwise
    the name's initial, which is the final component's whenever the name is
    unqualified. *)
let capitalize_struct n =
  if Common.get_force_cross_file_qualification () then capitalize_base n else capitalize_initial n

(** Get the appropriate name for an inductive reference.
    - Local inductives: original name directly (e.g., "list", "EvenTree")
    - Non-local inductives: capitalized name (e.g., "List", "Nat")
    Returns the name and whether it is a non-local inductive's
    (capitalized) one. *)
let inductive_name r =
  let n, needs_ns =
    match r with
    | GlobRef.IndRef _ when Module_plan.is_eponymous_record r ->
      (Cpp_name.unqualified (Common.pp_type_name_capitalized r), false)
    | GlobRef.IndRef _ when Ref.User.Tbl.mem promoted_inductives r ->
      (capitalize_struct (global_name Type r), false)
    | GlobRef.IndRef _ when is_local_inductive r ->
      if Common.get_force_cross_file_qualification () then
        (Cpp_name.unqualified (String.capitalize_ascii (Common.pp_global_name Type r)), false)
      else (global_name Type r, false)
    | GlobRef.IndRef _ -> (capitalize_struct (global_name Type r), true)
    | _ -> (global_name Type r, false)
  in
  (n, needs_ns)

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

(** Capitalize an enum type name, avoiding collision with parent module.
    @param s the base (unqualified) name string of the enum type
    @param r the [GlobRef] of the enum inductive, used for collision detection
    @return [s] unchanged if capitalization would collide with the parent
            module's struct name; otherwise [String.capitalize_ascii s] *)
let capitalize_enum_name s r =
  if enum_name_collides_with_parent r then
    s
  else
    String.capitalize_ascii s

(** An enum's name, its final component capitalized unless that would collide
    with its parent module's struct name. *)
let enum_name n r = if enum_name_collides_with_parent r then n else capitalize_base n

(** The name of a promoted inductive (one that IS its module struct), from its
    resolved name: the inductive's own label goes when it is its parent
    module's, case aside, so that [Foo::foo] is [Foo] and [Ns::Trie::trie] is
    [Ns::Trie]; otherwise the final component is capitalized. *)
let promoted_name n =
  match n with
  | Cpp_name.Name {scopes; base} -> (
    match List.rev scopes with
    | (Cpp_name.Namespace parent | Cpp_name.Class parent | Cpp_name.Parameter parent) :: rev_outer
      when String.equal (String.lowercase_ascii parent) (String.lowercase_ascii base) ->
      Cpp_name.name (List.rev rev_outer) (String.capitalize_ascii parent)
    | _ -> capitalize_base n )
  | Cpp_name.Foreign _ -> capitalize_base n

(** The name without a trailing [A::A]: when its innermost qualifier is its
    final component, the qualifier goes -- if another qualifier is left in
    front of it ([X::A::A] is [X::A]), or [allow_bare] allows none ([A::A] is
    [A]).  A leading [::] names the global scope and is no qualifier here. *)
let dedup_tail ?(allow_bare = false) n =
  match n with
  | Cpp_name.Name {scopes; base} -> (
    let global, inner =
      match scopes with Cpp_name.Global :: rest -> ([Cpp_name.Global], rest) | s -> ([], s)
    in
    match List.rev inner with
    | last :: rev_outer
      when last <> Cpp_name.Global
           && String.equal (Cpp_name.scope_text last) base
           && (rev_outer <> [] || allow_bare) ->
      Cpp_name.name (global @ List.rev rev_outer) base
    | _ -> n )
  | Cpp_name.Foreign _ -> n

(** The C++ type name for an inductive reference, handling eponymous records,
    promoted inductives, enums, locals, and merged/unmerged wrappers. *)
let inductive_type_name r =
  let force = Common.get_force_cross_file_qualification () in
  match r with
  | GlobRef.IndRef _ when Module_plan.is_eponymous_record r ->
    let cap_name = Common.pp_type_name_capitalized r in
    if force && Cpp_name.is_qualified (global_name Type r) then
      Cpp_name.name [Cpp_name.Class cap_name] cap_name
    else Cpp_name.unqualified cap_name
  | GlobRef.IndRef _ when Ref.User.Tbl.mem promoted_inductives r ->
    if is_local_inductive r then
      Cpp_name.unqualified (String.capitalize_ascii (Common.pp_global_name Type r))
    else promoted_name (global_name Type r)
  | GlobRef.IndRef _ when is_record_inductive r -> global_name Type r
  | GlobRef.IndRef _ when is_enum_inductive r ->
    let n = global_name Type r in
    enum_name
      (if Cpp_name.is_qualified n then n
       else Cpp_name.unqualified (Common.pp_global_name Type r))
      r
  | GlobRef.IndRef _ when is_local_inductive r ->
    if force then capitalize_base (global_name Type r) else global_name Type r
  | GlobRef.IndRef _ ->
    let n = global_name Type r in
    if Cpp_name.is_qualified n then
      if not force then n
      else if is_merged_inductive r then promoted_name n
      else capitalize_base n
    else if is_merged_inductive r then capitalize_initial n
    else Cpp_name.inside (capitalize_initial n) (fun s -> Cpp_name.Class s) n
  | _ -> global_name Type r

(** {!inductive_type_name} as a document. *)
let pp_inductive_type_name r = Cpp_name.pp (inductive_type_name r)

(** Add typename prefix for dependent types in template contexts. C++ requires
    'typename' keyword when accessing nested types in templates. *)
let typename_prefix_for n =
  if (!render_ctx).rc_in_template && Cpp_name.is_qualified n then
    str "typename "
  else
    mt ()

(** Whether the qualifiers [quals], outermost first, are written in [n],
    one after another. *)
let names_through n quals =
  let texts = List.map Cpp_name.scope_text (Cpp_name.scopes n) in
  let rec starts_with = function
    | _, [] -> true
    | t :: ts, q :: qs -> String.equal t q && starts_with (ts, qs)
    | [], _ :: _ -> false
  in
  let rec somewhere = function
    | [] -> quals = []
    | _ :: rest as ts -> starts_with (ts, quals) || somewhere rest
  in
  match n with
  | Cpp_name.Foreign text -> Common.contains_substring text (String.concat "::" quals ^ "::")
  | Cpp_name.Name _ -> somewhere texts

(** The struct qualifiers to write in front of [r]'s type name [n] when
    generating out-of-struct definitions.

    In a [.cpp] file, types defined inside the enclosing struct need to be
    qualified (e.g. [MyStruct::NestedType]) because the return-type position
    is outside the class scope.
    @param r the global reference whose C++ type name may need a struct
             qualifier
    @param n the name [r] is otherwise written under
    @return the qualifiers, outermost first, when qualification is required,
            or none otherwise *)
let struct_scopes_for r n =
  match (!render_ctx).rc_scope with
  | Some scope when not (!render_ctx).rc_in_struct ->
    let classes = List.map (fun s -> Cpp_name.Class s) in
    let struct_scopes = classes scope.Scope_plan.qualifier in
    (* How [r]'s module stands to the struct's, by kernel path: the textual
       tests below fire on a sibling module whose path merely contains the
       struct's name -- a file named after its module. *)
    let relation = mp_relation_to ~struct_mp:scope.Scope_plan.module_ r in
    let member_of_struct () = relation = Member in
    (* Already qualified by the struct -- nothing to add. *)
    if names_through n scope.Scope_plan.qualifier then []
    (* An inductive promoted to the struct, and an eponymous record merged
       into it, is the struct, and qualified by its own name it would name
       the struct's constructor; it takes the qualifier the struct itself is
       written with. *)
    else if
      (Ref.User.Tbl.mem promoted_inductives r || Module_plan.is_eponymous_record r)
      && ModPath.equal (modpath_of_r r) scope.Scope_plan.module_
    then
      match List.rev struct_scopes with
      | _ :: (_ :: _ as enclosing) -> List.rev enclosing
      | _ -> []
    (* Eponymous records are merged into the module struct at global scope,
       so they don't get an extra wrapper prefix.  However, when the record
       itself lives inside the current struct (nested sub-module), we must
       still qualify it in the [.cpp] file. *)
    else if Module_plan.is_eponymous_record r then
      if member_of_struct () then struct_scopes else []
    (* Non-local records are placed at C++ global scope (before the struct),
       so they never need the struct prefix. *)
    else if is_record_inductive r && not (is_local_inductive r) then []
    (* Enums at global scope need no prefix; those inside the struct do. *)
    else if Table.is_enum_inductive r then
      if Module_plan.is_global_scope_enum r then []
      else if member_of_struct () then struct_scopes
      else []
    (* A name the struct's module contributes to global scope rather than to
       the struct is never a member of it: a [using T = ...] alias, which C++
       puts outside, and a type class instance, which Crane lifts out so that
       a concept's template argument can be written unqualified.  Both are
       recorded by the module layout, which knows where the declaration goes;
       the kernel module path consulted below only knows where it came from,
       and for these two answers [Member]. *)
    else if Module_plan.is_global_scope_type r then []
    (* The kernel module path settles the question: the type is a member of
       this struct exactly when it was declared in the module the struct came
       from, or in one nested inside it.  Comparing the struct's C++ name with
       the type's Rocq path instead gives up whenever the module was emitted
       under a different name -- a duplicate-avoidance rename ([Pos] and
       [Coq_Pos]) or a collision suffix -- and fires spuriously when the paths
       merely share a prefix, as they do when the enclosing library is named
       after the module.  A type declared in a module that neither contains
       nor is contained by this struct's is not a member of it, so it takes no
       qualifier at all. *)
    else (
      match relation with
      | Member -> struct_scopes
      | Unrelated -> []
      (* A name declared in a module that encloses this struct is qualified by
         that module, never by the struct -- and only when the module is
         emitted as a struct of its own.  The extraction root is not: its
         members sit at global scope, so the bare name is already right.  A
         module that is a struct is named as its plan qualifies its
         out-of-line members ({!Scope_plan.qualifier}). *)
      | Ancestor -> (
        match Scope_plan.of_module (modpath_of_r r) with
        | Some sc when Common.is_struct_module (modpath_of_r r) -> classes sc.Scope_plan.qualifier
        | _ -> [] ) )
  | _ -> []

(** The global-scope qualifier [::] in front of a type name when a
    module-local inductive of the same name shadows it.

    A user inductive named [Nat] is rendered inside its module struct as
    [Nat], which is exactly the name Crane gives the runtime [nat] at C++
    global scope.  Unqualified lookup from inside the struct then finds the
    user's type, so [static Nat toNat(const Nat &n)] declares the wrong return
    type.  Naming the global one [::Nat] is unambiguous wherever it appears --
    including inside the global struct itself -- so no other name has to move.

    The nested names come from {!Cpp_state.nested_struct_names}, recorded by
    the struct printer itself, so the shadow test compares against the name
    that was actually emitted. *)
let global_scopes_for r n =
  match r with
  | GlobRef.IndRef _ when not (Cpp_name.is_qualified n) ->
    if Cpp_state.is_shadowed_global_name (Cpp_name.to_string n) r then [Cpp_name.Global] else []
  | _ -> []

let wrapper_qualify = Cpp_state.wrapper_qualify

(** The name a type is written under, from outside the struct that owns it.

    A module a name collision forced into a struct keeps its declarations
    there, so a use of one from elsewhere has to say which struct -- the same
    answer {!Cpp_state.wrapper_qualify} already gives the {i term} printer for
    a call into such a module.  Only the term printer was asking: an inductive
    reaches the reader through {!inductive_name}, which qualifies for its own
    reasons, and everything else a wrapped module declares -- a type class
    instance above all, named as a concept's template argument -- came out
    bare.

    The exceptions are the ones {!struct_scopes_for} already makes, and for
    its reasons: a [using T = ...] alias and a {i lifted} instance are
    contributed to namespace scope rather than to the struct, so the module
    path they came from does not say where they went.

    An inductive is excluded outright.  It reaches the reader through
    {!inductive_name} and the [Tnamespace] machinery, which qualify it for
    their own reasons and by their own spelling; asking here as well turns a
    settled [List<A>] into [Datatypes::template List<A>].  A type class is
    excluded for the reason {!concept_name_of_ref} gives: a concept may only be
    declared at namespace scope, so it is never inside the struct to begin
    with.

    Inside the struct the qualifier must not be written at all.  The class is
    incomplete while its own body is being printed, so [Wrapper::member] there
    names nothing -- and the member is in scope unqualified anyway. *)
let wrapper_qualified_type_name r n =
  match r with
  | GlobRef.IndRef _ | GlobRef.ConstructRef _ -> n
  | _ when Table.is_typeclass r -> n
  | _ when Module_plan.is_global_scope_type r -> n
  | _ -> if (!render_ctx).rc_in_struct then n else wrapper_qualify r n

(** Check if a global function needs :: prefix to avoid name collision. When
    generating out-of-struct definitions, we add :: to call external functions
    rather than recursing into the struct's own member. *)
let needs_global_qualifier x =
  match (!render_ctx).rc_scope with
  | Some scope ->
    (not (Cpp_name.is_qualified (global_name Term x)))
    && not (mp_encloses (modpath_of_r x) scope.Scope_plan.module_)
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

(** Higher-order helper to reduce cache-fallback pattern duplication.
    Queries [cached_lookup] when [name_cache] is populated; otherwise falls
    back to [fallback].
    @param cached_lookup function applied to the [Name_resolution.t] cache and
                         [r] when the cache is available
    @param fallback      function applied to [r] when no cache is present
    @param r             the global reference to classify
    @return the result of [cached_lookup] or [fallback], depending on cache
            availability *)
let with_cache
    (cached_lookup : Name_resolution.t -> GlobRef.t -> 'a)
    (fallback : GlobRef.t -> 'a)
    (r : GlobRef.t) : 'a =
  match !name_cache with
  | Some cache -> cached_lookup cache r
  | None -> fallback r

(** Cache-backed is_eponymous_record check — avoids hashtable lookup. *)
let is_eponymous_record_cached : GlobRef.t -> bool =
  with_cache Name_resolution.is_eponymous Module_plan.is_eponymous_record

(** Cache-backed is_global_scope_enum check — avoids hashtable lookup. *)
let is_global_scope_enum_cached : GlobRef.t -> bool =
  with_cache Name_resolution.is_global_scope_enum (fun r ->
    Module_plan.is_global_scope_enum r )

(** Cache-backed inductive classification queries. *)
let get_ind_kind_cached : GlobRef.t -> Minicpp.cpp_ind_kind option =
  with_cache Name_resolution.get_ind_kind (fun _ -> None)

(** Cache-backed enum check — falls back to [is_enum_inductive]. *)
let is_enum_cached (r : GlobRef.t) : bool =
  match get_ind_kind_cached r with
  | Some IK_Enum -> true
  | Some _ -> false
  | None -> is_enum_inductive r

(** Cache-backed record check — falls back to [is_record_inductive]. *)
let is_record_cached (r : GlobRef.t) : bool =
  match get_ind_kind_cached r with
  | Some (IK_Record _ | IK_Eponymous _) -> true
  | Some _ -> false
  | None -> is_record_inductive r

(** How an inductive's struct is spelled where it is declared. *)
type struct_spelling =
  | Eponymous_record_name  (** Its module's struct's name, capitalised. *)
  | Capitalized  (** Its own name, capitalised. *)
  | As_declared  (** Its own name. *)

(** The spelling of [id]'s struct at its declaration, [local] where the
    declaration is rendered among the inductives local to it: a promoted
    inductive, and one a reference sees as merged, take the merged spelling. *)
let struct_spelling ?(merged = is_merged_inductive)
    ?(promoted = Ref.User.Tbl.mem promoted_inductives) ~local id =
  match id with
  | GlobRef.IndRef _ when is_eponymous_record_cached id -> Eponymous_record_name
  | GlobRef.IndRef _ when promoted id -> Capitalized
  | GlobRef.IndRef _ when is_record_cached id -> As_declared
  | GlobRef.IndRef _ when Common.get_force_cross_file_qualification () -> Capitalized
  | GlobRef.IndRef _ when (not local) && merged id ->
    (* An inductive written straight into an enclosing struct has no
       namespace wrapper to be merged with, so nothing capitalised its
       declaration -- but a reference to it, being neither local nor behind
       an unmerged wrapper, spells the merged name.  One struct cannot be
       declared [dval] and named [Dval]; the reference is what every other
       file sees, so the declaration follows it. *)
    Capitalized
  | _ -> As_declared

(** An enum's name where it is declared: its own, unqualified there. *)
let enum_declaration_name r = capitalize_enum_name (Common.pp_global_name Type r) r

(** {!struct_spelling} as a string. *)
let struct_declaration_name ?merged ?promoted ~local id =
  match struct_spelling ?merged ?promoted ~local id with
  | Eponymous_record_name -> Common.pp_type_name_capitalized id
  | Capitalized -> String.capitalize_ascii (Common.pp_global_name Type id)
  | As_declared -> Common.pp_global_name Type id

(** Look up method info for a function reference in the method registry,
    where every candidate a render collects is registered
    ({!Method_registry.planned_candidate}). Returns Some this_pos if the
    function is a method, None otherwise.

    The answer is in the numbering of the arguments a C++ call site writes,
    not of the ML type's arrows: a candidate records the ML position, which is
    what reading its body wants, and an erased argument -- a dictionary, a
    [void] -- separates the two; the registry records the C++ one. *)
let lookup_method_this_pos n = Option.map snd (is_registered_method n)

let method_type_args n tys =
  match tys with
  | [] -> []
  | _ ->
    let carried = lookup_method_ind_tvar_positions n in
    let dropped = Callable_abi.dropped_positions n in
    List.filteri (fun i _ -> not (List.mem i carried || List.mem i dropped)) tys

module IdSet = Set.Make (Names.Id)
