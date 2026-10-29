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

let checked key ~live n =
  ( if Probe.checking () then
      let here = live () in
      if not (Cpp_name.equal n here) then
        Probe.violation "names resolved"
          Pp.(
            Cpp_resolution.pp_key key ++ str " was resolved as " ++ str (Cpp_name.to_string n)
            ++ str " where the declaration naming it is written, and is named " ++ str (Cpp_name.to_string here)
            ++ str " where it is printed" ) );
  n

let unresolved key = CErrors.anomaly Pp.(str "Crane: " ++ Cpp_resolution.pp_key key ++ str " was printed before it was resolved.")

let name_from names frame key ~live =
  match Cpp_resolution.find names frame key with
  | Found n -> checked key ~live n
  | Unresolved -> unresolved key
  | Not_requested ->
    CErrors.anomaly
      Pp.(str "Crane: a declaration names " ++ Cpp_resolution.pp_key key ++ str ", which resolving it did not ask for.")

(* [key]'s name at the position [c]: from the names of the declaration of
   the tree being written, at the frame printing it has entered, if one is
   being written; [live ()] where none is. *)
let named (c : render_ctx) key live =
  match c.rc_names with None -> live () | Some names -> name_from names c.rc_frame key ~live

(** The name of a global reference at the position [c]: the replacement text
    of an inline custom mapping, otherwise as resolution settles it there.
    @param k  the extraction key category (e.g. [Type] or [Term])
    @param r  the global reference to name *)
let global_name c k r =
  match find_custom_opt r with
  | Some custom_str when to_inline r -> Cpp_name.foreign custom_str
  | _ -> named c (Unmapped (k, r)) (fun () -> Common.global_name k r)

(** {!global_name} as text. *)
let str_global c k r = Cpp_name.to_string (global_name c k r)

(** The name [r] is declared under, wherever it is declared: the replacement
    text of an inline custom mapping, otherwise its own short name. *)
let declared_name k r =
  match find_custom_opt r with Some custom_str when to_inline r -> custom_str | _ -> Common.pp_global_name k r

(** {!global_name} as a document. *)
let pp_global c k r = Cpp_name.pp (global_name c k r)

(** The name a typeclass concept is declared and referenced under.  A concept
    may only appear at namespace scope, so it is hoisted out of every
    enclosing struct and carries no struct qualifier -- neither at its
    declaration nor at its uses.  A use in another file still names the file's
    namespace. *)
let concept_name c r =
  named c (Class_concept r) @@ fun () ->
  let name =
    match Module_plan.concept_name r with
    | Some name -> name
    | None -> Common.pp_global_name Type r
  in
  match Common.file_qualifier Type r with
  | Some file -> Cpp_name.name [Cpp_name.Namespace file] name
  | None -> Cpp_name.unqualified name

(** {!concept_name} as text. *)
let concept_name_of_ref c r = Cpp_name.to_string (concept_name c r)

(** {!concept_name} as a document. *)
let pp_concept_name_of_ref c r = Cpp_name.pp (concept_name c r)

let module_struct_name_of name =
  let raw = Cpp_name.pp name in
  let s = Pp.string_of_ppcmds raw in
  let escaped = Table.escape_reserved_struct_name s in
  if String.equal s escaped then raw else Pp.str escaped

let module_declared_name mp = Table.escape_reserved_struct_name (Common.emitted_module_name mp)

(** Whether the inductive [r] is promoted at the position [c]: promoted by
    the unit's plan, which nothing demotes in place, and not demoted in the
    body of the module whose element is being written
    ({!Module_frame.demoted_around}). *)
let promoted_at (c : render_ctx) r =
  Ref.User.Tbl.mem promoted_inductives r
  &&
  match c.rc_module with
  | Some mp -> not (List.exists (globref_equal r) (Module_frame.demoted_around mp))
  | None -> true

(** Whether a non-local inductive's Dnspace wrapper was merged with its inner
    struct at the position [c]: true if the wrapper WAS merged (no pending
    declarations, so List<A>); false if it was NOT merged (has pending
    declarations, so List::list<A>). *)
let merged_at c r = promoted_at c r || not (in_unmerged_wrapper r)

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
    scope), as the declaration generator sees it. Local inductives don't need
    namespace qualification (e.g., List::list vs just list).  The printer asks
    its position instead ({!local_at}). *)
let is_local_inductive r =
  List.exists (globref_equal r) (Translation_state.get_local_inductives ())

(** Whether [r] is an inductive spelled bare at the position [c]: one the body
    of the module whose element is being written spells bare, as planned
    ({!Scope_plan.local_inductives}); none where no module's element is. *)
let local_at (c : render_ctx) r =
  match c.rc_module with
  | None -> false
  | Some mp -> (
    match Scope_plan.local_inductives mp with
    | Some local -> List.exists (globref_equal r) local
    | None ->
      CErrors.anomaly
        Pp.(str "Crane: the body of the module " ++ str (ModPath.to_string mp) ++ str " has no planned local inductives.") )

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
let inductive_name ctx r =
  let n, needs_ns =
    match r with
    | GlobRef.IndRef _ when Module_plan.is_eponymous_record r ->
      (Cpp_name.unqualified (Common.pp_type_name_capitalized r), false)
    | GlobRef.IndRef _ when promoted_at ctx r ->
      (capitalize_struct (global_name ctx Type r), false)
    | GlobRef.IndRef _ when local_at ctx r ->
      if Common.get_force_cross_file_qualification () then
        (Cpp_name.unqualified (String.capitalize_ascii (Common.pp_global_name Type r)), false)
      else (global_name ctx Type r, false)
    | GlobRef.IndRef _ -> (capitalize_struct (global_name ctx Type r), true)
    | _ -> (global_name ctx Type r, false)
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
let inductive_type_name ctx r =
  let force = Common.get_force_cross_file_qualification () in
  match r with
  | GlobRef.IndRef _ when Module_plan.is_eponymous_record r ->
    let cap_name = Common.pp_type_name_capitalized r in
    if force && Cpp_name.is_qualified (global_name ctx Type r) then
      Cpp_name.name [Cpp_name.Class cap_name] cap_name
    else Cpp_name.unqualified cap_name
  | GlobRef.IndRef _ when promoted_at ctx r ->
    if local_at ctx r then
      Cpp_name.unqualified (String.capitalize_ascii (Common.pp_global_name Type r))
    else promoted_name (global_name ctx Type r)
  | GlobRef.IndRef _ when is_record_inductive r -> global_name ctx Type r
  | GlobRef.IndRef _ when is_enum_inductive r ->
    let n = global_name ctx Type r in
    enum_name
      (if Cpp_name.is_qualified n then n
       else Cpp_name.unqualified (Common.pp_global_name Type r))
      r
  | GlobRef.IndRef _ when local_at ctx r ->
    if force then capitalize_base (global_name ctx Type r) else global_name ctx Type r
  | GlobRef.IndRef _ ->
    let n = global_name ctx Type r in
    if Cpp_name.is_qualified n then
      if not force then n
      else if merged_at ctx r then promoted_name n
      else capitalize_base n
    else if merged_at ctx r then capitalize_initial n
    else Cpp_name.inside (capitalize_initial n) (fun s -> Cpp_name.Class s) n
  | _ -> global_name ctx Type r

(** Add typename prefix for dependent types in template contexts. C++ requires
    'typename' keyword when accessing nested types in templates. *)
let typename_prefix_for (ctx : render_ctx) n =
  if ctx.rc_in_template && Cpp_name.is_qualified n then
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
let struct_scopes_for (ctx : render_ctx) r n =
  match ctx.rc_scope with
  | Some scope when not ctx.rc_in_struct ->
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
      (promoted_at ctx r || Module_plan.is_eponymous_record r)
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
    else if is_record_inductive r && not (local_at ctx r) then []
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

    The nested names come from {!Cpp_state.nested_struct_names}, installed
    from the plan before anything is printed ({!Install_legacy_plan}); the
    printer checks, under [CRANE_CHECK_IR], that it printed exactly those. *)
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
let wrapper_qualified_type_name (ctx : render_ctx) r n =
  match r with
  | GlobRef.IndRef _ | GlobRef.ConstructRef _ -> n
  | _ when Table.is_typeclass r -> n
  | _ when Module_plan.is_global_scope_type r -> n
  | _ -> if ctx.rc_in_struct then n else wrapper_qualify r n

(** Check if a global function needs :: prefix to avoid name collision. When
    generating out-of-struct definitions, we add :: to call external functions
    rather than recursing into the struct's own member. *)
let needs_global_qualifier (ctx : render_ctx) x =
  match ctx.rc_scope with
  | Some scope ->
    (not (Cpp_name.is_qualified (global_name ctx Term x)))
    && not (mp_encloses (modpath_of_r x) scope.Scope_plan.module_)
  | None -> false

(* ============================================================================
   Cache-backed name resolution helpers
   ============================================================================
   These query the pre-computed Name_resolution cache for classification
   information (eponymous, enum, record, merged status). The actual display name
   rendering is still done by the original functions (inductive_type_name,
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
let struct_spelling ~merged ~promoted ~local id =
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
let struct_declaration_name ~merged ~promoted ~local id =
  match struct_spelling ~merged ~promoted ~local id with
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

(** {2 What a declaration not yet printed names} *)

let module_written (c : render_ctx) =
  match c.rc_module with
  | Some mp -> mp
  | None -> CErrors.anomaly (Pp.str "Crane: templates were read off something written as no module's element.")

let functor_concept_scope mp =
  List.find_map (fun (m, scope) -> if ModPath.equal m mp then Some scope else None) !functor_concept_scopes

let concept_extra_args kn =
  match kn with
  | ModPath.MPdot (mp0, _) -> ( match functor_concept_scope mp0 with Some (_, params) -> params | None -> [])
  | _ -> []

let modtype_concept_name mp =
  let base = Structure_analysis.concept_name_of_label in
  match mp with
  | ModPath.MPdot (mp0, l) -> (
    match functor_concept_scope mp0 with
    | Some (fl, _) -> base fl ^ "_" ^ base l
    | None -> Option.default (base l) (Module_plan.modtype_concept_name mp) )
  | MPfile _ | MPbound _ -> CErrors.anomaly (Pp.str "modtype_concept_name: a module type is a member of a structure")

let modtype_concept_ref ctx kn =
  match kn with
  | ModPath.MPdot (mp0, _) when Option.has_some (functor_concept_scope mp0) ->
    (* Declared at file scope, so named after the functor declaring it. *)
    Cpp_name.unqualified (modtype_concept_name kn)
  | MPdot (mp0, _) when Common.get_force_cross_file_qualification () ->
    (* A top-level module type of another file is a concept in a namespace
       of the same name, which from outside the namespace names the
       namespace: [C::C].  The file is the one holding the module whose
       element is being written, which the plan says, not the visibility in
       effect. *)
    let resolved = Common.resolve_module kn in
    let rec file_of = function
      | ModPath.MPfile _ as mp -> mp
      | MPdot (mp, _) -> file_of mp
      | MPbound _ -> mp0
    in
    let foreign_file =
      match mp0 with MPfile _ -> not (ModPath.equal mp0 (file_of (module_written ctx))) | _ -> false
    in
    if foreign_file && not (Cpp_name.is_qualified resolved) then
      Cpp_name.inside resolved (fun s -> Cpp_name.Namespace s) (Cpp_name.unqualified (modtype_concept_name kn))
    else resolved
  | MPdot _ ->
    (* Monolithic extraction: resolving the module records the file it names;
       the short label is the concept's name everywhere in the one file. *)
    ignore (Common.resolve_module kn);
    Cpp_name.unqualified (modtype_concept_name kn)
  | MPfile _ | MPbound _ -> Common.resolve_module kn

let struct_definition_name ctx id =
  let local = local_at ctx id and merged = merged_at ctx and promoted = promoted_at ctx in
  match struct_spelling ~merged ~promoted ~local id with
  | As_declared -> Cpp_name.unqualified (declared_name Type id)
  | Eponymous_record_name | Capitalized -> Cpp_name.unqualified (struct_declaration_name ~merged ~promoted ~local id)

let enum_definition_name ctx r =
  match r with GlobRef.IndRef _ -> inductive_type_name ctx r | _ -> global_name ctx Type r

(* The visibility inside the struct of the inductive [r]: a layer whose path
   names nothing a reference could be declared in, holding the
   constructors' struct names. *)
let inductive_struct_visibility r =
  match r with
  | GlobRef.IndRef ((kn, i) as ind) ->
    let ctors =
      List.init (Option.default 0 (Table.get_ind_nb_ctors_opt kn i)) (fun j ->
          Ml_type_util.ctor_struct_id_of_ref (GlobRef.ConstructRef (ind, j + 1)) )
    in
    let scope =
      Label.make (Printf.sprintf "%sstruct_%s_%d" Common.crane_local_prefix (Label.to_string (MutInd.label kn)) i)
    in
    let mp = ModPath.MPdot (top_visible_mp (), scope) in
    inside ~members:(Id.Set.of_list ctors) mp [] (current_visibility ())
  | _ -> current_visibility ()

let next (entered : Cpp_resolution.entered) (c : render_ctx) =
  let c =
    match entered with
    | Signature _ | Inductive_struct _ -> c
    | In_struct -> {c with rc_in_struct = true}
    | In_template -> {c with rc_in_template = true}
    | Function {owner; defines} ->
      {c with rc_scope = (if defines && not c.rc_in_struct then Scope_plan.of_declaration owner else None)}
  in
  {c with rc_frame = entered :: c.rc_frame}

(* The position is installed for the printers not yet given it, and the
   visibility for the names still resolved where the printer is: the
   resolver's replay, and the check against it. *)
let enter_from c (entered : Cpp_resolution.entered) k =
  let c' = next entered c in
  with_render_ctx (fun _ -> c') @@ fun () ->
  match entered with
  | Signature {signature; parameters} -> with_visibility (inside signature parameters (current_visibility ())) (fun () -> k c')
  | Inductive_struct r -> with_visibility (inductive_struct_visibility r) (fun () -> k c')
  | In_struct | In_template | Function _ -> k c'

let rec entering_from c l k = match l with [] -> k c | entered :: rest -> enter_from c entered (fun c' -> entering_from c' rest k)
let enter entered k = enter_from !render_ctx entered (fun _ -> k ())
let entering l k = entering_from !render_ctx l (fun _ -> k ())

let rec at_frame (frame : Cpp_resolution.frame) k =
  match frame with [] -> k () | entered :: outer -> at_frame outer (fun () -> enter entered k)

(* The name the inductive type [x] is written under as a value: the
   struct a constructor's value is built through. *)
let inductive_value_name ctx x =
  let ns_name, needs_ns = inductive_name ctx x in
  let type_name = global_name ctx Type x in
  let force = Common.get_force_cross_file_qualification () in
  (* Check eponymous record FIRST because they can also be local *)
  if is_eponymous_record_cached x then Cpp_name.unqualified (Common.pp_type_name_capitalized x)
  else if promoted_at ctx x then
    dedup_tail (if force then capitalize_base type_name else capitalize_initial type_name)
  else if Cpp_name.is_qualified type_name then
    let cap = if force then capitalize_base type_name else type_name in
    if merged_at ctx x then
      let allow_bare =
        let ref_base = base_mp (modpath_of_r x) in
        List.exists (ModPath.equal ref_base) (visible_mps (current_visibility ()))
      in
      dedup_tail ~allow_bare cap
    else cap
  else if needs_ns then
    if merged_at ctx x then
      (* Merged non-local inductive: use capitalized name directly *)
      List.fold_right Cpp_name.within (global_scopes_for x ns_name) ns_name
    else (* Unmerged non-local inductive: Wrapper::inner *)
      Cpp_name.inside ns_name (fun s -> Cpp_name.Class s) type_name
  else if force then capitalize_initial type_name
  else (* Local inductive: use original name directly *)
    type_name

let inductive_value ctx x = named ctx (Inductive_value x) (fun () -> inductive_value_name ctx x)

let live_name (key : Cpp_resolution.key) =
  with_render_ctx (fun c -> {c with rc_names = None}) @@ fun () ->
  (* The replay's position, which whoever resolves the key installs. *)
  let ctx = !render_ctx in
  match key with
  | Module mp -> Common.resolve_module mp
  | Module_declared mp -> Cpp_name.unqualified (module_declared_name mp)
  | Global (k, r) -> global_name ctx k r
  | Unmapped (k, r) -> Common.global_name k r
  | Inductive_value r -> inductive_value_name ctx r
  | Short (k, r) -> Cpp_name.unqualified (Common.pp_global_name k r)
  | Class_concept r -> concept_name ctx r
  | Modtype_concept mp -> modtype_concept_ref ctx mp
  | Modtype_concept_declared mp -> Cpp_name.unqualified (modtype_concept_name mp)
  | Definition (Enum_definition, r) -> enum_definition_name ctx r
  | Definition (Struct_definition, r) -> struct_definition_name ctx r
  | Definition (Alias_definition, r) -> global_name ctx Type r
