(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** {2 Conversion functions from Miniml to Minicpp types} *)

(** MiniML to MiniCpp translation: converts ML-style AST to C++-oriented AST. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Str
open Util
(* Re-export the shared translation state so it is available unqualified here
   and still reachable as [Translation.<accessor>] by external callers (via
   translation.mli). *)
include Translation_state
include Ml_type_util


(** Compute the factory method name for a constructor.
    Factory names are the lowercase of the constructor struct name
    (e.g. [Cons] -> ["cons"]). If the lowercased name collides with a C++
    keyword, a generated name ([v], [v_mut], [clone], [variant_t]), or the
    enclosing type's own name (which C++ treats as a constructor declaration),
    the original PascalCase is kept with a trailing underscore
    (e.g. [Char] -> ["Char_"]).

    @param type_name  the enclosing inductive type's C++ name, for same-name
                      collision detection (default [""]) *)
let factory_name_of_ctor ?(type_name = "") ctor_struct_name =
  let lc = String.lowercase_ascii ctor_struct_name in
  let reserved_generated_names =
    [ "v"; "v_"; "v_mut"; "clone"; "variant_t" ]
  in
  let collides =
    Id.Set.mem (Id.of_string lc) (get_keywords ())
    || lc = String.lowercase_ascii type_name
    || List.mem lc reserved_generated_names
  in
  if collides then ctor_struct_name ^ "_"
  else lc

(** {2 Named Constructor Fields}

    Constructor struct fields in C++ are named using Rocq binder names when
    available.  For example, [Node (left : tree) (v : A) (right : tree)]
    generates fields [d_left], [d_v], [d_right] instead of [d_a0], [d_a1],
    [d_a2].

    The pipeline:
    + Extraction ({!Extraction.extract_really_ind}) populates
      {!Miniml.ml_ind_packet.ip_consarg_names} from the kernel binder names.
    + {!compute_and_register_field_names} transforms each binder into a
      C++-safe identifier and registers the mapping in
      {!Common.ctor_field_names}.
    + Access sites ({!gen_match_branch}, record reuse, {!Loopify.patch_cell_field})
      call {!Common.lookup_ctor_field_name} to resolve field names. *)

(** Sanitize a Rocq binder name for use as a C++ struct field identifier.
    Lowercases the name, strips trailing primes ([a'] -> [a], [x''] -> [x]),
    and replaces non-alphanumeric characters (except [_]) with underscores.
    Returns [None] if the result is empty or starts with a digit, in which
    case the caller falls back to the generic positional name [d_aJ].

    @param name  the raw Rocq binder name (e.g. ["left"], ["a'"], ["1st"]) *)
let sanitize_binder_name name =
  let lc = String.lowercase_ascii name in
  let len = String.length lc in
  (* Strip trailing primes: [a'''] → [a] *)
  let rec strip_end i =
    if i <= 0 then 0
    else if lc.[i - 1] = '\'' then strip_end (i - 1)
    else i
  in
  let end_pos = strip_end len in
  if end_pos = 0 then None
  else
    let s = String.sub lc 0 end_pos in
    (* Replace non-C++ chars with underscores *)
    let buf = Buffer.create (String.length s) in
    String.iter
      (fun c ->
        if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_' then
          Buffer.add_char buf c
        else
          Buffer.add_char buf '_' )
      s;
    let result = Buffer.contents buf in
    if String.length result = 0 || (result.[0] >= '0' && result.[0] <= '9') then
      None
    else
      Some result

(** Derive the C++ field name string for constructor argument [k].
    Returns ["d_<sanitized_name>"] when a valid binder name exists and does
    not collide with a C++ keyword, or the positional name ["d_a<k>"]
    otherwise.

    @param consarg_names  binder names from {!Miniml.ml_ind_packet.ip_consarg_names}
    @param k              0-based field index *)
let field_name_str_of_idx consarg_names k =
  match List.nth_opt consarg_names k with
  | Some (Some id) -> (
    match sanitize_binder_name (Id.to_string id) with
    | Some sanitized ->
      if Id.Set.mem (Id.of_string sanitized) (get_keywords ()) then
        field_param_name k
      else
        if Table.std_lib () = "BDE" then "d_" ^ sanitized else sanitized
    | None -> field_param_name k )
  | _ -> field_param_name k

(** Compute and register the C++ field name for constructor field [j].
    Registers two entries:
    - [ctor_field_names]: the pretty field name (used for struct declarations
      and member access), derived from [field_consarg_names] which may include
      names supplied by [Arguments_renaming].
    - [ctor_bind_names]: the base name for structured-binding variables in
      pattern matches, derived from [bind_consarg_names] (kernel-only).  When
      the kernel binder is anonymous ([None]) the indexed fallback [a0]/[a1]/...
      is used unconditionally to prevent variable-shadowing in nested matches.

    @param ctor_struct_name   PascalCase name of the constructor struct
    @param field_consarg_names  field declaration names (kernel + Arguments override)
    @param bind_consarg_names   binding variable names (kernel only)
    @param _n_fields            total field count (unused but kept for symmetry)
    @param j                    0-based field index *)
let compute_field_name ctor_struct_name field_consarg_names bind_consarg_names
    _n_fields j =
  let base_str = field_name_str_of_idx field_consarg_names j in
  let has_dup =
    let rec check k =
      if k >= j then false
      else if String.equal (field_name_str_of_idx field_consarg_names k) base_str
      then true
      else check (k + 1)
    in
    check 0
  in
  let field_str =
    if has_dup then base_str ^ "_" ^ string_of_int j else base_str
  in
  let field_id = Id.of_string field_str in
  register_ctor_field_name ctor_struct_name j field_id;
  (* Binding variable name: use indexed fallback for anonymous kernel binders
     to prevent shadowing when nested matches on the same type reuse [a0]/[l0]. *)
  let bind_id =
    match List.nth_opt bind_consarg_names j with
    | Some (Some _) -> field_id  (* kernel-named: same as field for readability *)
    | _ -> field_param_id j      (* anonymous kernel binder: safe indexed fallback *)
  in
  register_ctor_bind_name ctor_struct_name j bind_id;
  field_id

(** Compute and register field names for all [n_fields] fields of a
    constructor struct.  [field_consarg_names] supplies the pretty names used
    for struct field declarations (may include [Arguments_renaming] overrides);
    [bind_consarg_names] supplies the kernel-only names used for structured-
    binding variable generation. *)
let compute_and_register_field_names ctor_struct_name field_consarg_names
    bind_consarg_names n_fields =
  List.init n_fields (fun j ->
    compute_field_name ctor_struct_name field_consarg_names bind_consarg_names
      n_fields j)

(** Augment [kernel_arg_names] with names from an [Arguments] declaration.
    Where [kernel_arg_names] has [None] (anonymous binder), the corresponding
    entry from [Arguments_renaming.arguments_names] is used if present and
    non-anonymous.  Kernel-named entries ([Some _]) are never overridden.
    Returns [kernel_arg_names] unchanged if [Arguments_renaming] has no entry
    for [cref] or if all kernel binders are already named. *)
let augment_with_args_renaming cref kernel_arg_names =
  if List.for_all (fun n -> n <> None) kernel_arg_names then
    kernel_arg_names
  else
    try
      let n_params =
        match cref with
        | GlobRef.ConstructRef ((kn, _), _) ->
          (try (Global.lookup_mind kn).mind_nparams
           with _ -> 0)
        | _ -> 0
      in
      let all_override = Arguments_renaming.arguments_names cref in
      let override = List.skipn n_params all_override in
      List.map2
        (fun kern over ->
          match kern with
          | Some _ -> kern
          | None ->
            (match over with
             | Names.Name id -> Some id
             | Names.Anonymous -> None))
        kernel_arg_names override
    with Not_found | Invalid_argument _ -> kernel_arg_names

(** Like [List.firstn] but returns [min(n, length lst)] elements instead of
    raising when [n > length lst]. Needed because extraction sometimes produces
    type argument lists shorter than expected (due to [Tdummy Ktype] erasure,
    higher-kinded extraction failures, or universe polymorphism).

    @param n    number of elements to take (must be >= 0)
    @param lst  input list
    @return prefix of [lst] with length [min(n, length lst)] *)
let safe_firstn n lst =
  let rec aux n lst acc =
    match n, lst with
    | 0, _ | _, [] -> List.rev acc
    | n, hd::tl -> aux (n-1) tl (hd::acc)
  in
  aux n lst []

(* The shared mutable translation state ([tctx], [local_inductives], and their
   accessors) lives in {!Translation_state}, opened at the top of this file. *)

(** Extract the innermost result type from a (possibly monadic) ML type.
    For [nat -> itree ioE unit], returns [unit].
    For [nat -> unit], returns [unit].
    For [itree ioE unit] (zero-arg monadic), returns [unit].
    The result type is always the LAST type argument of the monad
    (monads parameterize on the result type as their last type param). *)
let ml_result_type ty =
  let cod = ml_codomain ty in
  match cod with
  | Miniml.Tglob (r, args, _) when Table.is_monad r ->
    (match List.rev args with r :: _ -> r | [] -> cod)
  | _ -> cod

(** Check if a monad reference uses the reified ITree extraction mode
    (i.e. its monad template string contains ["ITree"]). *)
let is_monad_reified monad_ref =
  match Table.get_monad_template_opt monad_ref with
  | Some t ->
    ( try ignore (Str.search_forward (Str.regexp_string "ITree") t 0); true
      with Not_found -> false )
  | None -> false

(** If the codomain of [ty] is a registered monad, return its reference. *)
let extract_monad_from_codomain ty =
  match ml_codomain ty with
  | Miniml.Tglob (monad_ref, _, _) when Table.is_monad monad_ref ->
    Some monad_ref
  | _ -> None

(** Collect [Id.t]s for typeclass-typed parameters in an ML arrow type. *)
let collect_typeclass_param_ids ty =
  let rec aux acc i = function
    | Miniml.Tarr (t1, t2) ->
      if Table.is_typeclass_type t1 then
        aux (tc_instance_id i :: acc) (i + 1) t2
      else
        aux acc i t2
    | _ -> List.rev acc
  in
  match ty with Miniml.Tarr _ -> aux [] 0 ty | _ -> []

(** Apply unit-to-void conversion on a C++ type, respecting reified mode.
    In reified mode, [Unit] inside [ITree<Unit>] becomes [ITree<void>].
    In sequential mode, the entire type becomes [Tvoid]. *)
let apply_unit_void unit_void is_reified ty =
  if unit_void then
    if is_reified then voidify_unit_in_type ty
    else Tvoid
  else ty

(** Generate the C++ expression for Rocq's [tt] (the unit constructor).
    Does NOT call [gen_expr] — it checks the extraction table directly. *)
let mk_tt_expr () =
  match Table.resolve_tt_ctor () with
  | Some tt_ref when Table.is_custom tt_ref ->
    mk_cppglob tt_ref []
  | Some tt_ref ->
    let ind_ref, ctor_name =
      match tt_ref with
      | GlobRef.ConstructRef ((kn, i), cidx) ->
        ( GlobRef.IndRef (kn, i),
          Id.of_string (Table.enum_ctor_name_of_ref kn i cidx) )
      | _ ->
        CErrors.anomaly (Pp.str "mk_tt_expr: tt is not a ConstructRef")
    in
    CPPenum_val (ind_ref, ctor_name)
  | None ->
    CErrors.anomaly (Pp.str "mk_tt_expr: could not resolve core.unit.tt")

(** Check whether a global reference [r] has been void-ified: its ML type
    is a function (or monad) whose result type is [unit].  When such a
    function is called in expression context, the C++ call returns [void]
    and cannot be used as a value — we must wrap it in an IIFE that
    executes the call for side effects and returns [std::monostate{}]. *)
let is_void_ified_ref (r : GlobRef.t) : bool =
  match find_type_opt r with
  | Some ty ->
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty)
  | None -> false

(** Wrap a void-returning function call expression in an IIFE so it can
    be used in value context.  Produces:
      [&]() { void_call(); return std::monostate{}; }()
    The call is executed for side effects; the IIFE returns the unit value. *)
let wrap_void_call_as_value (call_expr : cpp_expr) : cpp_expr =
  CPPfun_call (
    CPPlambda ([], None,
      [Sexpr call_expr; Sreturn (Some (mk_tt_expr ()))],
      false),
    [])

(** Check whether an ML function expression [f] in [MLapp(f, args)] would
    produce a void-returning call in C++.  Handles:
    - [MLglob(r, _)]  — named function, look up type in extraction table
    - [MLrel(i)]       — variable (e.g. callback), look up type in env
    - [MLmagic(inner)] — transparent wrapper, recurse *)
let rec ml_callee_is_void = function
  | MLglob (r, _) -> is_void_ified_ref r
  | MLmagic inner -> ml_callee_is_void inner
  | MLrel i ->
    ( try
        let ty = get_env_type i in
        (match ty with Miniml.Tarr _ -> true
         | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
        && ml_type_is_unit (ml_result_type ty)
      with _ -> false )
  | _ -> false

(** {3 Reified ITree helpers}

    In reified mode, [itree E R] extracts to [std::shared_ptr<ITree<R>>]
    instead of being erased to [R].  The helpers below build C++ AST nodes
    for ITree types and constructors, and detect whether an ML expression
    already carries a reified tree value. *)

(** Extract the result type [R] from a monadic ML type [itree E R].
    Returns the second non-erased type argument, or [Miniml.Tunknown] if
    the type does not have the expected shape. *)
let extract_itree_result_ml (ml_ty : ml_type) : ml_type =
  match resolve_tmeta ml_ty with
  | Miniml.Tglob (_, _ :: r :: _, _) -> r
  | _ -> Miniml.Tunknown

(** Build the C++ type [std::shared_ptr<ITree<r_cpp>>]. *)
let mk_itree_type (r_cpp : cpp_type) : cpp_type =
  Tshared_ptr (Tid_external (Id.of_string "ITree", [r_cpp]))

(** Map well-known identifier names to their C++ equivalents.
    Returns [None] for ordinary (non-special) identifiers. *)
let resolve_special_id s =
  if String.equal s "int0" then Some "int64_t"
  else if String.equal s "string" then Some "std::string"
  else if String.equal s "dummy_type"
       || String.equal s "dummy_prop"
       || String.equal s "dummy_implicit"
  then Some "std::any"
  else None

(** Resolve a [VarRef] identifier to its C++ type name.
    Extends {!resolve_special_id} with additional known aliases
    like [prod] → [std::pair], [option] → [std::optional]. *)
let resolve_varref_id s =
  match resolve_special_id s with
  | Some r -> r
  | None ->
    if String.equal s "prod" || String.equal s "Prod" then "std::pair"
    else if String.equal s "option" || String.equal s "Option" then
      "std::optional"
    else if String.equal s "list" then "List"
    else s

(** Resolve an [IndRef] to its base C++ type name.  When the reference is
    in [raw_inductives], returns the raw Coq name; otherwise computes the
    C++ struct name with standard mappings (e.g. [prod] → [std::pair]).
    [~with_option] controls whether [option] maps to [std::optional] (only
    meaningful for zero-argument occurrences). *)
let resolve_indref_base ?(no_custom_inductives = Refset'.empty)
    ~raw_inductives ~with_option r =
  if Refset'.mem r raw_inductives then
    Common.pp_global_name Type r
  else
    let base = Common.pp_global_name Type r in
    let cap = Common.capitalize_last_component base in
    let parent_is_cap =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Names.MutInd.modpath kn with
        | Names.ModPath.MPdot (_, label) ->
          String.equal cap (Names.Label.to_string label)
        | _ -> false )
      | _ -> false
    in
    let skip_custom = Refset'.mem r no_custom_inductives in
    if (not skip_custom) && String.equal base "prod" then "std::pair"
    else if (not skip_custom) && with_option
         && (String.equal base "option" || String.equal base "Option")
    then "std::optional"
    else if parent_is_cap || String.equal base "nat" then cap
    else if
      List.exists
        (globref_equal r)
        (get_local_inductives ())
    then
      if Common.get_force_qualified_capitalization ()
      then String.capitalize_ascii (Common.pp_global_name Type r)
      else Common.pp_global Type r
    else cap

(** Render a C++ type as a plain string.  Used in [ITree<R>] qualified
    expressions, [clone_as_value<T>] template arguments, and anywhere a
    type must be serialised to a raw string.  Handles common built-in
    types; falls back to ["auto"] for unknown shapes. *)
let rec render_cpp_type_simple ?(raw_inductives = Refset'.empty)
    ?(no_custom_inductives = Refset'.empty) ty =
  let render = render_cpp_type_simple ~raw_inductives ~no_custom_inductives in
  let with_args base ts =
    match ts with [] -> base | _ ->
    base ^ "<" ^ String.concat ", " (List.map render ts) ^ ">"
  in
  match ty with
  | Tid (id, ts) ->
    let s = Id.to_string id in
    let base = match resolve_special_id s with Some r -> r | None -> s in
    with_args base ts
  | Tglob (r, ts, _) ->
    let base =
      match Table.find_custom_opt r with
      | Some s
        when (not (Refset'.mem r no_custom_inductives))
             && Table.to_inline r && not (String.contains s '%') ->
        s
      | _ ->
      match r with
      | GlobRef.IndRef _ ->
        resolve_indref_base ~no_custom_inductives ~raw_inductives
          ~with_option:true r
      | GlobRef.VarRef id -> resolve_varref_id (Id.to_string id)
      | _ -> Common.pp_global_name Type r
    in
    with_args base ts
  | Tid_external (id, ts) -> with_args (Id.to_string id) ts
  | Tnamespace (g, t) ->
    (* For local inductives whose names are eponymous with their parent module,
       no qualification is needed.  For others, prepend the capitalized parent
       module name (e.g., "NestedTree::tree").  We cannot use pp_global_name
       here because it gives the raw Coq name ("list" → "list") instead of
       the C++ struct name ("List"). *)
    if Table.is_enum_inductive g then
      let base = Common.pp_global_name Type g in
      let enum_name = Common.capitalize_last_component base in
      if
        List.exists
          (globref_equal g)
          (get_local_inductives ())
      then enum_name
      else (
        match g with
        | GlobRef.IndRef (kn, _) ->
          ( match Names.MutInd.modpath kn with
          | Names.ModPath.MPdot (_, label) ->
            Names.Label.to_string label ^ "::" ^ enum_name
          | _ -> enum_name )
        | _ -> enum_name )
    else if not (get_record_fields g == []) then render t
    else
    let inner = render t in
    let inner_base =
      match String.index_opt inner '<' with
      | Some i -> String.sub inner 0 i
      | None -> inner
    in
    let parent_ns =
      match g with
      | GlobRef.IndRef (kn, _) ->
        ( match Names.MutInd.modpath kn with
        | Names.ModPath.MPdot (_, label) ->
          let parent = Names.Label.to_string label in
          (* Strip template args before comparing: "List<t_A>" → "List" *)
          let cap_inner = Common.capitalize_last_component inner_base in
          (* Eponymous shortcut: parent "List" = inner "List" → no prefix.
             For MPdot types (inner module blocks), stripping the prefix avoids
             the incorrect `Trie::Trie<T>` form from inside the module.  Note
             that the MPdot branch cannot produce a fully qualified external
             path anyway (it only sees the last label), so this shortcut is
             the safest option for inner-module types. *)
          if String.equal parent cap_inner then ""
          else parent ^ "::"
        | Names.ModPath.MPfile f ->
          (* Top-level inductive in a .v file (e.g. list in Datatypes.v).
             In separate extraction, external inductives need their parent
             namespace as prefix (e.g. "Datatypes::").  In monolithic
             extraction, everything is in the same file so no prefix is
             needed — matching the old behaviour of the catch-all [_ -> ""]
             branch. *)
          if List.exists
               (globref_equal g)
               (get_local_inductives ())
          then ""
          else if not (Common.get_force_qualified_capitalization ())
          then ""
          else
            let parent =
              String.capitalize_ascii
                (Id.to_string (List.hd (Names.DirPath.repr f)))
            in
            (* Always emit the file-namespace prefix, even if the inductive
               name matches the file name (e.g. String::String).  The eponymous
               shortcut is wrong here: `String` alone resolves to the C++
               namespace, not to the type, so callers outside that namespace
               always need the `String::String` qualified form. *)
            parent ^ "::"
        | _ -> "" )
      | _ -> ""
    in
    parent_ns ^ inner
  | Tmod (TMconst, t) -> "const " ^ render t
  | Tmod (_, t) -> render t
  | Tref t -> render t ^ "&"
  | Tptr t -> render t ^ "*"
  | Tvar (_, Some n) ->
    let s = Id.to_string n in
    ( match resolve_special_id s with Some r -> r | None -> s )
  | Tqualified (base, id) ->
    "typename " ^ render base ^ "::" ^ Id.to_string id
  | Tshared_ptr t -> "std::shared_ptr<" ^ render t ^ ">"
  | Tvoid -> "void"
  | _ -> "auto"

(** Recursively wrap [Tglob] inductive references with [Tnamespace] so that
    [render_cpp_type_simple] produces fully-qualified names.  The [~skip]
    predicate controls which references are left unwrapped: [qualify_inductives]
    wraps all inductives, while [qualify_inductives ~skip:(Refset'.mem g set)]
    leaves members of [set] bare.  Used when the rendered type will appear in
    a context where inductives may not be in scope (e.g. [clone_as_value]
    template arguments in standalone free functions). *)
let rec qualify_inductives ?(skip = fun _ -> false) = function
  | Tglob (g, ts, es) ->
    let core = Tglob (g, List.map (qualify_inductives ~skip) ts, es) in
    ( match g with
    | GlobRef.IndRef _ when skip g -> core
    | GlobRef.IndRef _ when Table.is_inline_custom g -> core
    | GlobRef.IndRef _ -> Tnamespace (g, core)
    | _ -> core )
  | Tnamespace (g, t) ->
    (* qualify_inductives may add Tnamespace to a Tglob(g,...) inside t;
       avoid double-wrapping when the inner result already carries the
       same Tnamespace. *)
    let inner = qualify_inductives ~skip t in
    ( match inner with
    | Tnamespace (g2, _) when GlobRef.CanOrd.equal g g2 -> inner
    | _ -> Tnamespace (g, inner) )
  | Tshared_ptr t -> Tshared_ptr (qualify_inductives ~skip t)
  | Tref t -> Tref (qualify_inductives ~skip t)
  | Tmod (m, t) -> Tmod (m, qualify_inductives ~skip t)
  | Tptr t -> Tptr (qualify_inductives ~skip t)
  | Tfun (args, ret) ->
    Tfun (List.map (qualify_inductives ~skip) args,
          qualify_inductives ~skip ret)
  | Tid (id, ts) -> Tid (id, List.map (qualify_inductives ~skip) ts)
  | Tid_external (id, ts) ->
    Tid_external (id, List.map (qualify_inductives ~skip) ts)
  | Tqualified (base, id) ->
    Tqualified (qualify_inductives ~skip base, id)
  | t -> t

(** Render a C++ type as a string suitable for use in raw C++ template
    arguments, applying post-hoc fixups for names that
    {!render_cpp_type_simple} emits in Coq form rather than C++ form
    (e.g. [int0] → [int64_t], [Uint64_t] → [Uint0]). *)
let render_cpp_type_for_raw_template ?(raw_inductives = Refset'.empty)
    ?(no_custom_inductives = Refset'.empty) ty =
  Str.global_replace
    (Str.regexp "\\<string\\>")
    "std::string"
    (Str.global_replace
       (Str.regexp_string "Uint64_t")
       "Uint0"
       (Str.global_replace
          (Str.regexp_string "int0")
          "int64_t"
          (render_cpp_type_simple ~raw_inductives ~no_custom_inductives ty)))

let build_guard_compare_stmts n ids =
  match Table.find_guard_compare n with
  | None -> []
  | Some ctor_ref ->
    let strip_wrappers t =
      let rec go = function
        | Tref t | Tmod (_, t) | Tnamespace (_, t) -> go t
        | t -> t
      in
      go t
    in
    let rec find_pair = function
      | (id1, ty1) :: rest ->
        let base1 = strip_wrappers ty1 in
        ( match
            List.find_opt
              (fun (_, ty2) -> cpp_ty_eq base1 (strip_wrappers ty2))
              rest
          with
        | Some (id2, _) -> Some (id1, id2)
        | None -> find_pair rest )
      | [] -> None
    in
    ( match find_pair ids with
    | Some (p1, p2) ->
      let ctor_expr =
        match ctor_ref with
        | GlobRef.ConstructRef ((kn, i), cidx)
          when Table.is_enum_inductive (GlobRef.IndRef (kn, i)) ->
          let ctor_name = Id.of_string (Table.enum_ctor_name_of_ref kn i cidx) in
          CPPenum_val (GlobRef.IndRef (kn, i), ctor_name)
        | _ -> mk_cppglob ctor_ref []
      in
      [ Sif_then
          ( CPPbinop ("==", CPPunop ("&", CPPvar p1), CPPunop ("&", CPPvar p2)),
            [Sreturn (Some ctor_expr)] ) ]
    | None -> [] )

(** Post-processing pass: insert [std::move] for state-threading pattern.

    When a fixpoint's return type is [pair<S,R>] and it has a value parameter
    of type [S], each recursive call copies the whole state value.  This pass:
    1. Removes [const] from the state param (allows move-from at call sites).
    2. Wraps the state argument with [std::move] in every recursive self-call.
    3. Wraps the state component with [std::move] in every [make_pair] call
       that is in a terminal position (direct state var or state alias from
       a pair-match scrutinee).

    This reduces O(N) copies per recursion level to O(1) moves, making deep
    state-threaded recursions O(L) instead of O(L*N) total. *)
let rewrite_state_threading_moves
    (fn_ref : GlobRef.t) (state_id : Id.t) (s_ty : cpp_type)
    (ids : (Id.t * cpp_type) list) (body : cpp_stmt list) =
  let strip_const = function Tmod (TMconst, t) -> t | t -> t in
  (* Remove const from state param in the parameter list. *)
  let new_ids =
    List.map
      (fun (id, ty) ->
        if Id.equal id state_id then (id, strip_const ty) else (id, ty))
      ids
  in
  (* Check if a C++ type is pair<S, ?> where first component matches s_ty. *)
  let is_state_pair_type ty =
    match strip_const ty with
    | Tglob (g, t1 :: _, _) when is_prod_global g ->
      cpp_ty_eq (strip_const t1) (strip_const s_ty)
    | _ -> false
  in
  (* Check if a function expression is an inline [make_pair] custom. *)
  let is_make_pair_fn fn =
    match fn with
    | CPPglob (_, _, Some ci) -> (
      match ci.ci_inline with
      | Some s -> Common.contains_substring s "make_pair"
      | None -> false )
    | _ -> false
  in
  (* [subst] maps state-alias variable IDs to their source pair var + field.
     [subst id = Some (scrut_id, first_id)] means [id] is bound to
     [scrut_id.first] and can be replaced with [std::move(scrut_id.first)].
     [direct_owned] tracks variables that already OWN the state value via a
     move binding (from scrut_is_owned_pair in gen_custom_cpp_case).  These are
     moved directly ([std::move(id)]) rather than indirectly via scrut.first. *)
  let direct_owned = ref Id.Set.empty in
  let is_state_val e subst =
    match e with
    | CPPvar id ->
      Id.equal id state_id
      || Id.Set.mem id !direct_owned
      || subst id <> None
    | _ -> false
  in
  let wrap_state e subst =
    match e with
    | CPPvar id when Id.equal id state_id || Id.Set.mem id !direct_owned ->
      CPPmove (CPPvar id)
    | CPPvar id -> (
      match subst id with
      | Some (scrut_id, first_id) ->
        CPPmove (CPPmember (CPPvar scrut_id, first_id))
      | None -> e )
    | _ -> e
  in
  (* Count the number of times state_id (or an alias in subst) appears in an
     expression.  Used to guard std::move: we only move if the state appears
     exactly once in the whole make_pair call, so we don't invalidate a second
     use of the same value (e.g. dup_a x = (x, x)). *)
  let rec count_state_uses subst e =
    match e with
    | CPPvar id when Id.equal id state_id || Id.Set.mem id !direct_owned -> 1
    | CPPvar id when subst id <> None -> 1
    | CPPmove inner -> count_state_uses subst inner
    | _ ->
      fold_expr_children
        (fun acc child -> acc + count_state_uses subst child)
        0 e
  in
  let rec rewrite_expr subst e =
    match e with
    | CPPfun_call (CPPglob (g, tys, ci) as fn, args)
      when GlobRef.CanOrd.equal g fn_ref ->
      (* Self-recursive call: move state_id (or its aliases) wherever they
         appear within the argument expressions, including nested positions
         like cons(x, acc) where acc is threaded as part of the new state. *)
      let rec move_states e =
        match e with
        | CPPmove _ -> e  (* already moved, avoid double-wrap *)
        | CPPvar id when Id.equal id state_id || Id.Set.mem id !direct_owned ->
          CPPmove (CPPvar id)
        | CPPvar id when subst id <> None -> wrap_state (CPPvar id) subst
        | _ -> map_expr move_states (rewrite_stmt subst) Fun.id e
      in
      CPPfun_call (fn, List.map move_states args)
    | CPPfun_call (fn, [r_arg; s_arg]) when is_make_pair_fn fn ->
      (* [make_pair(s, r)] with args reversed: [r_arg; s_arg].
         [s_arg] is [%a0] = the first (state) component.
         Only move the state if it appears exactly once in the whole call
         (i.e. not also in r_arg), to avoid use-after-move bugs like
         dup_a x = (x, x) → make_pair(std::move(x), x). *)
      let total_uses = count_state_uses subst r_arg + count_state_uses subst s_arg in
      let s_arg' =
        if is_state_val s_arg subst && total_uses = 1 then wrap_state s_arg subst
        else rewrite_expr subst s_arg
      in
      CPPfun_call (fn, [rewrite_expr subst r_arg; s_arg'])
    | _ -> map_expr (rewrite_expr subst) (rewrite_stmt subst) Fun.id e
  and rewrite_stmt subst s =
    match s with
    | Scustom_case (ty, CPPvar scrut_id, tyargs, branches, tmpl) when is_state_pair_type ty ->
      (* Pair pattern match: the first bound var is the state alias.
         Two cases depending on whether the template uses move bindings:
         - const-ref binding (original): alias_id = scrut.first; track as
           indirect alias so make_pair uses std::move(scrut.first).
         - move binding (scrut_is_owned_pair): alias_id owns the value via
           std::move(scrut.first); track as a direct owned var so make_pair
           uses std::move(alias_id), avoiding a second move from scrut.first. *)
      let is_move_binding = Common.contains_substring tmpl "std::move" in
      let new_branches =
        List.map
          (fun (params, ret_ty, body_stmts) ->
            match params with
            | (alias_id, _) :: _ ->
              if is_move_binding then begin
                direct_owned := Id.Set.add alias_id !direct_owned;
                let body = List.map (rewrite_stmt subst) body_stmts in
                direct_owned := Id.Set.remove alias_id !direct_owned;
                (params, ret_ty, body)
              end else begin
                let first_id = Id.of_string "first" in
                let new_subst id =
                  if Id.equal id alias_id then Some (scrut_id, first_id)
                  else subst id
                in
                (params, ret_ty, List.map (rewrite_stmt new_subst) body_stmts)
              end
            | [] ->
              (params, ret_ty, List.map (rewrite_stmt subst) body_stmts))
          branches
      in
      Scustom_case (ty, CPPvar scrut_id, tyargs, new_branches, tmpl)
    | _ -> map_stmt (rewrite_expr subst) (rewrite_stmt subst) Fun.id s
  in
  let new_body = List.map (rewrite_stmt (fun _ -> None)) body in
  (new_ids, new_body)

(** Render a simple C++ expression to a string for use in raw C++ fragments.
    Returns [None] for compound expressions that cannot be reduced to a
    simple identifier or dereference chain. *)
let rec render_cpp_expr_simple = function
  | CPPvar id -> Some (Id.to_string id)
  | CPPthis -> Some "this"
  | CPPderef e ->
    Option.map (fun s -> "(*" ^ s ^ ")") (render_cpp_expr_simple e)
  | CPPget (e, field) ->
    Option.map (fun s -> s ^ "." ^ Id.to_string field)
      (render_cpp_expr_simple e)
  | CPPget' (e, field_ref) ->
    Option.map (fun s -> s ^ "." ^ Common.pp_global_name Type field_ref)
      (render_cpp_expr_simple e)
  | CPPmember (e, field) ->
    Option.map (fun s -> s ^ "." ^ Id.to_string field)
      (render_cpp_expr_simple e)
  | CPPdot_method_call (e, method_id, []) ->
    Option.map (fun s -> s ^ "." ^ Id.to_string method_id ^ "()")
      (render_cpp_expr_simple e)
  | CPParrow (e, field) ->
    Option.map (fun s -> s ^ "->" ^ Id.to_string field)
      (render_cpp_expr_simple e)
  | CPPmethod_call (e, method_id, []) ->
    Option.map (fun s -> s ^ "->" ^ Id.to_string method_id ^ "()")
      (render_cpp_expr_simple e)
  | CPPnullptr -> Some "nullptr"
  | CPPraw s -> Some s
  | _ -> None

(** Substitute placeholders in a Crane template string.
    Recognises: [%scrut], [%t{i}], [%b{i}a{j}], [%br{i}], [%a{i}].
    [scrut]: replacement for [%scrut].
    [types]: indexed list for [%t0], [%t1], …
    [bindings]: 2-D array; [bindings.(i).(j)] replaces [%b{i}a{j}].
    [branches]: indexed list for [%br0], [%br1], …
    [args]: indexed list for [%a0], [%a1], … *)
let subst_template tmpl ~scrut ~types ~bindings ~branches ~args =
  let buf = Buffer.create (String.length tmpl * 2) in
  let n = String.length tmpl in
  let i = ref 0 in
  let read_int_at s start =
    let j = ref start in
    while !j < String.length s && s.[!j] >= '0' && s.[!j] <= '9' do incr j done;
    if !j = start then None
    else Some (int_of_string (String.sub s start (!j - start)), !j)
  in
  while !i < n do
    if tmpl.[!i] = '%' && !i + 1 < n then begin
      let rest_start = !i + 1 in
      let rest = String.sub tmpl rest_start (n - rest_start) in
      let matched = ref false in
      if not !matched && String.length rest >= 5 && String.sub rest 0 5 = "scrut" then begin
        Buffer.add_string buf scrut;
        i := rest_start + 5; matched := true
      end;
      if not !matched && rest.[0] = 'b' && String.length rest > 1 then begin
        match read_int_at rest 1 with
        | Some (bi, k) when k < String.length rest && rest.[k] = 'a' ->
          (match read_int_at rest (k + 1) with
           | Some (ai, k2) ->
             (try Buffer.add_string buf bindings.(bi).(ai);
                  i := rest_start + k2; matched := true
              with Invalid_argument _ -> ())
           | None -> ())
        | _ -> ()
      end;
      if not !matched && String.length rest >= 2 && rest.[0] = 'b' && rest.[1] = 'r' then begin
        match read_int_at rest 2 with
        | Some (idx, k) ->
          (try Buffer.add_string buf (List.nth branches idx);
               i := rest_start + k; matched := true
           with Failure _ -> ())
        | None -> ()
      end;
      if not !matched && rest.[0] = 't' then begin
        match read_int_at rest 1 with
        | Some (idx, k) ->
          (try Buffer.add_string buf (List.nth types idx);
               i := rest_start + k; matched := true
           with Failure _ -> ())
        | None -> ()
      end;
      if not !matched && rest.[0] = 'a' then begin
        match read_int_at rest 1 with
        | Some (idx, k) ->
          (try Buffer.add_string buf (List.nth args idx);
               i := rest_start + k; matched := true
           with Failure _ -> ())
        | None -> ()
      end;
      if not !matched then begin Buffer.add_char buf '%'; incr i end
    end else begin
      Buffer.add_char buf tmpl.[!i]; incr i
    end
  done;
  Buffer.contents buf

(** Generate an inline C++ expression that converts [expr] from [src_ty] to
    [dst_ty].  Used at every boundary between the storage representation
    (where recursive fields are [shared_ptr]-wrapped) and the API
    representation (where they are bare values).

    Conversion cases:
    - [shared_ptr<S> -> shared_ptr<T>]: null-check, dereference, make_shared
    - [shared_ptr<T> -> T]: dereference (converting ctor if inner ≠ dst)
    - [T -> shared_ptr<T>]: wrap in make_shared
    - [C<shared_ptr<T>,...> -> C<T,...>]: non-recursive custom type, template-derived
    - [Tglob(g, ts1) -> Tglob(g, ts2)]: same container, different elements
    - Everything else (type variables, scalars): converting constructor

    Uses [render_cpp_type_for_raw_template] to produce type strings for
    [CPPraw]-based converting constructors, since [pp_cpp_type] renders
    custom-extracted types with different namespace qualification.

    @param skip    predicate for GlobRefs to skip during qualification
    @param src_ty  the source C++ type
    @param dst_ty  the destination C++ type
    @param expr    the C++ expression to convert
    @return a [cpp_expr] that produces a value of type [dst_ty] *)

(** Replace all occurrences of ["return "] with ["var_name = "] in a raw C++
    body string.  Safe because the only ["return "] substrings in
    template-expanded match bodies come from our own branch generation
    (["return " ^ ctor_s ^ ";"]) — no string literals or nested lambdas. *)
let replace_return_with_assign s var_name =
  let ret = "return " in
  let rlen = String.length ret in
  let repl = var_name ^ " = " in
  let buf = Buffer.create (String.length s) in
  let n = String.length s in
  let rec go i =
    if i >= n then ()
    else if i + rlen <= n && String.sub s i rlen = ret then begin
      Buffer.add_string buf repl;
      go (i + rlen)
    end else begin
      Buffer.add_char buf s.[i];
      go (i + 1)
    end
  in
  go 0;
  Buffer.contents buf

(** When [expr] is a single-argument IIFE
    [CPPfun_call(CPPlambda([(ty, id)], ret, body, false), [arg])], lift the
    lambda body into assignment statements targeting [target_var]:
    {[
      Type target_var{};
      const auto& param = arg;
      <body with "return X;" rewritten to "target_var = X;">
    ]}
    Returns [Some stmts] on success, [None] if [expr] is not a liftable IIFE.
    When [target_ty = Ttodo], the lambda's return type is used instead. *)
let lift_iife_assignment target_var target_ty expr =
  match expr with
  | CPPfun_call (
      CPPlambda ([(param_ty, Some param_id)], Some ret_ty, body, false),
      [arg]) ->
    let actual_ty = match target_ty with Ttodo -> ret_ty | t -> t in
    let tv_s = Id.to_string target_var in
    let lifted_body = List.map (function
      | Sreturn (Some e) -> Sasgn (target_var, None, e)
      | Sraw s -> Sraw (replace_return_with_assign s tv_s)
      | s -> s
    ) body in
    Some (Sdecl_init (target_var, actual_ty)
          :: Sasgn (param_id, Some param_ty, arg)
          :: lifted_body)
  | _ -> None

(** For inductives with dependent parameters (e.g. [sigT]), unresolved
    meta-type variables ([Tvar']) correspond to fields whose C++ type
    collapses to [std::any].  Retyping them as [Tdummy Ktype] marks them
    as erased, triggering [any_cast<T>] wrapping when returned as a
    template parameter. *)
let retype_dependent_params (typ : ml_type) ids =
  let is_dep_ind = match typ with
    | Tglob (GlobRef.IndRef _ as g, _, _) -> Table.has_dependent_params g
    | _ -> false
  in
  if is_dep_ind then
    List.map (fun (n, ml_ty) ->
      match ml_ty with Tvar' _ -> (n, Tdummy Ktype) | _ -> (n, ml_ty)) ids
  else ids

let rec gen_type_conversion_expr ?(skip = fun _ -> false) ~src_ty ~dst_ty expr =
  let render ty =
    render_cpp_type_for_raw_template (qualify_inductives ~skip ty)
  in
  (* Strip a single [Tnamespace] wrapper when it matches the inner [Tglob].
     [convert_ml_type_to_cpp_type] wraps external inductives as
     [Tnamespace(g, Tglob(g,...))] for qualified rendering, but for pattern
     matching we want the bare [Tglob(g,...)] form. *)
  let strip_ns = function
    | Tnamespace (g, (Tglob (g2, _, _) as core)) when GlobRef.CanOrd.equal g g2 -> core
    | t -> t
  in
  (* Save the original dst_ty (with its Tnamespace wrapper, if any) before
     stripping.  The stripped form is used for structural comparison; the
     original is used for rendering converting constructors via
     CPPconverting_ctor, which uses pp_cpp_type and correctly emits namespace
     qualification and typename keywords. *)
  let orig_dst_ty = dst_ty in
  let src_ty = strip_ns src_ty and dst_ty = strip_ns dst_ty in
  (* String-level type conversion for template substitution contexts.
     Fast-paths the common Tshared_ptr wrap/unwrap cases, and falls back to
     gen_type_conversion_expr for complex conversions (rendering the result
     to a string, or returning the original binding if unrenderable). *)
  let convert_arg_str binding src_inner dst_inner =
    if src_inner = dst_inner then binding
    else
      let src_s = strip_ns src_inner and dst_s = strip_ns dst_inner in
      match (src_s, dst_s) with
      | _, Tshared_ptr inner ->
        (* T → shared_ptr<T>: wrap with make_shared *)
        require_header "memory";
        "std::make_shared<" ^ render inner ^ ">(" ^ binding ^ ")"
      | Tshared_ptr _, _ ->
        (* shared_ptr<T> → T: dereference *)
        "(*" ^ binding ^ ")"
      | _ ->
        (* Fallback: use recursive gen_type_conversion_expr and try to render *)
        let conv = gen_type_conversion_expr ~skip
          ~src_ty:src_inner ~dst_ty:dst_inner (CPPraw binding) in
        (match render_cpp_expr_simple conv with
         | Some s -> s
         | None -> binding)
  in
  (* Apply a Table.accessor to a C++ expression, producing a field
     access (CPPmember) or pointer dereference (CPPderef). *)
  let apply_accessor acc e =
    match (acc : Table.accessor) with
    | AccMember f -> CPPmember (e, Id.of_string f)
    | AccDeref -> CPPderef e
  in
  (* Generate a conversion expression for a non-recursive custom type whose
     source and destination differ only in type arguments (e.g.
     optional<shared_ptr<T>> → optional<T>).  Uses the type's registered
     Crane Extract Inductive match and constructor templates.

     For single-constructor types with recognized accessors (e.g. pair), the
     conversion is inlined as a pure expression.  For multi-constructor types
     (e.g. option), the template-expanded body is wrapped in an IIFE with the
     scrutinee bound as a lambda parameter. *)
  let gen_custom_type_conversion g src_ts dst_ts orig_dst_ty' inner_expr =
    (* The guard in gen_type_conversion_expr guarantees g is an IndRef. *)
    let ip = match g with GlobRef.IndRef ip -> ip
      | _ -> CErrors.anomaly (Pp.str "gen_custom_type_conversion: expected IndRef") in
    match Table.find_custom_match_by_ref g with
    | None ->
      CPPconverting_ctor (orig_dst_ty', [inner_expr])
    | Some match_tmpl ->
      let ctor_tmpls = Table.find_custom_ctor_templates ip in
      let src_type_strs = List.map render src_ts in
      let dst_type_strs = List.map render dst_ts in
      let n_branches = List.length ctor_tmpls in
      let n_args = List.length src_ts in
      List.iter require_header (Table.get_ref_import_list g);
      let try_inline () =
        match Table.find_custom_accessors g with
        | Some accs when List.length accs = n_args ->
          let proj_exprs = List.map (fun acc ->
            apply_accessor acc inner_expr
          ) accs in
          let conv_exprs = List.mapi (fun j proj ->
            gen_type_conversion_expr ~skip
              ~src_ty:(List.nth src_ts j) ~dst_ty:(List.nth dst_ts j) proj
          ) proj_exprs in
          let arg_strs = List.map render_cpp_expr_simple conv_exprs in
          if List.for_all (fun x -> x <> None) arg_strs then
            let arg_strs = List.filter_map Fun.id arg_strs in
            let result = subst_template (List.hd ctor_tmpls)
              ~scrut:"" ~types:dst_type_strs ~bindings:[||] ~branches:[]
              ~args:arg_strs in
            Some (CPPraw result)
          else None
        | _ -> None
      in
      match try_inline () with
      | Some e -> e
      | None ->
        let bindings = Array.init n_branches (fun i ->
          Array.init n_args (fun j -> Printf.sprintf "_cv%d_%d" i j)
        ) in
        let branches = List.mapi (fun i ctor_tmpl ->
          let arg_strs = List.mapi (fun j _ ->
            convert_arg_str bindings.(i).(j)
              (List.nth src_ts j) (List.nth dst_ts j)
          ) dst_ts in
          let ctor_s = subst_template ctor_tmpl
            ~scrut:"" ~types:dst_type_strs ~bindings:[||] ~branches:[]
            ~args:arg_strs in
          "return " ^ ctor_s ^ ";"
        ) ctor_tmpls in
        let scrut_id = Id.of_string "__cv" in
        let body = subst_template match_tmpl
          ~scrut:(Id.to_string scrut_id) ~types:src_type_strs
          ~bindings:bindings ~branches:branches ~args:[] in
        CPPfun_call (
          CPPlambda (
            [(Tmod (TMconst, Tref Tauto), Some scrut_id)],
            Some (qualify_inductives ~skip orig_dst_ty'),
            [Sraw body],
            false),
          [inner_expr])
  in
  (* Helper: build a [CPPraw] using a string renderer, falling back to an
     IIFE lambda wrapper when [expr] cannot be rendered to a simple string.
     [lambda_ty] is the C++ return type for the wrapper. [make_body s] is
     called with either the rendered [expr] string or ["__x"] (the lambda
     param name). *)
  let with_expr_s ~lambda_ty ~make_body =
    match render_cpp_expr_simple expr with
    | Some s -> CPPraw (make_body s)
    | None ->
      let body = make_body "__x" in
      CPPfun_call
        ( CPPraw
            ("[](auto&& __x) -> " ^ lambda_ty ^ " { return " ^ body ^ "; }"),
          [expr] )
  in
  if src_ty = dst_ty then expr
  else
    (* ---- Different types: dispatch on wrapper structure ---- *)
    match (src_ty, dst_ty) with
    | Tshared_ptr _src_inner, Tshared_ptr dst_inner ->
      (* shared_ptr<S> → shared_ptr<T>: null-check + dereference inner *)
      require_header "memory";
      let dst_inner_s = render dst_inner in
      let ty_s = render dst_ty in
      with_expr_s ~lambda_ty:ty_s
        ~make_body:(fun s ->
          s ^ " ? std::make_shared<" ^ dst_inner_s ^ ">(*" ^ s ^ ") : nullptr")
    | Tshared_ptr inner, _ ->
      (* shared_ptr<T> → T: dereference.  Also strip Tnamespace from inner
         before comparing to dst_ty: strip_ns was applied to dst_ty at the
         top of this function but not to inner (which sits one level deeper
         inside Tshared_ptr).  Without stripping inner, a
         [Tnamespace(list, Tglob(list,...))] inner would wrongly appear
         different from the stripped [Tglob(list,...)] dst_ty and generate a
         spurious converting constructor with an unqualified type name. *)
      let inner = strip_ns inner in
      let derefed = CPPderef expr in
      if inner = dst_ty then derefed
      else CPPconverting_ctor (orig_dst_ty, [derefed])
    | _, Tshared_ptr inner ->
      CPPfun_call (CPPmk_shared inner, [expr])
    | Tglob (g1, src_ts, _), Tglob (g2, dst_ts, _)
      when GlobRef.CanOrd.equal g1 g2
           && Table.is_custom g1
           && not (Table.has_recursive_fields g1)
           && src_ts <> dst_ts
           (* Only use template-derived conversion when at least one type arg
              pair differs in shared_ptr wrapping.  Pure Tvar→Tvar differences
              (e.g. in template converting constructors) are handled by the
              simpler CPPconverting_ctor fallback below. *)
           && List.exists2 (fun s d -> s <> d
                && (match s with Tshared_ptr _ -> true | _ ->
                    match d with Tshared_ptr _ -> true | _ -> false))
                src_ts dst_ts ->
      gen_custom_type_conversion g1 src_ts dst_ts orig_dst_ty expr
    | Tglob (g1, _src_ts, _), Tglob (g2, _dst_ts, _)
      when GlobRef.CanOrd.equal g1 g2 && _src_ts <> _dst_ts
           && not (Table.is_inline_custom g1) ->
      (* Same Crane container, different element types → converting ctor *)
      CPPconverting_ctor (orig_dst_ty, [expr])
    | Tvar (_, Some _), Tvar (_, Some _) ->
      (* Type-variable-to-type-variable conversion in converting constructors.
         When the source type variable is std::any at runtime (e.g. List<_U>
         constructed from List<std::any> in grammar action wrappers), a plain
         converting constructor A(field) fails to compile because pair<K,V>
         has no constructor from std::any.  Dispatch at compile time instead.

         When A is a pair type, grammar actions may store elements as
         pair<any,any> (all fields erased) even when A = pair<K,V> with
         concrete K and V.  This happens because nt_semty erases all
         nonterminal semantic types to __ in ML extraction.  Handle this by
         attempting a direct any_cast<A> first (succeeds when stored as
         pair<K,V>), and falling back to a two-level cast from pair<any,any>
         when A has first_type/second_type members (i.e. A is a std::pair). *)
      require_header "any";
      let u_s = render src_ty in
      let a_s = render dst_ty in
      (match render_cpp_expr_simple expr with
      | Some field_s ->
        (* Generate an IIFE that handles three cases:
           1. Direct any_cast when the stored type matches A exactly.
           2. Two-level cast for pair<any,any> sources when A is a std::pair:
              each pair field is cast individually, skipping the cast when the
              target field type is std::any (since _k/_v are already std::any
              and any_cast<std::any>(x) is not an identity — it looks for a
              stored std::any inside x, which fails at runtime).
           3. Fallthrough any_cast for non-pair types. *)
        CPPraw ("[&]() -> " ^ a_s ^ " { if constexpr (std::is_same_v<" ^ u_s
               ^ ", std::any>) { if (" ^ field_s ^ ".type() == typeid(" ^ a_s
               ^ ")) return std::any_cast<" ^ a_s ^ ">(" ^ field_s
               ^ "); if constexpr (requires { typename " ^ a_s
               ^ "::first_type; typename " ^ a_s ^ "::second_type; }) { const auto& "
               ^ "[_k, _v] = std::any_cast<std::pair<std::any, std::any>>("
               ^ field_s ^ "); return " ^ a_s ^ "{ [&]() -> typename " ^ a_s
               ^ "::first_type { if constexpr (std::is_same_v<typename " ^ a_s
               ^ "::first_type, std::any>) return _k; else return "
               ^ "std::any_cast<typename " ^ a_s ^ "::first_type>(_k); }(), "
               ^ "[&]() -> typename " ^ a_s ^ "::second_type { if constexpr "
               ^ "(std::is_same_v<typename " ^ a_s ^ "::second_type, std::any>"
               ^ ") return _v; else return std::any_cast<typename " ^ a_s
               ^ "::second_type>(_v); }() }; } return std::any_cast<" ^ a_s
               ^ ">(" ^ field_s ^ "); } else return " ^ a_s ^ "(" ^ field_s
               ^ "); }()")
      | None ->
        CPPconverting_ctor (orig_dst_ty, [expr]))
    | (_, dst) when (let strip_ns = function Tnamespace (_, t) -> t | t -> t in
                     match strip_ns dst with
                     | Tglob (g, [elem_ty], _) ->
                       is_list_global g && Table.is_custom g
                       && elem_ty <> Tany && elem_ty <> Tauto
                     | _ -> false) ->
      let strip_ns = function Tnamespace (_, t) -> t | t -> t in
      (match strip_ns dst with
       | Tglob (g, [_], _) ->
         (match src_ty with
           | Tany -> CPPany_cast (Tglob (g, [Tany], []), expr)
           | _ -> expr)
       | _ -> expr)
    | _ ->
      (* Type variables or fully concrete different types: converting
         constructor.  Type variables are always bare (never shared_ptr)
         because nested self-references are wrapped at the field level. *)
      CPPconverting_ctor (orig_dst_ty, [expr])

(** Build a [CPPfun_call] for [ITree<R>::ret(...)].
    When [r_cpp] is [Tvoid], generates [ITree<void>::ret()]. *)
let mk_itree_ret (r_cpp : cpp_type) (args : cpp_expr list) : cpp_expr =
  let itree_ty = Tid_external (Id.of_string_soft "ITree", [r_cpp]) in
  CPPfun_call (CPPqualified_t (itree_ty, Id.of_string "ret"), args)

(** Build [ITree<R>::ret(v)] or [ITree<void>::ret()] depending on whether
    the result type is void.  [r_cpp] is the C++ result type; [r_ml] is
    the ML result type (checked with {!ml_type_is_void} for unit-mapped
    types); [v] is the value expression to wrap. *)
let mk_itree_ret_for_value r_cpp r_ml v =
  if r_cpp = Tvoid || ml_type_is_unit_or_void r_ml then
    mk_itree_ret Tvoid []
  else
    mk_itree_ret r_cpp [v]

(** Reify a monadic parameter type for ITree extraction.

    In reified mode, the C++ type for a monadic parameter [itree E R] after
    monad erasure is just [R].  This function wraps it back into
    [shared_ptr<ITree<R>>] so the tree can be passed as a first-class value.
    Does nothing in sequential mode or when [ml_ty] is not monadic. *)
let reify_monadic_param_type ml_ty cpp_ty =
  if is_monadic_ml_type ml_ty && tctx.itree_mode = Reified then begin
    Table.require_itree_header ();
    let r_ty =
      match cpp_ty with
      | Tglob (_, _ :: r :: _, _) -> r
      | t -> t
    in
    (* Voidify unit result type inside ITree params *)
    let r_ty = if is_cpp_unit_type r_ty then Tvoid else r_ty in
    mk_itree_type r_ty
  end
  else cpp_ty

(** Check whether an ML expression is a de Bruijn reference to a variable
    whose [env_type] is monadic.  Such variables have been reified to
    [shared_ptr<ITree<R>>] and need [->run()] to extract the value. *)
let is_reified_monadic_var ml_expr =
  match ml_expr with
  | MLrel i ->
    (match get_env_type_opt i with Some ty -> is_monadic_ml_type ty | None -> false)
  | _ -> false

(** Check whether an ML expression already produces a reified monadic value
    (a [shared_ptr<ITree<R>>]).  Extends {!is_reified_monadic_var} to also
    cover [MLapp(MLrel f, args)] where [f] is a local function whose return
    type is monadic.  Such calls already return a tree, so wrapping in
    [ITree::ret()] would incorrectly double-wrap.

    Does {b not} return [true] for [MLapp(MLglob g, args)] because global
    inline extractions (e.g. [print_endline]) may produce direct C++
    expressions that genuinely need Ret wrapping. *)
let is_reified_monadic_expr ml_expr =
  match ml_expr with
  | MLrel i ->
    (match get_env_type_opt i with Some ty -> is_monadic_ml_type ty | None -> false)
  | MLapp (MLrel i, _) ->
    (match get_env_type_opt i with Some ty -> is_monadic_ml_type (ml_codomain ty) | None -> false)
  | _ -> false

(** If [ml_expr] refers to a reified monadic variable, wrap [cpp_expr] in
    a [->run()] call to execute the tree and produce the direct value.
    Otherwise returns [cpp_expr] unchanged. *)
let deref_reified ml_expr cpp_expr =
  if is_reified_monadic_var ml_expr then
    CPPmethod_call (cpp_expr, Id.of_string "run", [])
  else
    cpp_expr

(** Convert returned lambdas to capture by value. Lambdas returned from
    functions outlive the function's stack frame, so capturing by reference
    ([&]) would create dangling references. This rewrites
    [Sreturn (Some (CPPlambda (_, _, _, false)))] to capture by value ([true]).
*)
let return_captures_by_value stmts =
  let rec expr = function
    | CPPlambda (args, ret, body, false) ->
      CPPlambda (args, ret, List.map stmt body, true)
    | CPPlambda (args, ret, body, true) ->
      CPPlambda (args, ret, List.map stmt body, true)
    | CPPfun_call (f, args) -> CPPfun_call (expr f, List.map expr args)
    | CPPderef e -> CPPderef (expr e)
    | CPPmove e -> CPPmove (expr e)
    | CPPforward (ty, e) -> CPPforward (ty, expr e)
    | CPPoverloaded es -> CPPoverloaded (List.map expr es)
    | CPPstruct (id, tys, es) -> CPPstruct (id, tys, List.map expr es)
    | CPPstruct_id (id, tys, es) -> CPPstruct_id (id, tys, List.map expr es)
    | CPPstructmk (id, tys, es) -> CPPstructmk (id, tys, List.map expr es)
    | CPPshared_ptr_ctor (ty, e) -> CPPshared_ptr_ctor (ty, expr e)
    | CPPbinop (op, a, b) -> CPPbinop (op, expr a, expr b)
    | CPPunop (op, e) -> CPPunop (op, expr e)
    | CPPmember (e, id) -> CPPmember (expr e, id)
    | CPPqualified (e, id) -> CPPqualified (expr e, id)
    | CPPget (e, id) -> CPPget (expr e, id)
    | CPPget' (e, id) -> CPPget' (expr e, id)
    | CPPmethod_call (e, id, args) ->
      CPPmethod_call (expr e, id, List.map expr args)
    | CPPany_cast (ty, e) -> CPPany_cast (ty, expr e)
    | e -> e
  and stmt = function
    | Sreturn (Some e) -> Sreturn (Some (expr e))
    | Sexpr e -> Sexpr (expr e)
    | Sasgn (_, _, _) as s -> s
    | Sderef_asgn (_, _) as s -> s
    | Sif (c, t, f) -> Sif (expr c, List.map stmt t, List.map stmt f)
    | Sswitch (scrut, ind, branches, default) ->
      Sswitch
        ( expr scrut,
          ind,
          List.map (fun (id, body) -> (id, List.map stmt body)) branches,
          Option.map (List.map stmt) default )
    | Smatch (branches, default) ->
      Smatch
        ( List.map
            (fun br ->
              { br with
                smb_scrutinee = expr br.smb_scrutinee;
                smb_body = List.map stmt br.smb_body })
            branches,
          Option.map (List.map stmt) default )
    | Scustom_case (ty, e, tys, branches, err) ->
      Scustom_case
        ( ty,
          expr e,
          tys,
          List.map
            (fun (ids, ctor, body) -> (ids, ctor, List.map stmt body))
            branches,
          err )
    | s -> s
  in
  List.map
    (fun s ->
      match s with
      | Sreturn (Some (CPPlambda (args, ret, body, false))) ->
        Sreturn (Some (CPPlambda (args, ret, body, true)))
      | Sreturn (Some e) -> Sreturn (Some (expr e))
      | s -> s )
    stmts

(** Run escape analysis on [body], saving and restoring the analysis state
    around the call to [f]. This is needed because escape analysis runs at
    multiple nesting levels (lambdas, let-in expressions, top-level functions)
    and each level has its own set of safe bindings. *)
let with_escape_analysis body f =
  let saved_depth = tctx.current_letin_depth in
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let saved_match_counter = tctx.match_param_counter in
  let saved_cs_counter = tctx.cs_counter in
  let saved_return_type = tctx.current_cpp_return_type in
  tctx.current_letin_depth <- 0;
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_owned_vars <- Escape.IntSet.empty;
  tctx.move_n_params <- 0;
  tctx.match_param_counter <- 0;
  tctx.cs_counter <- 0;
  (* Prevent void optimization from leaking into IIFE/lambda bodies: when the
     outer function returns void, gen_stmts generates bare 'return;' for tt,
     but IIFE bodies return their own type (e.g. monostate), not void. *)
  ( if tctx.current_cpp_return_type = Some Tvoid then
      tctx.current_cpp_return_type <- None );
  let result = f () in
  tctx.current_letin_depth <- saved_depth;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  tctx.match_param_counter <- saved_match_counter;
  tctx.cs_counter <- saved_cs_counter;
  tctx.current_cpp_return_type <- saved_return_type;
  result

(** Save move-tracking state, shift de Bruijn indices by [n] binders, run [f],
    then restore the original state.  This is the standard bracket for code
    that introduces [n] pattern variables or let bindings.

    {b Why shift.}  [move_owned_vars] and [move_dead_after] track variables by
    de Bruijn index.  When entering a scope with [n] new binders, all existing
    indices must be shifted up by [n] so they continue to refer to the same
    outer variables.

    @param clear_dead  If [true], empty [move_dead_after] instead of shifting.
      Used inside match branches, which are independent scopes: the outer
      dead-after set must not leak in, because a variable dead after one branch
      may still be live in another.
    @param add_owned  Optional de Bruijn index to add to the owned set after
      shifting.  Used for monadic bind continuation parameters that receive an
      owned [shared_ptr] value (e.g. [>>=] callback arguments).
    @param exclude_owned  Optional de Bruijn index to REMOVE from the owned set
      after shifting.  Used for match scrutinees: after shifting by [n], the
      scrutinee's outer index [db] becomes [db + n].  Excluding it prevents
      [std::move(scrutinee)] from being emitted inside the branch while
      pattern-variable structured bindings ([const auto& [d_a0, d_a1] = ...])
      still hold const references into it — which would cause use-after-move. *)
let with_shifted_move_tracking n ?(clear_dead = false) ?add_owned
    ?(add_owned_set = Escape.IntSet.empty) ?exclude_owned f =
  let saved_owned = tctx.move_owned_vars in
  let saved_dead = tctx.move_dead_after in
  tctx.move_owned_vars <-
    Escape.IntSet.map (fun i -> i + n) tctx.move_owned_vars;
  ( match add_owned with
  | Some idx -> tctx.move_owned_vars <- Escape.IntSet.add idx tctx.move_owned_vars
  | None -> () );
  tctx.move_owned_vars <-
    Escape.IntSet.union tctx.move_owned_vars add_owned_set;
  ( match exclude_owned with
  | Some idx -> tctx.move_owned_vars <- Escape.IntSet.remove idx tctx.move_owned_vars
  | None -> () );
  tctx.move_dead_after <-
    ( if clear_dead then Escape.IntSet.empty
      else Escape.IntSet.map (fun i -> i + n) tctx.move_dead_after );
  let result = f () in
  tctx.move_owned_vars <- saved_owned;
  tctx.move_dead_after <- saved_dead;
  result

(* ============================================================================
   Shared helpers for method generation (used by gen_ind_header_v2 and
   gen_record_methods)
   ============================================================================ *)

(** Re-export [IntSet] from [Escape] for local use in type variable collection. *)
module IntSet = Escape.IntSet

(** Collect all Tvar indices from an ml_type. Used to find type variables beyond
    those of the containing inductive/record. *)
let rec collect_tvars_set acc = function
  | Miniml.Tvar i | Miniml.Tvar' i -> IntSet.add i acc
  | Miniml.Tarr (t1, t2) -> collect_tvars_set (collect_tvars_set acc t1) t2
  | Miniml.Tglob (_, args, _) -> List.fold_left collect_tvars_set acc args
  | Miniml.Tmeta {contents = Some t} -> collect_tvars_set acc t
  | _ -> acc

(** Convert an IntSet of type variable indices back to a list, wrapping
    [collect_tvars_set]. Used to collect all Tvar indices from an ml_type. *)
let collect_tvars acc ty =
  IntSet.elements (collect_tvars_set (IntSet.of_list acc) ty)

(** Collect all Tvar indices from an ML AST, using collect_tvars on embedded
    types. Used to find all type variables referenced in a function body. *)
let rec collect_tvars_ast acc = function
  | MLlam (_, ty, body) -> collect_tvars_ast (collect_tvars acc ty) body
  | MLletin (_, ty, a, b) ->
    collect_tvars_ast (collect_tvars_ast (collect_tvars acc ty) a) b
  | MLglob (_, tys) -> List.fold_left collect_tvars acc tys
  | MLcons (ty, _, args) ->
    List.fold_left collect_tvars_ast (collect_tvars acc ty) args
  | MLcase (ty, e, brs) ->
    let acc = collect_tvars_ast (collect_tvars acc ty) e in
    Array.fold_left
      (fun acc (ids, ty, _, body) ->
        let acc =
          List.fold_left (fun acc (_, t) -> collect_tvars acc t) acc ids
        in
        collect_tvars_ast (collect_tvars acc ty) body )
      acc
      brs
  | MLfix (_, ids, funs, _) ->
    let acc =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) acc ids
    in
    Array.fold_left collect_tvars_ast acc funs
  | MLapp (f, args) ->
    List.fold_left collect_tvars_ast (collect_tvars_ast acc f) args
  | MLmagic a -> collect_tvars_ast acc a
  | MLparray (arr, def) ->
    collect_tvars_ast (Array.fold_left collect_tvars_ast acc arr) def
  | MLtuple args -> List.fold_left collect_tvars_ast acc args
  | MLrel _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> acc

(** True when evaluating an ML AST may throw through an extracted axiom or
    exception. Functions whose bodies can throw must not be marked
    [__attribute__((pure))]: Clang may otherwise move calls across local
    exception handlers or discard them when their result is unused. *)
let rec ast_may_throw = function
  | MLaxiom _ | MLexn _ -> true
  | MLglob (r, _) -> Table.is_axiom_value r
  | MLlam (_, _, body) -> ast_may_throw body
  | MLletin (_, _, a, b) -> ast_may_throw a || ast_may_throw b
  | MLcons (_, _, args) -> List.exists ast_may_throw args
  | MLcase (_, e, brs) ->
    ast_may_throw e
    || Array.exists (fun (_, _, _, body) -> ast_may_throw body) brs
  | MLfix (_, _, funs, _) -> Array.exists ast_may_throw funs
  | MLapp (f, args) -> ast_may_throw f || List.exists ast_may_throw args
  | MLmagic a -> ast_may_throw a
  | MLparray (arr, def) -> Array.exists ast_may_throw arr || ast_may_throw def
  | MLtuple args -> List.exists ast_may_throw args
  | MLrel _ | MLdummy _ | MLuint _ | MLfloat _ | MLstring _ -> false

(** Build Tvar i -> concrete_type substitution by unifying two ML types
    structurally. Walks both types in parallel; when one side has Tvar i and the
    other has a concrete type, records the mapping. Conflicting mappings are
    discarded. *)
let build_tvar_subst_from_unify ty_with_tvars ty_concrete =
  let seen = Hashtbl.create 8 in
  let rec unify t1 t2 =
    match (t1, t2) with
    | (Miniml.Tvar i | Miniml.Tvar' i), _ when not (has_tvar t2) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t2)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | _, (Miniml.Tvar i | Miniml.Tvar' i) when not (has_tvar t1) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t1)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) ->
      unify a1 a2;
      unify b1 b2
    | Miniml.Tglob (_, args1, _), Miniml.Tglob (_, args2, _)
      when List.length args1 = List.length args2 -> List.iter2 unify args1 args2
    | Miniml.Tmeta {contents = Some t}, other
     |other, Miniml.Tmeta {contents = Some t} -> unify t other
    | _ -> ()
  in
  unify ty_with_tvars ty_concrete;
  Hashtbl.fold
    (fun i v acc ->
      match v with
      | Some ty -> (i, ty) :: acc
      | None -> acc )
    seen
    []

(** Collect all types that should be unified with the top-level function type.
    Returns a list of types to unify pairwise with the top-level type:
    - The arrow type reconstructed from MLlam annotations
    - The type annotation on the MLfix binding (if present)
    - The arrow type from the MLfix's inner function body *)
let collect_body_types_for_unify body =
  let types = ref [] in
  let rec from_lams = function
    | MLlam (_, ty, inner) -> Miniml.Tarr (ty, from_lams inner)
    | MLfix (_, ids, funs, _) ->
      Array.iter (fun (_, ty) -> types := ty :: !types) ids;
      Array.iter (fun f -> types := from_lams f :: !types) funs;
      Miniml.Tunknown
    | _ -> Miniml.Tunknown
  in
  let outer = from_lams body in
  outer :: !types

(** Resolve Tvars in the body by unifying body type annotations with the
    top-level type. Only applied when the top-level type is fully concrete (no
    Tvars, no unresolved metas). Returns the (possibly substituted) body. *)
let resolve_body_tvars b ty =
  let ty = type_simpl ty in
  if has_tvar ty then
    b (* top-level type is polymorphic, don't touch the body *)
  else
    let body_types = collect_body_types_for_unify b in
    let tvar_subst =
      List.concat_map (fun bt -> build_tvar_subst_from_unify bt ty) body_types
    in
    let tvar_subst =
      List.fold_left
        (fun acc (i, t) -> if List.mem_assoc i acc then acc else (i, t) :: acc)
        []
        tvar_subst
    in
    match tvar_subst with
    | [] -> b
    | _ -> map_types_in_ast (subst_tvars_type tvar_subst) b

(** Resolve all unresolved type meta-variables in an [ml_type] to fresh
    [Tvar]s. Each [Tmeta {contents = None}] encountered gets unified (via
    [try_mgu]) with [Tvar idx], where [idx] is drawn from [next_tvar] and
    incremented. Chases [Tmeta {contents = Some t}]. Recurses into [Tarr]
    and [Tglob] args. *)
let rec resolve_type_metas ~next_tvar = function
  | Miniml.Tmeta ({contents = None} as m) ->
    let idx = !next_tvar in
    next_tvar := idx + 1;
    try_mgu (Miniml.Tmeta m) (Miniml.Tvar idx)
  | Miniml.Tmeta {contents = Some t} -> resolve_type_metas ~next_tvar t
  | Miniml.Tarr (t1, t2) ->
    resolve_type_metas ~next_tvar t1;
    resolve_type_metas ~next_tvar t2
  | Miniml.Tglob (_, args, _) -> List.iter (resolve_type_metas ~next_tvar) args
  | _ -> ()

(** Resolve unresolved metas in an ML AST by walking its sub-types.
    resolve_metas should be a function that resolves metas in a single ml_type.
*)
let rec resolve_metas_in_ast resolve_metas = function
  | MLlam (_, ty, body) ->
    resolve_metas ty;
    resolve_metas_in_ast resolve_metas body
  | MLletin (_, ty, a, b) ->
    resolve_metas ty;
    resolve_metas_in_ast resolve_metas a;
    resolve_metas_in_ast resolve_metas b
  | MLglob (_, tys) -> List.iter resolve_metas tys
  | MLcons (ty, _, args) ->
    resolve_metas ty;
    List.iter (resolve_metas_in_ast resolve_metas) args
  | MLcase (ty, e, brs) ->
    resolve_metas ty;
    resolve_metas_in_ast resolve_metas e;
    Array.iter
      (fun (ids, ty, _, body) ->
        List.iter (fun (_, t) -> resolve_metas t) ids;
        resolve_metas ty;
        resolve_metas_in_ast resolve_metas body )
      brs
  | MLfix (_, ids, funs, _) ->
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    Array.iter (resolve_metas_in_ast resolve_metas) funs
  | MLapp (f, args) ->
    resolve_metas_in_ast resolve_metas f;
    List.iter (resolve_metas_in_ast resolve_metas) args
  | MLmagic a -> resolve_metas_in_ast resolve_metas a
  | MLparray (arr, def) ->
    Array.iter (resolve_metas_in_ast resolve_metas) arr;
    resolve_metas_in_ast resolve_metas def
  | MLtuple args -> List.iter (resolve_metas_in_ast resolve_metas) args
  | MLrel _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> ()

(** Substitute [CPPvar target] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion. *)
let rec local_var_subst_expr (target : Id.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPvar id when Id.equal id target -> repl
  | _ ->
    map_expr
      (local_var_subst_expr target repl)
      (local_var_subst_stmt target repl)
      Fun.id
      e

(** Statement-level counterpart of [local_var_subst_expr]: substitute
    [CPPvar target] with [repl] inside a single C++ statement. *)
and local_var_subst_stmt (target : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt
    (local_var_subst_expr target repl)
    (local_var_subst_stmt target repl)
    Fun.id
    s

(** Check whether a variable [target] is referenced in a list of C++ stmts. *)
let stmts_reference_var (target : Id.t) (stmts : cpp_stmt list) : bool =
  let exception Found in
  let rec visit_expr e =
    ( match e with
    | CPPvar id when Id.equal id target -> raise Found
    | _ -> () );
    map_expr visit_expr visit_stmt Fun.id e
  and visit_stmt s =
    map_stmt visit_expr visit_stmt Fun.id s
  in
  try List.iter (fun s -> ignore (visit_stmt s)) stmts; false
  with Found -> true

(** Build type variable names for a list of Tvar indices. Indices within
    [n_outer] reuse names from [outer_tvars]; indices beyond get fresh
    [tvar_id i] names. Converts [outer_tvars] to an array for O(1) lookup. *)
let build_tvar_names ~outer_tvars tvar_indices =
  let n_outer = List.length outer_tvars in
  let outer_arr = Array.of_list outer_tvars in
  List.map
    (fun i ->
      if i <= n_outer then outer_arr.(i - 1) else tvar_id i)
    tvar_indices

(** Build extended tvar names covering both signature and body Tvar indices.
    sig_indices: sorted list of Tvar indices from the function signature
    sig_names: corresponding Id.t names for those indices body_tvars:
    sorted-unique list of all Tvar indices found in the body *)
let build_extended_tvar_names sig_indices sig_names body_tvars =
  let n_sig = List.length sig_indices in
  let sig_set = IntSet.of_list sig_indices in
  let body_extra_tvars =
    List.filter (fun i -> not (IntSet.mem i sig_set)) body_tvars
  in
  let max_tvar = List.fold_left max 0 (sig_indices @ body_tvars) in
  let tvar_name_map =
    List.map2 (fun i name -> (i, name)) sig_indices sig_names
  in
  let tvar_name_map =
    if body_extra_tvars <> [] then
      let min_sig = List.hd sig_indices in
      let min_extra = List.fold_left min max_int body_extra_tvars in
      let offset = min_extra - min_sig in
      List.fold_left
        (fun acc i ->
          let mapped_sig_idx = i - offset in
          if mapped_sig_idx >= 1 && mapped_sig_idx <= n_sig then
            let name = List.assoc mapped_sig_idx tvar_name_map in
            (i, name) :: acc
          else
            (i, tvar_id i) :: acc )
        tvar_name_map
        body_extra_tvars
    else
      tvar_name_map
  in
  if max_tvar > 0 then
    List.init max_tvar (fun i ->
      let idx = i + 1 in
      match List.assoc_opt idx tvar_name_map with
      | Some name -> name
      | None -> anon_tvar_id idx )
  else
    sig_names

(* Walk an ML AST and collect source-order parameter indices that are NOT
   simply forwarded unchanged at recursive call sites.  [is_self_call depth f]
   returns true when the head [f] of an application is a self-recursive
   reference at the given binder depth.

   After collect_lams, param source index [i] has de Bruijn index
   [n_params - i] at depth 0, shifted by [depth] under binders. *)
let detect_non_forwarded_params_generic ~is_self_call n_params body =
  let non_fwd = Hashtbl.create 4 in
  let is_forwarded depth i arg =
    let expected_db = n_params - i + depth in
    match arg with
    | MLmagic (MLrel db) | MLrel db -> db = expected_db
    | _ -> false
  in
  let rec walk depth = function
    | MLapp (f, args) when is_self_call depth f ->
      List.iteri
        (fun i arg ->
          if i < n_params && not (is_forwarded depth i arg) then
            Hashtbl.replace non_fwd i true )
        args
    | MLapp (f, args) ->
      walk depth f;
      List.iter (walk depth) args
    | MLlam (_, _, body) -> walk (depth + 1) body
    | MLletin (_, _, e1, e2) ->
      walk depth e1;
      walk (depth + 1) e2
    | MLcase (_, scrut, branches) ->
      walk depth scrut;
      Array.iter
        (fun (ids, _, _, body) ->
          walk (depth + List.length ids) body )
        branches
    | MLcons (_, _, args) -> List.iter (walk depth) args
    | MLtuple args -> List.iter (walk depth) args
    | MLfix (_, _, bodies, _) ->
      let n = Array.length bodies in
      Array.iter (walk (depth + n)) bodies
    | MLmagic e -> walk depth e
    | MLparray (elts, def) ->
      Array.iter (walk depth) elts;
      walk depth def
    | MLrel _
     |MLglob _
     |MLexn _
     |MLdummy _
     |MLaxiom _
     |MLuint _
     |MLfloat _
     |MLstring _ -> ()
  in
  walk 0 body;
  Hashtbl.fold (fun k _ acc -> k :: acc) non_fwd []

(* Detect non-forwarded params in a local fixpoint body.  Self-references
   use MLrel: after collect_lams strips [n_params] lambda params, the fix
   binding for [fix_idx] in [n_fix] mutual funs is at
   db = [n_params + n_fix - fix_idx], shifted by binder depth. *)
let detect_non_forwarded_params_fix n_params n_fix fix_idx body =
  let base_self_db = n_params + n_fix - fix_idx in
  detect_non_forwarded_params_generic
    ~is_self_call:(fun depth -> function
      | MLrel db -> db = base_self_db + depth
      | _ -> false )
    n_params body

(** Convert ML params to C++ types with const/ref wrapping, and create
    forwarding-ref template parameters for function-typed params. convert_fn:
    function to convert ml_type -> cpp_type (typically
    convert_ml_type_to_cpp_type env tvar_names) Returns
    (cpp_params, all_temps_with_funs). *)
let build_lifted_cpp_params ?(non_fwd_source_indices = []) convert_fn base_temps params =
  let n_total = List.length params in
  (* Non-forwarded check in source order (for fun_tys, which iterates List.rev) *)
  let is_non_fwd_source j = List.mem j non_fwd_source_indices in
  (* Non-forwarded check in de Bruijn order (for cpp_params replacement) *)
  let is_non_fwd_db j = List.mem (n_total - 1 - j) non_fwd_source_indices in
  let cpp_params =
    List.map
      (fun (id, ty) ->
        let cpp_ty = convert_fn ty in
        match cpp_ty with
        | Tshared_ptr _ -> (id, Tref (Tmod (TMconst, cpp_ty)))
        | _ -> (id, Tmod (TMconst, cpp_ty)) )
      params
  in
  let unwrap_fun_ty = function
    | Tmod (TMconst, (Tfun _ as f)) -> Some f
    | Tfun _ as f -> Some f
    | _ -> None
  in
  let fun_tys =
    List.filter_map
      (fun (x, ty, j) ->
        match unwrap_fun_ty ty with
        | Some (Tfun (dom, cod_f)) when not (is_non_fwd_source j) ->
          let cod_f = if is_cpp_unit_type cod_f then Tvoid else cod_f in
          Some (x, TTfun (dom, cod_f), fun_tparam_id j)
        | _ -> None )
      (List.mapi (fun j (x, ty) -> (x, ty, j)) (List.rev cpp_params))
  in
  let n_params = List.length cpp_params in
  let cpp_params =
    List.mapi
      (fun j (x, ty) ->
        match unwrap_fun_ty ty with
        | Some (Tfun _) when not (is_non_fwd_db j) ->
          (x, Tref (Tref (Tvar (0, Some (fun_tparam_id (n_params - j - 1))))))
        | _ -> (x, ty) )
      cpp_params
  in
  let extra_temps = List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let all_temps_with_funs = base_temps @ extra_temps in
  (cpp_params, all_temps_with_funs)

(** Substitute type schema variables [Tvar i] with concrete types.
    [ml_subst_tvars subst ty] replaces [Tvar i] with [subst.(i-1)] when
    the index is in range. Used to instantiate the polymorphic type of a
    global reference with its actual type arguments from [MLglob(r, tys)]. *)
let rec ml_subst_tvars (subst : ml_type array) (ty : ml_type) : ml_type =
  match ty with
  | Tvar i | Tvar' i when i >= 1 && i <= Array.length subst -> subst.(i - 1)
  | Tarr (t1, t2) -> Tarr (ml_subst_tvars subst t1, ml_subst_tvars subst t2)
  | Tglob (g, ts, args) ->
    Tglob (g, List.map (ml_subst_tvars subst) ts, args)
  | Tmeta {contents = Some t} -> ml_subst_tvars subst t
  | _ -> ty

(** Infer the ML type of a body expression from its structure.
    Returns [None] when the type cannot be determined.
    Used to annotate CPPlambda return types so that loopify's frame type
    inference doesn't fall back to [decltype(lambda)]. *)
let rec infer_ml_body_type (a : ml_ast) : ml_type option =
  match a with
  | MLapp (MLglob (r, tys), args) ->
    ( match find_type_opt r with
    | Some ty ->
      (* Instantiate type schema variables with actual type arguments *)
      let ty = match tys with
        | [] -> ty
        | _ -> ml_subst_tvars (Array.of_list tys) ty
      in
      strip_tarr_n (count_real_ml_args args) ty
    | None -> None )
  | MLcons (ty, _, _) -> Some (resolve_tmeta ty)
  | MLcase (_, _, pv) when Array.length pv > 0 ->
    let (_, rty, _, _) = pv.(0) in
    Some (resolve_tmeta rty)
  | MLletin (_, _, _, body) -> infer_ml_body_type body
  | MLlam (_, ty, body) ->
    Option.map (fun rty -> Tarr (ty, rty)) (infer_ml_body_type body)
  | MLglob (r, _) -> find_type_opt r
  | MLmagic e -> infer_ml_body_type e
  | _ -> None

(** Check if a GlobRef returns a typeclass type (possibly through Tarr layers).
*)
let ref_returns_typeclass r =
  match find_type_opt r with
  | Some ty -> Table.is_typeclass_type (ml_return_type ty)
  | None -> false

(** Check if a function returns a skipped type (e.g., ReSum instances whose
    Class is extracted as a ConstRef, not IndRef, and thus not recognized by
    [is_typeclass]). Such arguments are infrastructure that should be erased. *)
let ref_returns_skipped r =
  match find_type_opt r with
  | Some ty ->
    ( match ml_return_type ty with
    | Tglob (rr, _, _) ->
      Table.is_inline_custom rr && Table.find_custom_opt rr = Some ""
    | _ -> false )
  | None -> false

(* Use Common.extract_at_pos for extracting elements at a position *)

(** Create a substitution function for extra type variables in C++ types.
    num_ind_vars: number of type vars from the containing inductive/record
    extra_tvar_map: mapping from Tvar index to Id for extra type vars *)
let make_subst_extra_tvars num_ind_vars extra_tvar_map =
  let rec subst = function
    | Tvar (i, None) when List.mem_assoc i extra_tvar_map ->
      Tvar (0, Some (List.assoc i extra_tvar_map))
    | Tvar (i, None) when i >= 1 && i <= num_ind_vars ->
      (* Inductive's type var - keep as-is for tvar_subst_stmt *)
      Tvar (i, None)
    | Tfun (dom, cod) -> Tfun (List.map subst dom, subst cod)
    | Tshared_ptr t -> Tshared_ptr (subst t)
    | Tglob (r, args, e) -> Tglob (r, List.map subst args, e)
    | Tref t -> Tref (subst t)
    | Tmod (m, t) -> Tmod (m, subst t)
    | Tvariant tys -> Tvariant (List.map subst tys)
    | Tnamespace (r, t) -> Tnamespace (r, subst t)
    | Tqualified (t, id) -> Tqualified (subst t, id)
    | t -> t
  in
  subst

(** Collect de Bruijn indices of free variables in an ML AST. n_bound is the
    number of locally bound variables (lambda params, let bindings, etc.).
    Returns indices relative to the outer scope (i.e., i - n_bound for each free
    MLrel i). *)
let rec collect_free_rels_set n_bound acc = function
  | MLrel i -> if i > n_bound then IntSet.add (i - n_bound) acc else acc
  | MLlam (_, _, body) -> collect_free_rels_set (n_bound + 1) acc body
  | MLletin (_, _, a, b) ->
    collect_free_rels_set n_bound (collect_free_rels_set (n_bound + 1) acc b) a
  | MLapp (f, args) ->
    List.fold_left
      (collect_free_rels_set n_bound)
      (collect_free_rels_set n_bound acc f)
      args
  | MLcase (_, e, brs) ->
    let acc = collect_free_rels_set n_bound acc e in
    Array.fold_left
      (fun acc (ids, _, _, body) ->
        collect_free_rels_set (n_bound + List.length ids) acc body )
      acc
      brs
  | MLfix (_, ids, funs, _) ->
    let n_fix = Array.length ids in
    Array.fold_left
      (fun acc f ->
        let params, body = collect_lams f in
        collect_free_rels_set (n_bound + List.length params + n_fix) acc body )
      acc
      funs
  | MLcons (_, _, args) ->
    List.fold_left (collect_free_rels_set n_bound) acc args
  | MLmagic a -> collect_free_rels_set n_bound acc a
  | MLtuple args -> List.fold_left (collect_free_rels_set n_bound) acc args
  | MLparray (arr, def) ->
    collect_free_rels_set
      n_bound
      (Array.fold_left (collect_free_rels_set n_bound) acc arr)
      def
  | MLglob _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> acc

(** Collect all free de Bruijn variables (rels) from an ML AST, wrapping
    [collect_free_rels_set]. Used to detect which lambda parameters are
    captured. *)
let collect_free_rels n_bound body =
  IntSet.elements (collect_free_rels_set n_bound IntSet.empty body)

(** Compute ownership flags for function parameters.  Combines escape analysis
    with sub-binding escape for value-typed (prod) params: a param is owned if
    it escapes the body, or if its sub-bindings escape and its ML type is a
    product type (enabling move-from-.first/.second). *)
let infer_owned_flags n_params body params_with_types =
  let base = Escape.infer_owned_params n_params body in
  let sub_esc = Escape.infer_sub_bindings_escape_params n_params body in
  List.map2
    (fun (b, se) (_, ty) -> b || (se && is_prod_ml_type ty))
    (List.combine base sub_esc)
    params_with_types

(** Wraps a C++ parameter type with const/ref based on ownership semantics.
    Owned inductive/shared_ptr params are passed by value (moved in);
    borrowed inductive/shared_ptr params are passed by const reference;
    other types are passed by const value. *)
let wrap_param_by_ownership ?(is_owned = false) cpp_ty =
  match cpp_ty with
  | Tshared_ptr _ when is_owned -> cpp_ty
  | Tshared_ptr _ -> Tref (Tmod (TMconst, cpp_ty))
  | _ when is_inductive_value_type cpp_ty ->
    if is_owned then cpp_ty  (* pass by value, caller moves *)
    else Tref (Tmod (TMconst, cpp_ty))  (* const T& for borrowing *)
  | Tvar _ | Tqualified _ ->
    (* Template type parameters and dependent types (e.g. typename C::t) have
       unknown concrete size; always pass by const-ref to avoid deep copies.
       When owned (caller moves in), pass by value to enable move semantics. *)
    if is_owned then cpp_ty
    else Tref (Tmod (TMconst, cpp_ty))
  | _ -> cpp_ty

(** Check if the return type of an ML function type is erased — i.e., it
    becomes [std::any] in C++.  This covers three cases:
    - Promoted type vars (erased carrier projections like [Obj C]).
    - [Tunknown] arising from dependent type families.
    - Erased type constants — non-promoted type-valued record fields
      (e.g. [Hom : Obj -> Obj -> Type] in [PreCategory]) registered during
      extraction via {!Table.add_erased_type_const}. *)
let rec ml_return_type_is_erased = function
  | Miniml.Tarr (_, ret) -> ml_return_type_is_erased ret
  | Miniml.Tmeta { contents = Some t } -> ml_return_type_is_erased t
  | Miniml.Tglob (g, _, _) when Table.is_promoted_type_var g -> true
  | Miniml.Tglob (g, _, _) when Table.is_erased_type_const g -> true
  | Miniml.Tunknown -> true
  | _ -> false

(** Check if an ML expression is (or starts with) a record field projection
    whose projected field returns a promoted type var (erased to [std::any] in
    C++).  This detects the gap between Coq-level types and C++ types that
    arises when a record like [Functor] uses erased carriers ([Obj = std::any])
    in its field types.

    For example, [object_of forward_functor 7] is an [MLapp] wrapping an
    [MLcase] record projection.  The projected field [object_of] has ML type
    [carrier → carrier] whose return type [carrier] is a promoted var.  The
    Coq type says the result is [nat = unsigned int], but the C++ expression
    [forward_functor->object_of(7u)] actually returns [std::any]. *)
let rec ml_body_returns_erased_field = function
  | Miniml.MLapp ((MLglob (r, tys) | MLmagic (MLglob (r, tys))), args) as full ->
    let direct =
      match find_type_opt r with
      | Some ty ->
        let ty = match tys with [] -> ty | _ -> ml_subst_tvars (Array.of_list tys) ty in
        ( match strip_tarr_n (count_real_ml_args args) ty with
        | Some ret_ty -> ml_return_type_is_erased ret_ty
        | None -> false )
      | None -> false
    in
    direct ||
    (match full with Miniml.MLapp (f, _) -> ml_body_returns_erased_field f | _ -> false)
  | Miniml.MLapp (f, _) -> ml_body_returns_erased_field f
  | MLmagic f -> ml_body_returns_erased_field f
  | MLcase (typ, _, pv) when Array.length pv = 1 ->
    let ids, _, _, proj_body = pv.(0) in
    let n = List.length ids in
    let proj_idx =
      match proj_body with
      | MLrel i when i >= 1 && i <= n -> Some (n - i)
      | MLmagic (MLrel i) when i >= 1 && i <= n -> Some (n - i)
      | MLapp (MLrel i, _) when i >= 1 && i <= n -> Some (n - i)
      | MLapp (MLmagic (MLrel i), _) when i >= 1 && i <= n -> Some (n - i)
      | _ -> None
    in
    ( match proj_idx with
    | Some idx -> (
      match typ with
      | Tglob (r, _, _) ->
        let all_field_types = Table.record_field_types r in
        let non_erased =
          filter_value_types all_field_types
        in
        ( try
            let field_ty = List.nth non_erased idx in
            ml_return_type_is_erased field_ty
          with _ -> false )
      | _ -> false )
    | None -> false )
  | _ -> false

(** Check if the head of an ML application has an [MLmagic] wrapper.

    The [simpl] optimization in {!Mlutil} transforms
    [MLmagic(MLapp(f, args))] into [MLapp(MLmagic(f), args)], pushing magic
    inside application heads.  A top-level [MLmagic] check therefore misses
    these cases.  This function follows application heads recursively.

    Used in {!gen_spec} to detect when a function call's result needs a C++
    cast to match the expected return type. *)
let rec ml_head_has_magic = function
  | Miniml.MLmagic _ -> true
  | MLapp (f, _) -> ml_head_has_magic f
  | _ -> false

(** Wrap [expr] when [storage_ty] and [api_ty] differ due to pointer
    wrapping.  Converts from API form to storage form (e.g. bare value →
    [shared_ptr]).  No-op when the types match or neither involves smart
    pointers. *)
let wrap_storage_expr ~storage_ty ~api_ty expr =
  if storage_ty <> api_ty && contains_shared_ptr storage_ty then
    gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:storage_ty expr
  else
    expr

(** Like {!wrap_storage_expr} but converts from storage form to API form
    (e.g. [shared_ptr] → bare value). *)
let wrap_api_expr ~storage_ty ~api_ty expr =
  if storage_ty <> api_ty && contains_shared_ptr storage_ty then
    gen_type_conversion_expr ~src_ty:storage_ty ~dst_ty:api_ty expr
  else
    expr

(** Convert ML type to C++ type. Handles custom types, inductives, type
    variables, and erased parameters. env: variable environment; ns: set of
    local references; tvars: type variable names *)
let rec convert_ml_type_to_cpp_type
    env
    ?(ns : Refset'.t = Refset'.empty)
    (tvars : Id.t list)
    (ml_t : ml_type) : cpp_type =
  (* [ns] is the only source of recursive-storage wrapping.  Most callers
     omit it (defaulting to empty), so types like [List<tree>] stay value
     shaped in function signatures.  Struct-field storage conversion passes the
     owning inductive in [ns], so non-coinductive recursive occurrences at
     constructor storage sites become [shared_ptr]. *)
  match ml_t with
  | Tarr (t1, t2) ->
    (* std::function<F(A)> is already a value type and provides the heap
       indirection needed to break recursive layout cycles.  Always pass an
       empty [ns] for domain and codomain so that recursive self-references
       inside function types stay as value types instead of being wrapped in
       shared_ptr.  The outer field-position wrapping (shared_ptr for direct
       self-ref fields) is handled at the call site, not here. *)
    let t1c = convert_ml_type_to_cpp_type env tvars t1 in
    (* Reify monadic domain types: itree E R in parameter position becomes
       shared_ptr<ITree<R>> so the tree can be passed as a value. *)
    let t1c = reify_monadic_param_type t1 t1c in
    let t2c = convert_ml_type_to_cpp_type env tvars t2 in
    (* Skip erased params: isTdummy catches direct Tdummy, is_cpp_dummy_type
       catches Tdummy wrapped in Tmeta (e.g., Tmeta{contents=Some(Tdummy Kprop)}
       which converts to dummy_prop glob). Do NOT use is_erased_type here as it
       also catches Tany (std::any), which is a valid type for universally
       quantified parameters — stripping it would incorrectly collapse (A -> IO)
       into just IO. *)
    if isTdummy t1 || is_cpp_dummy_type t1c then
      t2c
    else (
      (* Void-ify unit codomain: function types returning [unit] (directly
         or via monadic wrapper like [itree E unit]) should map to [void]
         to match void-ified function definitions. Check the ML type [t2]
         since the C++ type may still be a monad Tglob, not bare unit. *)
      let voidify_cod c =
        if is_cpp_unit_type c then Tvoid
        else if ml_type_is_unit (ml_result_type t2) then Tvoid
        else c
      in
      match
        t2c
      with
      | Tfun (l, t) -> Tfun (t1c :: l, voidify_cod t)
      | _ -> Tfun (t1c :: [], voidify_cod t2c) )
  | Tglob (g, _, _) when is_void g -> Tvoid
  (* PROMOTED TYPE VARIABLES: Handle references to record fields that were
     "promoted" from value-level fields to type-level parameters.

     A "promoted" field is a Type-valued record field (e.g., [m_carrier : Type]
     in [Record Monoid]) that became a C++ concept type requirement instead of
     a struct field. At usage sites, references to these fields must be treated
     as TYPES, not values.

     Example:
       Coq: [mfold (M : Monoid) (l : list (m_carrier M))]
            Here [m_carrier M] is a TYPE (the carrier type of the monoid M)

       C++: [template <Monoid _tcI0> ... List<typename _tcI0::m_carrier> ...]
            Must qualify as a type, not access as a field: NOT _tcI0->m_carrier

     Three contexts for promoted type vars:
     1. Inside template functions with typeclass params: [promoted_var_map] is
        populated, resolve to qualified types like [typename _tcI0::m_carrier]
     2. Module-level (constructor expressions): Use module aliases ([std::any])
     3. No context: Mark with [Tvar(1000, ...)] for later resolution *)
  | Tglob (g, ts, _) when Table.is_promoted_type_var g ->
    ( match Table.promoted_type_var_name g with
    | Some var_id ->
      (match
        List.find_opt
          (fun (n, _) -> Id.equal n var_id)
          tctx.promoted_var_map
      with
      | Some (_, resolved) -> resolved
      | None ->
        (* No resolution found.  When the constructor-expression flag is set,
           all promoted vars become [Tany] (= std::any) because module-level
           type aliases are always std::any and non-Type promoted vars (like
           [base_category]) have no alias at all.  Otherwise keep the marker
           for concept generation and signature printing. *)
        if tctx.in_constructor_expr then Tany
        else Tvar (1000, Some var_id) )
    | None -> Tany )
  | Tglob (g, _, _) when Table.is_value_dep_type_scheme g ->
    (* Value-dependent type scheme (e.g. [sym_semty : sym -> Type]) applied to a
       runtime value — not representable as a C++ type, so erase to [std::any].
       This keeps erasure consistent: such values are already stored as
       [std::any], so the types that mention them are [std::any] too, and no
       [any_cast] guard is needed at use sites. *)
    Tany
  | Tglob (g, ts, args) when is_custom g ->
    Tglob
      ( g,
        List.map (convert_ml_type_to_cpp_type env ~ns tvars) ts,
        List.map (gen_expr env) args )
  | Tglob (g, ts, _) ->
    (* For inductives, only keep type args that correspond to parameters (not
       indices). Parameters become template params in C++; indices are
       erased. *)
    let filtered_ts =
      match g with
      | GlobRef.IndRef (kn, _) ->
        (* Filter type args to keep only parameters (not indices). Use
           get_ind_num_param_vars_opt to determine how many to keep. For
           local/self-references with non-empty tvars, we can use tvars length
           as a fallback, but prefer the table lookup for accuracy. *)
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* Only keep the first num_param_vars type args - the rest are
             indices *)
          safe_firstn num_param_vars ts
        | None ->
          (* Fallback: if tvars is non-empty and this is a local reference, use
             tvars length *)
          let is_local =
            Refset'.mem g ns
            || List.exists
                 (globref_equal g)
                 !local_inductives
          in
          if is_local && tvars <> [] then
            safe_firstn (List.length tvars) ts
          else
            ts )
        (* Keep all if we can't determine *)
      | _ -> ts
    in
    (* Only propagate ns into type arguments when g itself is a self-ref.
       For non-self types (e.g. list inside tree's definition), type args
       stay bare — the field-level wrapping handles the cycle-breaking.
       This ensures type variables are never shared_ptr-wrapped at instantiation. *)
    let ns_for_args =
      if Refset'.mem g ns then ns else Refset'.empty
    in
    let converted_ts =
      List.map (convert_ml_type_to_cpp_type env ~ns:ns_for_args tvars) filtered_ts
    in
    let converted_ts =
      match g with
      | GlobRef.IndRef _ ->
        let rec first_ktype_idx i = function
          | [] -> max_int
          | (Tdummy Ktype | Tmeta {contents = Some (Tdummy Ktype)}) :: _ -> i
          | _ :: rest -> first_ktype_idx (i + 1) rest
        in
        let cutoff = first_ktype_idx 0 filtered_ts in
        if cutoff < max_int then
          List.mapi (fun i t -> if i > cutoff then Tany else t) converted_ts
        else
          converted_ts
      | _ -> converted_ts
    in
    let core = Tglob (g, converted_ts, []) in
    ( match g with
    | GlobRef.IndRef _ ->
      (* Enum inductives are value types - no shared_ptr wrapping *)
      if is_enum_inductive g then
        let is_local =
          Refset'.mem g ns
          || List.exists
               (globref_equal g)
               !local_inductives
        in
        if is_local then
          core
        else
          Tnamespace (g, core)
      else
        (* Check if this inductive is in the explicit ns list or in
           local_inductives context *)
        let is_self_ref = Refset'.mem g ns in
        (* Check if g is a mutual sibling: shares the same MutInd.t KerName
           as any member of ns, but at a different index. Mutual siblings
           need shared_ptr because their types are incomplete (forward-declared). *)
        let is_mutual_sibling =
          (not is_self_ref) &&
          match g with
          | GlobRef.IndRef (kn_g, _) ->
            Refset'.exists (fun r ->
              match r with
              | GlobRef.IndRef (kn_r, _) ->
                MutInd.CanOrd.equal kn_g kn_r
              | _ -> false) ns
          | _ -> false
        in
        let is_local =
          is_self_ref
          || List.exists
               (globref_equal g)
               !local_inductives
        in
        let is_uniform_self_ref =
          if not is_self_ref then
            true
          else if converted_ts = [] then
            (* Non-parametric inductive: self-reference is trivially uniform.
               The surrounding context may have type vars (e.g. T1 in rect<T1>)
               that are unrelated to the inductive's own parameters — don't
               let those force shared_ptr for a monomorphic self-reference. *)
            true
          else
            List.length converted_ts = List.length tvars
            && List.for_all2
                 (fun ty id ->
                   match ty with
                   | Tvar (_, Some id') -> Id.equal id id'
                   | _ -> false)
                 converted_ts
                 tvars
        in
        if
          (is_self_ref || is_mutual_sibling)
          && not (Table.is_coinductive g)
          && is_uniform_self_ref
        then
          (* Recursive value-type self/mutual references are owned by their
             containing constructor. The pointed-to type may be incomplete at
             field declaration time, so it still needs indirection, but unique
             ownership plus explicit clone is enough. *)
          Tshared_ptr core
        else if is_self_ref || is_mutual_sibling then
          (* Non-uniform recursion and coinductive self-references use
             shared_ptr.  Non-uniform recursion requires shared_ptr rather than
             unique_ptr because destructor instantiation would diverge.  Coinductive
             recursive fields need shared_ptr because the lazy thunk
             copies the tail reference ([=] capture). *)
          Tshared_ptr core
        else if is_local then
          (* Local non-self inductive: value type, no pointer wrapping *)
          core
        else if not (get_record_fields g == []) then
          (* Record inductive: value type, no pointer wrapping *)
          core
        else
          (* External inductive: value type, namespace-qualified *)
          Tnamespace (g, core)
    | _ -> core )
  | Tvar i | Tvar' i ->
    ( try Tvar (i, Some (List.nth tvars (pred i)))
      with Failure _ -> Tvar (i, None) )
  | Tmeta {contents = Some t} -> convert_ml_type_to_cpp_type env ~ns tvars t
  | Tmeta {id = i} ->
    (* Unresolved meta - use std::any for type erasure. This happens for
       existential type variables in indexed inductives. *)
    Tany
  (* Tdummy marks erased type/prop/implicit parameters in the ML AST. We convert
     them to Tglob(VarRef "dummy_*") as intermediate markers so that downstream
     filtering (is_cpp_dummy_type / is_erased_type / filter_erased_type_args in
     gen_expr, eta_fun, and gen_decl_for_pp) can detect and drop them. These
     markers should never survive to the C++ output — the filtering pipeline
     removes them from template argument lists and function signatures. *)
  | Tdummy Ktype -> Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
  | Tdummy Kprop -> Tglob (GlobRef.VarRef (Id.of_string "dummy_prop"), [], [])
  | Tdummy (Kimplicit _) ->
    Tglob (GlobRef.VarRef (Id.of_string "dummy_implicit"), [], [])
  | Tstring ->
    Tid_external (Id.of_string_soft "std::string", [])
  | Tunknown -> Tany
  | Taxiom -> Tglob (GlobRef.VarRef (Id.of_string "axiom"), [], [])

(** Convert ML type arguments to C++ template parameters, applying type
    simplification and handling out-of-scope type variables.

    This function maps a list of ML types to C++ types for use in template
    argument lists. It performs two key transformations:

    1. Type simplification via [type_simpl] to normalize ML types
    2. Conversion to C++ types via [convert_ml_type_to_cpp_type]
    3. Detection and erasure of unbound type variables

    The [tvars] parameter specifies the type variables in scope (as a list of
    typename declarations in the current C++ context). When a [Tvar] appears
    with [None] for its binding and [tvars] is non-empty, this indicates the
    type variable index is out of scope — it references a typename that doesn't
    exist in the current C++ context.

    Out-of-scope type variables are marked as [dummy_type], which triggers
    [filter_erased_type_args] to drop the entire type argument list. This is
    safer than emitting invalid C++ like [template<typename T> ... U] where
    [U] is undefined.

    Example scenario where this occurs:
    - ML function with type scheme [forall A B, A -> B -> option A]
    - Partial application instantiates [A] but leaves [B] polymorphic
    - C++ code generator enters context with only [typename A]
    - Type arg list includes [Tvar 2] for [B]
    - [convert_ml_type_to_cpp_type] returns [Tvar(2, None)] (no binding)
    - We mark it [dummy_type] to trigger erasure

    @param env   Translation environment (unused in current implementation)
    @param tvars Type variables in scope (C++ typename parameters)
    @param tys   ML type arguments to convert
    @return List of C++ types, with out-of-scope Tvars marked as dummy_type *)

(** [convert_ml_type_to_cpp_type] only resolves [Tvar] indices within
    [tvars]; anything out of range comes back as [Tvar (_, None)], which
    prints as a bogus, undeclared template parameter name (e.g. "T3").
    Normalize those to [Tany] instead, since they represent erased/
    unresolvable data. *)
and erase_unresolved_tvars = function
  | Tvar (_, None) -> Tany
  | Tglob (g, ts, es) -> Tglob (g, List.map erase_unresolved_tvars ts, es)
  | Tfun (dom, cod) ->
    Tfun (List.map erase_unresolved_tvars dom, erase_unresolved_tvars cod)
  | Tshared_ptr t -> Tshared_ptr (erase_unresolved_tvars t)
  | Tref t -> Tref (erase_unresolved_tvars t)
  | t -> t

(** [resolves_to_any_type ty] — true if [ty] ultimately resolves to
    [std::any].  Handles direct [Tany], erased-type constants (aliases for
    [std::any] registered via {!Table.is_erased_type_const}), and type
    aliases that expand to an erased type.  Used to decide whether a
    scrutinee's template argument makes a constructor field store its
    value as [std::any] at runtime. *)
and resolves_to_any_type = function
  | Tany -> true
  | Tglob (g, [], _) when Table.is_erased_type_const g -> true
  | Tglob (g, [], _) ->
    (match find_type_opt g with
     | Some ml_ty ->
       let tvars = get_current_type_vars () in
       resolves_to_any_type (convert_ml_type_to_cpp_type (empty_env ()) tvars ml_ty)
     | None -> false)
  | t when is_erased_type t -> true
  | _ -> false

(** [populate_erased_field_env ~cname ~typ ~env ~n_pat_vars ~n_fields
    ~non_erased_def_site_field_tys] populates {!cpp_erased_env} and
    {!cpp_erased_type_env} for a pattern-match branch.  For each
    constructor field whose definition-site type is a type variable that
    resolves to [std::any] via the scrutinee's template arguments, marks
    the corresponding de Bruijn index as erased and records its concrete
    C++ type from the template arguments.

    @param cname  constructor reference (to look up parameter count)
    @param typ    ML type of the scrutinee
    @param env    translation environment
    @param n_pat_vars  number of pattern variables in this branch
    @param n_fields    number of non-erased constructor fields
    @param non_erased_def_site_field_tys  definition-site field types
           with erased (dummy) entries filtered out *)
and populate_erased_field_env ~cname ~typ ~env ~n_pat_vars ~n_fields
    ~non_erased_def_site_field_tys =
  let scrut_cpp_ty =
    let tvars = get_current_type_vars () in
    convert_ml_type_to_cpp_type env tvars typ
  in
  let scrut_template_args = extract_template_args scrut_cpp_ty in
  let num_pv = Table.get_ctor_num_param_vars cname in
  let check_tvar k =
    match List.nth_opt scrut_template_args (k - 1) with
    | Some t -> resolves_to_any_type t
    | None -> false
  in
  let is_field_stored_as_any field_i =
    if num_pv = 0 then
      match List.nth_opt non_erased_def_site_field_tys field_i with
      | Some def_ty ->
        let cpp_ty =
          convert_ml_type_to_cpp_type (empty_env ()) ~ns:Refset'.empty [] def_ty
        in
        has_unnamed_tvar cpp_ty
      | None -> false
    else
      match List.nth_opt non_erased_def_site_field_tys field_i with
      | Some (Miniml.Tvar k | Miniml.Tvar' k) -> check_tvar k
      | Some (Miniml.Tmeta {contents = Some (Miniml.Tvar k | Miniml.Tvar' k)}) ->
        check_tvar k
      | _ -> false
  in
  List.iteri (fun field_i _ ->
    let db_idx = n_pat_vars - field_i in
    if is_field_stored_as_any field_i then
      tctx.cpp_erased_env <- Escape.IntSet.add db_idx tctx.cpp_erased_env;
    (match List.nth_opt non_erased_def_site_field_tys field_i with
     | Some (Miniml.Tvar k | Miniml.Tvar' k) ->
       (match List.nth_opt scrut_template_args (k - 1) with
        | Some t -> tctx.cpp_erased_type_env <- IntMap.add db_idx t tctx.cpp_erased_type_env
        | None -> ())
     | _ -> ())
  ) (List.init n_fields Fun.id)

(** Save the current erased-env state for later restoration. *)
and save_erased_env () =
  (tctx.cpp_erased_env, tctx.cpp_erased_type_env)

(** Restore erased-env state from a previously saved pair. *)
and restore_erased_env (saved_env, saved_type_env) =
  tctx.cpp_erased_env <- saved_env;
  tctx.cpp_erased_type_env <- saved_type_env

and build_template_params env tvars tys =
  (* Template params emitted at expression/function-call sites are public API
     types. Recursive storage wrapping is introduced only when converting
     constructor fields with an explicit storage namespace. *)
  let ns = Refset'.empty in
  List.map
    (fun ty ->
      (* Simplify and convert the ML type to C++ *)
      let t =
        convert_ml_type_to_cpp_type env ~ns tvars (type_simpl ty)
      in
      (* Check for unbound type variables *)
      match t with
      | Tvar (_, None) when tvars <> [] ->
        (* Type variable has no binding, but we're in a context with typename
           params. This means the Tvar index exceeds the scope of tvars.
           Mark as dummy_type to trigger full erasure via filter_erased_type_args.
           Using the unbound Tvar would generate invalid C++ references. *)
        Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
      | _ ->
        (* Type is either bound, or we're in an untyped context (tvars = []).
           Keep the type as-is. *)
        t )
    tys

(** Generate code for a custom-extracted constructor application.

    Custom-extracted constructors have user-defined C++ syntax (registered via
    [Crane Extract Constant]) that may include type argument placeholders like
    [%t0], [%t1], etc. This function builds the C++ expression by:
    1. Filtering the ML type argument list to keep only type parameters
       (dropping index arguments that don't correspond to C++ template params)
    2. Converting ML types to C++ types via [build_template_params]
    3. Filtering erased types (Tdummy Ktype → dummy_type) to avoid passing
       empty or partial template argument lists to custom syntax
    4. Wrapping in [mk_cppglob] to apply the custom syntax template

    The filtering is critical because custom syntax strings expect concrete
    type arguments for their placeholders. If we pass an empty or erased
    type arg list, the custom syntax renderer in cpp_print.ml will raise
    an anomaly ("Custom syntax: unbound type argument").

    Example:
    - ML: [MLcons(Tglob(option, [Tglob(nat)]), cons_ctor, [5])]
    - Custom syntax: [(Datatypes.option, 0) := "std::optional<%t0>"]
    - After filtering: [std::optional<unsigned int>]
    - Generated C++: [std::make_optional<unsigned int>(5u)]

    Note: This only handles custom constructors. Regular (non-custom) inductives
    follow a different code path via the main [gen_expr] MLcons case.

    @param env Translation environment (contains type context)
    @param ty  ML type of the constructor application (contains type args)
    @param r   Constructor reference (must be custom-extracted)
    @param ts  ML expression arguments (converted to C++ recursively)
    @return C++ expression applying custom syntax with type/value arguments *)

and gen_expr_custom_cons env (ty : ml_type) r ts =
  (* Try to fold binary positive chains inside Z/N constructors to avoid
     unsigned-int overflow.  Zpos(xI(xO(...xH...))) and Zneg(...) chains
     are folded into INT64_C(n) / INT64_C(-n) literals when the parent
     inductive has a numeral format registered via Crane Extract Numeral. *)
  let folded =
    match (r, ts) with
    | GlobRef.ConstructRef ((kn, i), cidx), [inner] ->
      let ind_ref = GlobRef.IndRef (kn, i) in
      ( match Table.get_numeral_info ind_ref with
      | Some info -> try_fold_z_binary info cidx inner
      | None -> None )
    | _ -> None
  in
  match folded with
  | Some e -> e
  | None ->
  (* Some custom-extracted inductives (e.g. [sum1], registered as
     [Crane Extract Inductive sum1 => "" ["%a0" "%a0"]]) are pure type-level
     erasure markers: their constructor template forwards the argument
     completely unboxed, with no runtime wrapper type at all. For these, the
     generic "erase Tvar-typed fields into std::any" logic below must NOT
     fire, because there is no field storage to box into — the value must
     stay exactly as it was produced. Wrapping it anyway makes the erased
     [std::any] hold the argument's own (possibly unique closure) type
     instead of whatever a downstream consumer expects inside that [std::any]
     (e.g. [itree_vis] expects [std::function<std::any()>], not a bare
     lambda), and the mismatched [std::any_cast] throws at runtime
     (CWE-704, finding 44). *)
  let is_passthrough_ctor_arg i =
    match r with
    | GlobRef.ConstructRef ((kn, mi), cidx) ->
      ( try
          let tmpl = List.nth (Table.find_custom_ctor_templates (kn, mi)) (cidx - 1) in
          String.trim tmpl = Printf.sprintf "%%a%d" i
        with _ -> false )
    | _ -> false
  in
  (* PROMOTED TYPE VARIABLES in constructor expressions: Use module-level
     aliases (std::any) instead of template-qualified types.

     Inside a template function taking a typeclass parameter, promoted type vars
     normally resolve via [promoted_var_map]:
       [m_carrier] ↦ [typename _tcI0::m_carrier]

     But constructor expressions are NOT in template scope — they're module-level
     static initializers:
       static inline const Functor forward_functor = ...;

     Here, there's no [_tcI0] to qualify. Instead, promoted vars use the
     module-level [using] declaration:
       using Obj = std::any;
       using Hom = std::any;

     So [object_of forward_functor 7] becomes:
       forward_functor->object_of(7u)  // returns std::any
       std::any_cast<unsigned int>(...)  // cast to concrete type

     Setting [in_constructor_expr] makes unresolvable promoted vars (those
     NOT in [promoted_var_map]) fall back to [Tany] = [std::any].

     We do NOT clear [promoted_var_map] here: inside template functions,
     promoted vars must resolve to qualified types (e.g., typename _tcI0::Obj)
     so that constructor type args match the function's declared return type.
     At module level, [promoted_var_map] is already empty, so the
     [in_constructor_expr] fallback handles it naturally. *)
  let saved_in_ctor = tctx.in_constructor_expr in
  tctx.in_constructor_expr <- true;
  (* Convert value arguments to C++ expressions.

     Erased proof/type arguments ([MLdummy]) produce [std::any{}] rather
     than [CPPabort]: the corresponding C++ parameter type is [std::any]
     (all erased types map to [std::any]), and custom constructors like
     [std::make_pair] are evaluated eagerly so a throw would crash at
     runtime.  This mirrors the [gen_ctor_arg] in the [MLcons] case of
     {!gen_expr}. *)
  (* Generate constructor arguments with live move_dead_after so the move
     analysis can fire for single-use variables (nb_occur_match = 1 already
     prevents moving variables that appear more than once across all args). *)
  let gen_ctor_arg ?expected_ty e =
    match e with
    | MLdummy _ -> CPPconverting_ctor (Tany, [])
    | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
      wrap_void_call_as_value (gen_expr env e)
    | _ -> gen_expr ?expected_ty env e
  in
  (* Generate args with expected type hints: set expected_ml_type_for_arg to
     the i-th type arg of the constructor's inductive type before generating
     the i-th value arg.  This allows gen_ctor_call to recover concrete element
     types for nil lists whose ML annotation has unresolved metas (Tmeta{None}).
     Specifically: in pair(fr, nil), the pair type args [A, B] tell us B = list(A),
     so the nil's element type can be recovered as A even if its annotation is Tmeta. *)
  (* Try to get type args from the pair type annotation, falling back to the
     outer expected_ml_type_for_arg (set by an enclosing MLletin or MLapp
     lookahead) when the pair type itself is erased (Tmeta{None}). This
     recovers the expected element type for nil args in pairs like
       let sk0 : parser_frame × list(parser_frame) = (fr(...), nil)
     where the pair MLcons has type annotation Tmeta{None}. *)
  let ty_args_for_expected =
    let rec deep_resolve ty =
      match resolve_tmeta ty with
      | Miniml.Tglob (n, tys, s) -> Miniml.Tglob (n, List.map deep_resolve tys, s)
      | Miniml.Tarr (t1, t2) -> Miniml.Tarr (deep_resolve t1, deep_resolve t2)
      | t -> t
    in
    (* Also try the expected type from the enclosing let-binding when deep_resolve
       can't resolve sub-metas in the pair's own type annotation.
       The expected type comes from t_effective which may have different (resolved) metas. *)
    let fallback_from_expected tys =
      if List.exists ml_type_contains_erased tys then
        match tctx.expected_ml_type_for_arg with
        | Some exp ->
          let ctor_ind = match r with
            | GlobRef.ConstructRef ((kn, i), _) -> Some (GlobRef.IndRef (kn, i))
            | _ -> None
          in
          (match deep_resolve exp, ctor_ind with
          | Miniml.Tglob (exp_n, exp_tys, _), Some ind
            when GlobRef.CanOrd.equal exp_n ind
                 && List.length exp_tys = List.length tys ->
            List.map2 (fun local outer ->
              if ml_type_contains_erased local then outer else local) tys exp_tys
          | _ -> tys)
        | None -> tys
      else tys
    in
    match deep_resolve ty with
    | Miniml.Tglob (_, tys, _) -> fallback_from_expected tys
    | _ ->
      (match tctx.expected_ml_type_for_arg with
      | Some exp ->
        let ctor_ind = match r with
          | GlobRef.ConstructRef ((kn, i), _) -> Some (GlobRef.IndRef (kn, i))
          | _ -> None
        in
        (match deep_resolve exp, ctor_ind with
        | Miniml.Tglob (exp_n, exp_tys, _), Some ind
          when GlobRef.CanOrd.equal exp_n ind -> exp_tys
        | _ -> [])
      | None -> [])
  in
  (* Pre-compute field types and draft template types so we can wrap lambdas
     that are stored in erased (std::any) fields.  This mirrors the logic in
     wrap_if_needed_for_field for the standard MLcons path. *)
  let field_types_for_wrap = match Table.get_ctor_ip_types_opt r with
    | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
    | None -> [] in
  let draft_ctor_temps_for_wrap = match ty with
    | Miniml.Tglob (cn, raw_tys, _) ->
      let tys = match cn with
        | GlobRef.IndRef (kn, _) ->
          (match Table.get_ind_num_param_vars_opt kn with
          | Some nv -> safe_firstn nv raw_tys
          | None -> raw_tys)
        | _ -> raw_tys
      in
      let temps = build_template_params env [] tys in
      (* When all type args are erased and promoted_var_map is active, use
         concrete promoted types so elements don't get wrapped in std::any. *)
      if List.for_all is_erased_type temps && tctx.promoted_var_map <> [] then
        let promoted_tys =
          List.filter_map (fun (_, cpp_ty) ->
            if is_erased_type cpp_ty then None else Some cpp_ty
          ) tctx.promoted_var_map
        in
        if List.length promoted_tys = List.length tys then promoted_tys
        else temps
      else temps
    | _ -> []
  in
  (* When a pair/tuple constructor has at least one erased (Tany) type parameter,
     ALL type-variable fields must be stored as std::any so that the runtime cast
     in concat_tuple_rec_case (any_cast<pair<any,any>>) succeeds.  E.g., for
     symbols_semty [x] = prod (symbol_semty x) unit: the first field is Tany
     (erased symbol_semty x) but the second is concrete unit.  Without this flag
     the second element stays as std::monostate{} and the pair<any,monostate> cast
     in concat_tuple_rec_case fails. *)
  let draft_has_any_tany = List.mem Tany draft_ctor_temps_for_wrap in
  let args =
    List.rev (List.mapi (fun i e ->
      let saved_expected = tctx.expected_ml_type_for_arg in
      let saved_ret = tctx.current_cpp_return_type in
      let new_expected =
        match List.nth_opt ty_args_for_expected i with
        | Some _ as x -> x
        | None ->
          (* Fall back to the concrete field type when the enclosing constructor
             has an erased ML type (e.g. pair(pred, action) with Tmeta{None}).
             Combined with the MLlam Tarr-stripping logic, this lets gen_ctor_call
             recover the concrete element type for nil constructors. *)
          List.nth_opt field_types_for_wrap i
      in
      tctx.expected_ml_type_for_arg <- new_expected;
      tctx.current_cpp_return_type <- None;
      let expected_cpp_ty =
        match new_expected with
        | Some ml_ty ->
          let tvars = get_current_type_vars () in
          let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
          if is_erased_type cpp_ty then None
          else (match cpp_ty with
            | Tglob (g, _, _) when is_list_global g -> None
            | _ -> Some cpp_ty)
        | None -> None
      in
      let will_erase_fn_wrap =
        match List.nth_opt field_types_for_wrap i with
        | Some (Miniml.Tvar j | Miniml.Tvar' j) ->
          (match List.nth_opt draft_ctor_temps_for_wrap (j - 1) with
          | _ when is_passthrough_ctor_arg i -> false
          | Some Tany -> ml_expr_is_function_value e
          | _ -> false)
        | _ -> false
      in
      let e =
        if will_erase_fn_wrap then
          match strip_magic e with
          | MLlam (id, ty, body) ->
            (* The lambda is stored via [crane_erase_fn] into an erased slot,
               so at runtime it is invoked with its argument boxed as a single
               [std::any] holding the fully-erased representation
               ([pair<any,any>] for a pair domain) — that is what producers of
               a value-dependent type emit (see [flows_into_erased_slot]).  Its
               parameter's own pattern match must therefore treat the scrutinee
               as erased and go through [any_cast<pair<any,any>>]. *)
            let tvars = get_current_type_vars () in
            let param_cpp_ty = convert_ml_type_to_cpp_type env tvars ty in
            if Ml_type_util.has_tany_in_type param_cpp_ty then
              MLlam (id, ty, mark_own_param_for_pair_erasure 1 body)
            else
              (* Domain resolves to a fully concrete type at this literal (e.g.
                 a literal index [0] picks out a concrete branch of a dependent
                 type family), yet the value received at runtime is the erased
                 [pair<any,any>] a generic producer emits.  Erase the parameter
                 to [std::any] so the lambda renders with an erased parameter
                 and the [any_cast<pair<any,any>>] on it compiles. *)
              MLlam (id, Miniml.Tunknown, mark_own_param_for_pair_erasure 1 body)
          | _ -> e
        else e
      in
      let result = gen_ctor_arg ?expected_ty:expected_cpp_ty e in
      tctx.current_cpp_return_type <- saved_ret;
      tctx.expected_ml_type_for_arg <- saved_expected;
      (* When this pair/tuple value flows directly into a value-dependent
         erased slot — the enclosing function's C++ return type resolves to
         [std::any] (e.g. [domty n], a type-level match) — a generic consumer
         reconstructs its shape from the match structure and reads it back as
         [pair<std::any, std::any>] with each component boxed.  The concrete
         component types available here (e.g. [string], [unit]) would produce
         [pair<string, monostate>], which the consumer's
         [any_cast<pair<any,any>>] cannot recover.  Box each concrete component
         into [std::any] so the stored representation is the fully-erased
         [pair<any,any>] the consumer expects. *)
      let flows_into_erased_slot =
        match tctx.current_cpp_return_type with
        | Some t -> resolves_to_any_type t
        | None -> false
      in
      let result = match List.nth_opt field_types_for_wrap i with
        | Some (Miniml.Tvar j | Miniml.Tvar' j) ->
          (match List.nth_opt draft_ctor_temps_for_wrap (j - 1) with
          | _ when is_passthrough_ctor_arg i -> result
          | Some Tany ->
            (match result with
            | _ when ml_expr_is_function_value e ->
              (* Function value stored into an erased ([std::any]) field via a
                 custom constructor (e.g. a [std::pair<std::any, std::any>]
                 component from [prod]).  Route it through [crane_erase_fn] so
                 the stored [std::any] holds a [std::function<std::any(std::any)>]
                 that the application-site [any_cast] can recover, instead of a
                 raw closure.  This covers both non-lambda callables (named
                 [mk] parameters) and inline lambda literals — including the
                 generic [ [](const auto&){...} ] form produced when the
                 function's domain is an erased/abstract type. *)
              Table.mark_needs_erase_fn ();
              CPPfun_call (CPPvar (Id.of_string "crane_erase_fn"), [result])
            | CPPlambda _ -> result
            | _ -> CPPconverting_ctor (Tany, [result]))
          | Some _ when draft_has_any_tany ->
            (* Concrete-typed field in a constructor where another field is erased.
               E.g. (v, tt) : symbols_semty [x] = prod (symbol_semty x) unit — the
               second field is concrete unit but concat_tuple_rec_case casts the
               pair as pair<any,any>, so std::monostate{} must become
               std::any(std::monostate{}). *)
            CPPconverting_ctor (Tany, [result])
          | Some _
            when flows_into_erased_slot
                 && (match result with
                     | CPPconverting_ctor (Tany, _) | CPPany_cast _ -> false
                     | _ -> true) ->
            (* Concrete component of a pair/tuple whose whole value flows into
               a value-dependent erased slot (see [flows_into_erased_slot]).
               Box it so the stored representation is [pair<any,any>], matching
               what a generic consumer's [any_cast<pair<any,any>>] recovers. *)
            CPPconverting_ctor (Tany, [result])
          | _ -> result)
        | _ -> result
      in
      let result =
        if tctx.wrap_for_any_param then
          let is_recursive_field =
            match List.nth_opt field_types_for_wrap i with
            | Some (Miniml.Tglob (field_ind, _, _)) ->
              (match r with
              | GlobRef.ConstructRef ((kn, mi), _) ->
                GlobRef.CanOrd.equal field_ind (GlobRef.IndRef (kn, mi))
              | _ -> false)
            | _ -> false
          in
          (* Don't wrap in std::any when building a custom LIST cons and the
             element cpp type is a container (e.g. pair<any,any>).  Storing
             pair<any,any> directly in deque<pair<any,any>> keeps element types
             consistent with what gen_match_branch expects via erase_type_to_any.
             Only apply this for LIST cons: pair/tuple fields must stay as
             std::any so that any_cast<pair<any,any>> at the consumer works. *)
          let is_list_cons_ctor =
            match r with
            | GlobRef.ConstructRef ((kn, _), _) ->
              let ind = GlobRef.IndRef (kn, 0) in
              is_list_global ind && Table.is_custom ind
            | _ -> false
          in
          let is_already_container =
            is_list_cons_ctor &&
            match new_expected with
            | Some ml_fty ->
              let tvars = get_current_type_vars () in
              let cpp_fty = convert_ml_type_to_cpp_type env tvars ml_fty in
              (match cpp_fty with
               | Tglob (_, _ :: _, _) -> true
               | _ -> false)
            | None -> false
          in
          if is_recursive_field || is_already_container then result
          else CPPconverting_ctor (Tany, [result])
        else result
      in
      result) ts)
  in
  (* Helper to wrap expression in function call syntax if it has arguments *)
  let app x =
    match args with
    | [] -> x
    | _ -> CPPfun_call (x, args)
  in
  let result =
    match ty with
    | Miniml.Tglob (n, tys, _) ->
      (* Step 1: Filter out index type args - only keep parameters.

         Inductive types distinguish between parameters (uniform across all
         constructors, e.g., the [A] in [list A]) and indices (may vary,
         e.g., the [n] in [vec A n]). In C++, only parameters become template
         arguments; indices are encoded in types or runtime values.

         We use [get_ind_num_param_vars_opt] to find the parameter count and
         [safe_firstn] to extract them. [safe_firstn] handles cases where the
         type arg list is shorter than expected (e.g., due to Tdummy Ktype
         erasure in make_tyargs). *)
      let tys =
        match n with
        | GlobRef.IndRef (kn, _) ->
          ( match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars ->
            (* Take first num_param_vars elements, or fewer if list is short *)
            safe_firstn num_param_vars tys
          | None ->
            (* Not in table - keep all type args *)
            tys )
        | _ ->
          (* Not an inductive ref - keep all type args *)
          tys
      in
      (* Step 2: Convert ML types to C++ types *)
      let temps = build_template_params env [] tys in
      let temps = filter_erased_type_args temps in
      (* Step 2b: Recover type args from the return type when unresolved metas
         caused all type args to be erased.  This happens for nullary custom
         constructors (e.g., None) inside let-bindings: the extraction phase
         uses a fresh meta as the expected type, so the constructor's type
         parameter meta never gets unified with the concrete type.  If the
         enclosing function/constant return type matches the same inductive,
         extract the type args from there. *)
      let temps =
        if temps = [] && tys <> []
        then
          let from_expected =
            match tctx.expected_ml_type_for_arg with
            | Some (Miniml.Tglob (exp_r, exp_tys, _))
              when Names.GlobRef.CanOrd.equal exp_r n
                   && List.length exp_tys = List.length tys ->
              let exp_temps = build_template_params env [] exp_tys in
              let r = filter_erased_type_args exp_temps in
              if r <> [] && not (List.exists (function Tvar (_, None) -> true | _ -> false) r)
              then r
              else []
            | _ -> []
          in
          if from_expected <> [] then from_expected
          else
            let from_ret =
              match tctx.current_cpp_return_type with
              | Some (Minicpp.Tglob (ret_r, ret_tys, _))
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length tys ->
                filter_erased_type_args ret_tys
              | Some (Minicpp.Tshared_ptr (Minicpp.Tglob (ret_r, ret_tys, _)))
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length tys ->
                filter_erased_type_args ret_tys
              | _ -> []
            in
            if from_ret <> [] then from_ret
            else if tctx.promoted_var_map <> [] then
              let promoted_tys =
                List.filter_map (fun (_, cpp_ty) ->
                  if is_erased_type cpp_ty then None else Some cpp_ty
                ) tctx.promoted_var_map
              in
              if List.length promoted_tys = List.length tys then
                promoted_tys
              else temps
            else temps
        else temps
      in
      let temps =
        if tctx.wrap_for_any_param && temps <> [] then
          (* For custom list constructors (e.g., deque nil), preserve the
             erased element type instead of forcing to Tany. This makes
             deque<pair<any,any>>{} instead of deque<any>{} for list(nat*nat),
             keeping the stored element type consistent with consumers. *)
          let is_custom_list =
            match r with
            | GlobRef.ConstructRef ((kn, _), _) ->
              let ind = GlobRef.IndRef (kn, 0) in
              is_list_global ind && Table.is_custom ind
            | _ -> false
          in
          if is_custom_list then
            List.map erase_type_to_any temps
          else
            List.map (fun _ -> Tany) temps
        else temps
      in
      app (mk_cppglob r temps)
    | _ ->
      (* Type is not a Tglob - no type args to pass.
         This case is rare for custom constructors, which typically have
         Tglob types. Fall back to bare constructor reference. *)
      app (mk_cppglob r [])
  in
  tctx.in_constructor_expr <- saved_in_ctor;
  (* Collapse identity inline customs (%a0) for constructors, matching
     the same collapse done for function applications at gen_expr. *)
  let result =
    match result with
    | CPPfun_call (CPPglob (_, _, Some ci), [single_arg])
      when ci.ci_inline = Some "%a0" ->
      single_arg
    | _ -> result
  in
  result

(** Strip [MLmagic] wrappers recursively — [MLmagic] is a transparent coercion
    in the ML AST and should be ignored by numeral-folding traversals. *)
and strip_magic = function MLmagic e -> strip_magic e | e -> e

(** Whether [e] denotes a value whose ML type is a function (at least one value
    arrow).  Used to decide, at a constructor argument that is stored into an
    erased ([std::any]) field, whether to route it through the [crane_erase_fn]
    runtime helper so the canonical [std::function<std::any(std::any...)>]
    representation is stored (matching the [any_cast] on the application side)
    rather than a raw closure.  An [MLrel] already erased to [std::any]
    ([tctx.cpp_erased_env]) is excluded: it is not callable, so wrapping it
    would miscompile. *)
and ml_expr_is_function_value e =
  match strip_magic e with
  | MLrel i ->
    (not (Escape.IntSet.mem i tctx.cpp_erased_env))
    && ( match get_env_type_opt i with
       | Some t -> count_ml_value_arrows t >= 1
       | None -> false )
  (* A partial application of a global whose codomain mentions a
     value-dependent erased type (e.g. [mk_action n : domty n -> bool]) is
     wrapped in [MLmagic] by the kernel's typing coercion even at the
     application node itself, not just around the whole expression — so
     [strip_magic] above (which only strips the outer expression) does not
     expose the [MLglob] underneath. Look through it here, locally, rather
     than in [infer_ml_body_type] itself (whose result also feeds unrelated
     callers like lambda return-type annotation), so this fix cannot change
     behavior anywhere but function-value detection. *)
  | MLapp (MLmagic f, args) ->
    ( match infer_ml_body_type (MLapp (f, args)) with
    | Some t -> count_ml_value_arrows t >= 1
    | None -> false )
  | other ->
    ( match infer_ml_body_type other with
    | Some t -> count_ml_value_arrows t >= 1
    | None -> false )

(** When a lambda literal is about to be stored via [crane_erase_fn] (see the
    [ml_expr_is_function_value] call site in the custom-constructor arg loop),
    the lambda will only ever be invoked with its whole argument boxed as a
    single raw [std::any] (never with the generically-deduced concrete type),
    because that is exactly what [crane_erase_fn]'s CTAD-non-viable fallback
    forwards. If the lambda's own bound parameter [n] is immediately
    pattern-matched via a custom (e.g. pair) match, that match must therefore
    treat the scrutinee as erased — wrap it in [MLmagic] so
    [gen_custom_cpp_case] emits [any_cast<pair<any,any>>(...)] instead of a
    structured binding directly on the (at runtime erased) parameter. Without
    this, a domain type that is a pair with a mix of erased/concrete fields
    (e.g. [S.sem a * unit]) renders the parameter as a generic [auto&], and the
    destructure compiles fine at the OCaml/template level but fails at C++
    instantiation time when [auto&] deduces to [std::any] (structured
    bindings are not valid on [std::any]). *)
and mark_own_param_for_pair_erasure n body =
  match body with
  | MLcase (ty, MLrel i, pv) when i = n && is_custom_match pv ->
    MLcase (ty, MLmagic (MLrel i), pv)
  | MLmagic a -> MLmagic (mark_own_param_for_pair_erasure n a)
  | other -> other

(** Try to fold a Peano numeral chain (nested constructors) into an integer *)
and try_fold_numeral info expr =
  match strip_magic expr with
  | MLcons (_ty, cr, []) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_zero_ctor ->
      Some 0
    | _ -> None )
  | MLcons (_ty, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_succ_ctor ->
      Option.map (fun n -> n + 1) (try_fold_numeral info inner)
    | _ -> None )
  | _ -> None

(** Try to fold a binary positive chain [xI(xO(...xH...))] into an [int64].
    Returns [Some n] where [n > 0] if the entire chain can be folded, or
    [None] if any node is not a recognized positive constructor.
    Constructor indices (1-based): xI=[positive_xI_idx], xO=[positive_xO_idx],
    xH=[positive_xH_idx]. *)
and try_fold_positive expr : int64 option =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), []) when idx = positive_xH_idx ->
    Some 1L
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) when idx = positive_xI_idx ->
    Option.map (fun n -> Int64.add (Int64.mul 2L n) 1L) (try_fold_positive inner)
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) when idx = positive_xO_idx ->
    Option.map (fun n -> Int64.mul 2L n) (try_fold_positive inner)
  | _ -> None

(** Fold a Zpos/Zneg constructor wrapping a positive chain into a rendered
    numeral string.  [cidx] is the 1-based constructor index of the Z
    constructor; [inner] is its positive argument.  Returns [None] if [inner]
    cannot be folded. *)
and try_fold_z_binary info cidx inner : cpp_expr option =
  Option.map
    (fun pos_val ->
      let z_val =
        if cidx = z_pos_idx then pos_val
        else if cidx = z_neg_idx then Int64.neg pos_val
        else pos_val
      in
      CPPraw (Common.render_template [("%n", Int64.to_string z_val)] info.Table.num_fmt))
    (try_fold_positive inner)

(** Fold a Decimal.uint digit chain into an arbitrary-precision integer.
    Constructor indices (1-based): Nil=[uint_nil_idx], D0..[decimal_d9_idx].
    Digits are processed outside-in (most significant first).
    Uses [Z.t] from zarith to avoid overflow on large literals. *)
and try_fold_decimal_uint expr acc =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), []) when idx = uint_nil_idx ->
    Some acc
  | MLcons (_, GlobRef.ConstructRef (_, cidx), [inner])
    when cidx >= decimal_d0_idx && cidx <= decimal_d9_idx ->
    let digit = Z.of_int (cidx - decimal_d0_idx) in
    try_fold_decimal_uint inner Z.(acc * of_int 10 + digit)
  | _ -> None

(** Fold a Hexadecimal.uint digit chain into an arbitrary-precision integer.
    Constructor indices (1-based): Nil=[uint_nil_idx], D0..[hex_df_idx].
    Uses [Z.t] from zarith to avoid overflow on large literals. *)
and try_fold_hex_uint expr acc =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), []) when idx = uint_nil_idx ->
    Some acc
  | MLcons (_, GlobRef.ConstructRef (_, cidx), [inner])
    when cidx >= hex_d0_idx && cidx <= hex_df_idx ->
    let digit = Z.of_int (cidx - hex_d0_idx) in
    try_fold_hex_uint inner Z.(acc * of_int 16 + digit)
  | _ -> None

(** Fold a Number.uint (UIntDecimal | UIntHexadecimal) into an
    arbitrary-precision integer.
    Constructor indices (1-based): UIntDecimal=[num_uint_decimal_idx],
    UIntHexadecimal=[num_uint_hex_idx]. *)
and try_fold_num_uint expr =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) ->
    if idx = num_uint_decimal_idx then try_fold_decimal_uint inner Z.zero
    else if idx = num_uint_hex_idx then try_fold_hex_uint inner Z.zero
    else None
  | _ -> None

(** Fold a Decimal.signed_int (Pos | Neg) wrapping a Decimal.uint chain.
    Constructor indices (1-based): Pos=[signed_pos_idx], Neg=[signed_neg_idx]. *)
and try_fold_signed_decimal_int expr =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) ->
    if idx = signed_pos_idx then try_fold_decimal_uint inner Z.zero
    else if idx = signed_neg_idx then
      Option.map Z.neg (try_fold_decimal_uint inner Z.zero)
    else None
  | _ -> None

(** Fold a Hexadecimal.signed_int (Pos | Neg) wrapping a Hexadecimal.uint chain.
    Constructor indices (1-based): Pos=[signed_pos_idx], Neg=[signed_neg_idx]. *)
and try_fold_signed_hex_int expr =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) ->
    if idx = signed_pos_idx then try_fold_hex_uint inner Z.zero
    else if idx = signed_neg_idx then
      Option.map Z.neg (try_fold_hex_uint inner Z.zero)
    else None
  | _ -> None

(** Fold a Number.signed_int (IntDecimal | IntHexadecimal) into an
    arbitrary-precision integer.
    Constructors: IntDecimal(idx=1), IntHexadecimal(idx=2). *)
and try_fold_num_int expr =
  match strip_magic expr with
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> try_fold_signed_decimal_int inner
    | GlobRef.ConstructRef (_, 2) -> try_fold_signed_hex_int inner
    | _ -> None )
  | _ -> None

(** Check whether an ML expression's C++ type is erased ([std::any]).
    Used by the [MLmagic] handler to decide whether [any_cast] is needed. *)
and ml_expr_is_erased env (t : ml_ast) : bool =
  let tvars = get_current_type_vars () in
  match t with
  | MLrel i -> is_env_var_erased env tvars i
  | MLapp (f, args) ->
    let n_value_args =
      List.length (List.filter (fun a ->
        match a with MLdummy _ -> false | _ -> true) args)
    in
    let ml_ty_opt = match f with
      | MLglob (r, _) -> find_type_opt r
      | MLrel i -> get_env_type_opt i
      | _ -> None
    in
    ( match ml_ty_opt with
      | Some ml_ty -> ml_codomain_erases_to_any n_value_args ml_ty
      | None -> false )
  | MLglob (r, _) ->
    ( match find_type_opt r with
      | Some ml_ty -> is_erased_type (convert_ml_type_to_cpp_type env tvars ml_ty)
      | None -> false )
  | MLmagic inner -> ml_expr_is_erased env inner
  | MLcase (case_ty, _, _) ->
    ( match case_ty with
      | Miniml.Tvar _ | Miniml.Tvar' _ | Miniml.Tunknown -> true
      | _ -> false )
  | _ -> false

(** Generate C++ expression from ML AST. Main expression compiler - handles
    lambdas, applications, constructors, pattern matching, etc. Monadic
    non-function globals are wrapped in CPPfun_call by the MLglob case below. *)
and gen_expr ?(expected_ty : cpp_type option) env (ml_e : ml_ast) : cpp_expr =
  match ml_e with
  | MLrel i ->
    let var_expr =
      try CPPvar (get_db_name i env)
      with Failure _ -> CPPvar (db_fallback_id i)
    in
    (* Phase 2: move on last use. Emit std::move if: (1) the variable is dead
       after this point, (2) it's an owned variable (not borrowed), and (3) this
       is its only occurrence in the current RHS expression.
       Never move typeclass template parameters (_tcI0, _tcI1, ...) — they
       are type references in the concept paradigm, not owned values. Wrapping
       them in std::move produces invalid C++ like [std::move(_tcI0)::method()]. *)
    let is_tc_param =
      match var_expr with
      | CPPvar id ->
        let s = Id.to_string id in
        String.length s >= 4 && String.sub s 0 4 = "_tcI"
      | _ -> false
    in
    let move_candidate =
      (not is_tc_param)
      && Escape.IntSet.mem i tctx.move_dead_after
      && Escape.IntSet.mem i tctx.move_owned_vars
    in
    let result = if move_candidate then CPPmove var_expr else var_expr in
    if Escape.IntSet.mem i tctx.cpp_erased_env then begin
      match expected_ty with
      | Some ty when not (is_erased_type ty) && ty <> Tvoid ->
        if resolves_to_any_type ty then result
        else CPPany_cast (ty, result)
      | _ -> result
    end
    else result
  | MLapp (MLmagic t, args) -> gen_expr ?expected_ty env (MLapp (t, args))
  | MLapp (MLglob (r, ret_tys), a1 :: l) when is_ret r ->
    if tctx.itree_mode = Reified then begin
      (* Reified mode: Ret produces ITree<R>::ret(value). Don't strip it. *)
      Table.require_itree_header ();
      let t = Common.last (a1 :: l) in
      match t with
      | MLglob (g, _) when is_ghost g ->
        mk_itree_ret Tvoid []
      | MLcons (_, cr, []) when Table.is_tt_constructor cr ->
        mk_itree_ret Tvoid []
      | _ ->
        let inner = gen_expr env t in
        (* Extract R from the monad's type arguments: itree has template "%t1"
           so the ML type args for Ret are [E, R] where E is typically Tdummy
           and R is the result type. *)
        let tvars = get_current_type_vars () in
        let r_cpp =
          let non_dummy = filter_value_types ret_tys in
          match non_dummy with
          | r_ml :: _ ->
            convert_ml_type_to_cpp_type env tvars r_ml
          | [] -> Tvoid
        in
        mk_itree_ret r_cpp [inner]
    end
    else begin
      let t = Common.last (a1 :: l) in
      gen_expr env t
    end
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h -> gen_expr env
     (MLapp (a1, a2::[])) *)
  | MLapp (MLglob (r, _), _ :: _ :: _) as a when is_bind r
      && tctx.itree_mode <> Reified ->
    (* Sequential mode: bind in expression context (e.g., nested inside
       another expression). Wrap in IIFE so gen_stmts can sequentialize. *)
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLapp (MLfix _, _) as a ->
    (* Nested fix application in expression context (e.g., S((fix aux ...) es)).
       Wrap in an IIFE, delegating to gen_stmts which handles MLapp(MLfix
       ...). *)
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLapp (MLapp ((MLglob _ as g), inner_args), outer_args) ->
    (* Flatten nested MLapp when inner callee is a global reference. This arises
       from Rocq partial applications like: div_conq_split x f1 f2 l which
       extracts as MLapp(MLapp(MLglob(dcs), [x,f1,f2]), [l]). Flattening to
       MLapp(MLglob(dcs), [x,f1,f2,l]) lets eta_fun see the complete argument
       list and generate a direct call. *)
    eta_fun env g (inner_args @ outer_args)
  | MLapp (MLglob (r, _), [arg]) when Table.is_numeral_converter r ->
    (* Fold Number.uint/signed_int digit chain into a direct integer literal.
       Tries unsigned (of_num_uint) then signed (of_num_int).
       Falls through to eta_fun on failure. *)
    let ind_ref = Option.get (Table.numeral_ind_of_converter r) in
    ( match Table.get_numeral_info ind_ref with
    | Some info ->
      let folded = match try_fold_num_uint arg with
        | Some _ as r -> r
        | None -> try_fold_num_int arg
      in
      ( match folded with
      | Some n ->
        CPPraw (Common.render_template [("%n", Z.to_string n)] info.Table.num_fmt)
      | None -> eta_fun env (MLglob (r, [])) [arg] )
    | None -> eta_fun env (MLglob (r, [])) [arg] )
  | MLapp (MLcase (typ, scrut, pv), outer_args)
    when Array.length pv = 1
         && not (record_fields_of_type typ == []) ->
    (* Flatten outer args into a single-branch record-projection case body.
       When a typeclass method is partially applied, Rocq extracts it as
       MLcase(instance, [(binds, MLapp(MLrel field, inner_args))]). If this
       MLcase is the callee of an outer MLapp, the inner call only has some
       args while the outer provides the rest — generating a curried C++ call
       like make(a)(b) instead of make(a, b).  Push the outer args into the
       branch body so gen_expr sees the complete argument list. *)
    let (ids, rty, pat, body) = pv.(0) in
    let n_bindings = List.length ids in
    let lifted_outer = List.map (ast_lift n_bindings) outer_args in
    let new_body = match body with
      | MLapp (f, inner_args) -> MLapp (f, inner_args @ lifted_outer)
      | _ -> MLapp (body, lifted_outer)
    in
    gen_expr env (MLcase (typ, scrut, [|(ids, rty, pat, new_body)|]))
  | MLapp (f, args) -> eta_fun env f args
  | MLlam _ as a ->
    let args, a = collect_lams a in
    let lam_params = List.map (fun (x, y) -> (id_of_mlid x, y)) args in
    let args, env = push_vars' lam_params env in
    let saved_env_types = tctx.env_types in
    push_env_types args;
    (* Infer owned/borrowed for each lambda parameter using escape analysis.

       Owned parameters (stored in a data structure or returned) are passed by
       value (shared_ptr<T>), transferring ownership to the callee.  Borrowed
       parameters (only read, not stored/returned) are passed by const ref
       (const shared_ptr<T>&), avoiding a refcount bump on every call.

       The inference is conservative: if a parameter escapes in any code path
       (e.g. captured by a closure, stored in a constructor, or returned), it
       is marked as owned.  See {!Escape.infer_owned_params}. *)
    let n_all_params = List.length lam_params in
    let owned_flags = infer_owned_flags n_all_params a args
    in
    let args_with_owned =
      List.map2 (fun (id, ty) owned -> (id, ty, owned)) args owned_flags
    in
    let filtered_args_with_owned =
      List.filter (fun (_, ty, _) ->
        not (isTdummy ty) && not (ml_type_is_void ty)
        && not (tctx.itree_mode = Reified && ml_type_is_unit ty))
        args_with_owned
    in
    let filtered_args =
      List.map (fun (id, ty, _) -> (id, ty)) filtered_args_with_owned
    in
    let f =
      with_escape_analysis a (fun () ->
        let tvars = get_current_type_vars () in
        let cpp_arg_info =
          List.map
            (fun (id, ty, owned) ->
              let bare_cpp_ty =
                convert_ml_type_to_cpp_type env tvars ty
              in
              let stored_cpp_ty =
                convert_ml_type_to_cpp_type env ~ns:tctx.method_self_ns tvars ty
              in
              let body_subst =
                match (bare_cpp_ty, stored_cpp_ty) with
                | Tglob (g1, [], _), Tshared_ptr (Tglob (g2, [], _))
                  when globref_equal g1 g2 && Table.is_coinductive g2 ->
                  Some (id, CPPderef (CPPvar id))
                | _ -> None
              in
              let param_cpp_ty =
                match body_subst with
                | Some _ -> Tref (Tmod (TMconst, stored_cpp_ty))
                | None when has_tany_in_type bare_cpp_ty ->
                  (* The ML type contains erased positions (std::any).  Use
                     [const auto&] so the C++ compiler deduces the concrete
                     type at the call site — explicit std::any in the param
                     type would block valid calls and prevent field accesses
                     inside the body from resolving to the concrete type. *)
                  Tref (Tmod (TMconst, Tauto))
                | None -> wrap_param_by_ownership ~is_owned:owned bare_cpp_ty
              in
              (param_cpp_ty, Some id, body_subst) )
            filtered_args_with_owned
        in
        let cpp_args =
          List.map (fun (ty, id, _) -> (ty, id)) cpp_arg_info
        in
        let saved_expected_lam = tctx.expected_ml_type_for_arg in
        let () =
          let rec strip_arrows n ty =
            if n = 0 then Some ty
            else match resolve_tmeta ty with
                 | Miniml.Tarr (_, cod) -> strip_arrows (n - 1) cod
                 | _ -> None
          in
          (match tctx.expected_ml_type_for_arg with
          | Some fn_ty ->
            (match strip_arrows n_all_params fn_ty with
            | Some cod ->
              (match resolve_tmeta cod with
              | Miniml.Tdummy _ | Miniml.Tunknown
              | Miniml.Tmeta {contents = None} -> ()
              | _ -> tctx.expected_ml_type_for_arg <- Some cod)
            | None -> ())
          | None -> ());
        in
        (* Generate the body, then check if the body returns a lambda (this
           happens when extract_cons_app generates curried partial constructor
           applications with an MLmagic barrier). If so, convert the returned
           lambda to capture by value to avoid dangling references to the outer
           lambda's parameters. *)
        let body_stmts = gen_stmts env (fun x -> Sreturn (Some x)) a in
        tctx.expected_ml_type_for_arg <- saved_expected_lam;
        let body_stmts =
          List.fold_left
            (fun stmts (_, _, subst) ->
              match subst with
              | Some (id, expr) -> List.map (local_var_subst_stmt id expr) stmts
              | None -> stmts )
            body_stmts
            cpp_arg_info
        in
        let body_stmts = return_captures_by_value body_stmts in
        (* When the lambda body is a standalone fixpoint (MLfix with no
           applied args), the fix represents a function value that would make
           this lambda curried — e.g. [fun x => fix f r := ...] generates
           [[=](x){auto f=...; return f;}] (1-arg returning fn) instead of
           the flat [[=](x,r){auto f=...; return f(r);}] (2-arg).  Fold the
           fix's own params into this lambda so the result is uncurried and
           directly compatible with [std::function<R(A,B)>] contexts. *)
        let cpp_args, body_stmts =
          match a with
          | MLfix (fix_x, _fix_ids, fix_funs, _)
            when List.length filtered_args <= 1 ->
            let fix_lam_params, _ = Mlutil.collect_lams fix_funs.(fix_x) in
            let fix_value_params =
              List.filter
                (fun (_, ty) -> not (isTdummy ty) && not (ml_type_is_void ty))
                fix_lam_params
            in
            ( match fix_value_params with
            | [] -> (cpp_args, body_stmts)
            | _ ->
              (* Only fold when body_stmts ends with a bare variable return,
                 i.e. the non-lifted ycomb path.  Lifted (polymorphic) fixes
                 are returned via a call expression and don't need folding. *)
              let last_is_var_return =
                match List.rev body_stmts with
                | Sreturn (Some (CPPvar _)) :: _ -> true
                | _ -> false
              in
              if not last_is_var_return then (cpp_args, body_stmts)
              else
                let extra_cpp_params =
                  List.mapi
                    (fun i (_, ml_ty) ->
                      let bare =
                        convert_ml_type_to_cpp_type env tvars ml_ty
                      in
                      let param_ty =
                        match bare with
                        | Tshared_ptr _ ->
                          Tref (Tmod (TMconst, bare))
                        | _ -> bare
                      in
                      (param_ty,
                       Some (Id.of_string (Printf.sprintf "_fea%d" i))) )
                    fix_value_params
                in
                let extra_args =
                  List.map
                    (fun (_, id_opt) -> CPPvar (Option.get id_opt))
                    extra_cpp_params
                in
                let rec modify_last_return = function
                  | [] -> []
                  | [Sreturn (Some e)] ->
                    [Sreturn (Some (CPPfun_call (e, List.rev extra_args)))]
                  | stmt :: rest -> stmt :: modify_last_return rest
                in
                (* The printer does List.rev on params, so put extra params
                   first (they will print last, after the outer lambda's own
                   params).  Within extra_cpp_params, reverse so that fix param
                   i prints at position i from the left (natural order). *)
                ( List.rev extra_cpp_params @ cpp_args,
                  modify_last_return body_stmts ) )
          | _ -> (cpp_args, body_stmts)
        in
        (* The return type annotation is left as [None]; loopify's
           [infer_saved_type] infers it from the body when computing frame
           struct field types.  Annotating here caused regressions for inner
           lambdas whose bodies return further closures (the inferred type
           became [std::function<...>] instead of the plain return type). *)
        CPPlambda (cpp_args, None, body_stmts, true) )
    in
    tctx.env_types <- saved_env_types;
    ( match filtered_args with
    | [] ->
      (* All lambda params are dummy (type abstractions). Skip the lambda
         wrapper and generate the body expression directly. However, when the
         body is a reference to a template function (detectable by having
         Tdummy-typed leading params in its ML type), we must wrap it in a
         generic forwarding lambda — C++ cannot pass overloaded or template
         function names as first-class values. *)
      ( match a with
      | MLglob (r, tys_inner) ->
        let ml_ty =
          match find_type_opt r with
          | Some ty -> ty
          | None -> Tunknown
        in
        let has_dummy_prefix = function
          | Tarr (t, _) when isTdummy t -> true
          | _ -> false
        in
        if has_dummy_prefix ml_ty then
          (* The function is a template that had type-level leading params. We
             need a forwarding lambda because C++ can't pass template function
             names as first-class values.

             To handle non-deducible template type params (like T2 that only
             appears in the return type), we use a C++20 template lambda with
             explicitly typed value parameters. This lets the compiler deduce
             type variables from the argument types, and we compute
             non-deducible tvars via std::invoke_result_t. *)
          let rec collect_non_dummy_types = function
            | Miniml.Tarr (t, rest) when not (isTdummy t) ->
              t :: collect_non_dummy_types rest
            | Miniml.Tarr (_, rest) -> collect_non_dummy_types rest
            | _ -> []
          in
          let non_dummy_param_tys = collect_non_dummy_types ml_ty in
          let n = List.length non_dummy_param_tys in
          let arg_names = List.init n (fun i -> field_param_name i) in
          let fn_name = Common.pp_global_name Term r in
          (* Collect all tvars from the ML type *)
          let all_tvars_set =
            List.fold_left
              collect_tvars_set
              IntSet.empty
              (non_dummy_param_tys @ [ml_ty])
          in
          let all_tvars = IntSet.elements all_tvars_set in
          (* Tvars deducible from non-function value params *)
          let value_param_tys =
            List.filter
              (fun t ->
                match t with
                | Miniml.Tarr _ -> false
                | _ -> true )
              non_dummy_param_tys
          in
          let deducible_set =
            List.fold_left collect_tvars_set IntSet.empty value_param_tys
          in
          let deducible_tvars = IntSet.elements deducible_set in
          let non_deducible_tvars =
            List.filter (fun i -> not (IntSet.mem i deducible_set)) all_tvars
          in
          (* Create tvar names for the template lambda *)
          let tvar_name i = "_T" ^ string_of_int i in
          (* Render an ML type as a C++ value type string using local tvar
             names. Inductives must stay bare values here; recursive ownership
             is represented only inside constructor fields. *)
          let rec render_ml_ty = function
            | Miniml.Tvar i | Miniml.Tvar' i -> tvar_name i
            | Miniml.Tarr (t1, t2) ->
              "std::function<" ^ render_ml_ty t2 ^ "(" ^ render_ml_ty t1 ^ ")>"
            | Miniml.Tglob (g, ts, _) when is_custom g ->
              (* Custom types may use %t0, %t1 placeholders for type args *)
              let custom_str = find_custom g in
              let rendered_ts = Array.of_list (List.map render_ml_ty ts) in
              let n_rendered = Array.length rendered_ts in
              let len = String.length custom_str in
              let buf = Buffer.create len in
              let rec subst i =
                if i >= len then
                  ()
                else if
                  i <= len - 3
                  && custom_str.[i] = '%'
                  && custom_str.[i + 1] = 't'
                  && custom_str.[i + 2] >= '0'
                  && custom_str.[i + 2] <= '9'
                then (
                  let digit_start = i + 2 in
                  let rec find_end j =
                    if j < len && custom_str.[j] >= '0' && custom_str.[j] <= '9'
                    then
                      find_end (j + 1)
                    else
                      j
                  in
                  let digit_end = find_end digit_start in
                  let idx =
                    int_of_string
                      (String.sub
                         custom_str
                         digit_start
                         (digit_end - digit_start) )
                  in
                  if idx < n_rendered then
                    Buffer.add_string buf rendered_ts.(idx)
                  else
                    Buffer.add_string
                      buf
                      (String.sub custom_str i (digit_end - i));
                  subst digit_end )
                else (
                  Buffer.add_char buf custom_str.[i];
                  subst (i + 1) )
              in
              subst 0;
              Buffer.contents buf
            | Miniml.Tdummy _ -> "std::any"
            | Miniml.Tglob (g, ts, _) ->
              let is_ind =
                match g with
                | GlobRef.IndRef _ -> true
                | _ -> false
              in
              let base =
                Common.pp_global_name (if is_ind then Type else Term) g
              in
              if ts = [] then
                base
              else
                base
                ^ "<"
                ^ String.concat ", " (List.map render_ml_ty ts)
                ^ ">"
            | _ -> "auto"
          in
          if non_deducible_tvars <> [] && not (IntSet.is_empty deducible_set)
          then
            (* There are non-deducible tvars — use template lambda with typed
               params. The first param (function type) uses auto&&, value params
               get specific types. *)
            let template_params =
              String.concat
                ", "
                (List.map (fun i -> "typename " ^ tvar_name i) deducible_tvars)
            in
            let params =
              List.mapi
                (fun i ty ->
                  match ty with
                  | Miniml.Tarr _ ->
                    (* Function-typed param: use auto&& *)
                    "auto &&" ^ List.nth arg_names i
                  | _ ->
                    (* Value param: use specific type for tvar deduction *)
                    "const " ^ render_ml_ty ty ^ " &" ^ List.nth arg_names i )
                non_dummy_param_tys
            in
            let params_str = String.concat ", " params in
            let fwd_args =
              String.concat
                ", "
                (List.mapi
                   (fun i ty ->
                     match ty with
                     | Miniml.Tarr _ ->
                       "std::forward<decltype("
                       ^ List.nth arg_names i
                       ^ ")>("
                       ^ List.nth arg_names i
                       ^ ")"
                     | _ -> List.nth arg_names i )
                   non_dummy_param_tys )
            in
            (* Build explicit type args: deducible tvars + non-deducible
               computed via invoke_result_t *)
            let deducible_args = List.map tvar_name deducible_tvars in
            let non_deducible_args =
              List.map
                (fun _i ->
                  (* Compute as invoke_result_t<F&, deducible_tvars&...> where F
                     is the first function param *)
                  let f_param = List.nth arg_names 0 in
                  let deducible_refs =
                    String.concat
                      ", "
                      (List.map (fun j -> tvar_name j ^ " &") deducible_tvars)
                  in
                  "std::invoke_result_t<decltype("
                  ^ f_param
                  ^ ") &, "
                  ^ deducible_refs
                  ^ ">" )
                non_deducible_tvars
            in
            let all_type_args = deducible_args @ non_deducible_args in
            let ty_args_str = "<" ^ String.concat ", " all_type_args ^ ">" in
            CPPraw
              ( "[]<"
              ^ template_params
              ^ ">("
              ^ params_str
              ^ ") -> decltype(auto) { return "
              ^ fn_name
              ^ ty_args_str
              ^ "("
              ^ fwd_args
              ^ "); }" )
          else
            (* No non-deducible tvars or no deducible tvars — simple
               forwarding *)
            let params_str =
              String.concat ", " (List.map (fun s -> "auto &&" ^ s) arg_names)
            in
            let fwd_args =
              String.concat
                ", "
                (List.map
                   (fun s -> "std::forward<decltype(" ^ s ^ ")>(" ^ s ^ ")")
                   arg_names )
            in
            (* Convert inner type args to C++ types, filtering out Tany *)
            let inner_tvars = get_current_type_vars () in
            let tys_cpp =
              List.map
                (convert_ml_type_to_cpp_type env inner_tvars)
                tys_inner
            in
            let tys_cpp = List.filter (fun t -> t <> Tany) tys_cpp in
            let ty_args_str =
              match tys_cpp with
              | [] -> ""
              | _ ->
                let rec render_ty = function
                  | Tvar (_, Some n) -> Id.to_string n
                  | Tvar (i, None) -> tvar_name i
                  | Tglob (r, [], _) -> Common.pp_global_name Type r
                  | Tglob (r, tys, _) ->
                    Common.pp_global_name Type r
                    ^ "<"
                    ^ String.concat ", " (List.map render_ty tys)
                    ^ ">"
                  | Tshared_ptr ty -> "std::shared_ptr<" ^ render_ty ty ^ ">"
                  | _ -> "auto"
                in
                "<" ^ String.concat ", " (List.map render_ty tys_cpp) ^ ">"
            in
            CPPraw
              ( "[]("
              ^ params_str
              ^ ") -> decltype(auto) { return "
              ^ fn_name
              ^ ty_args_str
              ^ "("
              ^ fwd_args
              ^ "); }" )
        else
          gen_expr env a
      | _ ->
        (* Body is not a template function ref — wrap in void thunk (old
           behavior). gen_expr env a might produce lambdas with [&] capture
           which fail at static scope, so we use the pre-built capture-free
           lambda f.

           Exception: in reified mode, when the lambda had void-typed params
           (from monadic result type erasure), keep the lambda as a function
           object rather than an IIFE. This is needed for itree_bind
           continuations which expect std::function, not the result of
           calling the function. *)
        if tctx.itree_mode = Reified
           && List.exists (fun (_, ty) -> ml_type_is_unit_or_void ty) lam_params then
          f
        else
          CPPfun_call (f, []) )
    | _ -> f )
  | MLglob (x, tys) when is_inline_custom x ->
    let tvars = get_current_type_vars () in
    let ty = find_type x in
    let ty = convert_ml_type_to_cpp_type env tvars ty in
    ( match ty with
    | Tfun (dom, cod) ->
      eta_fun env (MLglob (x, tys)) []
    | _ -> mk_cppglob x (build_template_params env tvars tys) )
  | MLglob (x, tys) ->
    let tvars = get_current_type_vars () in
    let tys_cpp =
      List.map
        (fun ty ->
          let t =
            convert_ml_type_to_cpp_type env tvars (type_simpl ty)
          in
          match t with
          | Tvar (_, None) when tvars <> [] ->
            Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
          | _ -> t )
        tys
    in
    let cglob = mk_cppglob x (filter_erased_type_args tys_cpp) in
    let needs_call =
      match find_type_opt x with
      | Some ml_ty when is_monadic_ml_type ml_ty -> true
      | Some _ when Table.is_cofixpoint x -> true
      | Some _ when Table.is_axiom_value x -> true
      | _ -> false
    in
    if needs_call then
      CPPfun_call (cglob, [])
    else
      cglob
  | MLcons (_ty, r, _ts)
    when match r with
         | GlobRef.ConstructRef ((kn, i), _) ->
           Table.is_numeral_inductive (GlobRef.IndRef (kn, i))
         | _ -> false ->
    (* Try to fold Peano numeral chain into an integer literal *)
    let ind_ref =
      match r with
      | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
      | _ -> CErrors.anomaly (Pp.str "try_fold_numeral: expected ConstructRef")
    in
    ( match Table.get_numeral_info ind_ref with
    | Some info ->
      ( match try_fold_numeral info ml_e with
      | Some n ->
        CPPraw (Common.render_template [("%n", string_of_int n)] info.Table.num_fmt)
      | None ->
        (* Peano folding failed.  Try binary positive folding for
           Z constructors: Zpos(xI(xO(...xH...))) / Zneg(...) chains
           can overflow unsigned int, so fold into INT64_C(n) literals. *)
        let z_folded =
          match (_ts, r) with
          | [inner], GlobRef.ConstructRef (_, cidx) ->
            try_fold_z_binary info cidx inner
          | _ -> None
        in
        ( match z_folded with
        | Some e -> e
        | None -> gen_expr_custom_cons env _ty r _ts ) )
    | None -> gen_expr_custom_cons env _ty r _ts )
  | MLcons (ty, r, ts) when is_custom r ->
    gen_expr_custom_cons env ty r ts
  | MLcons (ty, r, ts)
    when ts = []
         &&
         match r with
         | GlobRef.ConstructRef ((kn, _), _) ->
           is_enum_inductive (GlobRef.IndRef (kn, 0))
         | _ -> false ->
    let ind_ref, ctor_name =
      match r with
      | GlobRef.ConstructRef ((kn, i), cidx) ->
        ( GlobRef.IndRef (kn, i),
          Id.of_string (Table.enum_ctor_name_of_ref kn i cidx) )
      | _ ->
        CErrors.anomaly
          (Pp.str "gen_expr: enum constructor expected ConstructRef")
    in
    CPPenum_val (ind_ref, ctor_name)
  | MLcons (ty, r, ts) ->
    (* Setting [in_constructor_expr] makes unresolvable promoted vars (those
       NOT in [promoted_var_map]) fall back to [Tany] = [std::any].

       For non-record constructors (fds = []), we keep [promoted_var_map] so
       that template type annotations (e.g., SigT<..., Path<typename
       _tcI0::Obj>>) match the function's declared return type.

       For record constructors (fds != []), we clear [promoted_var_map]
       because record structs use erased types (std::any) for promoted fields,
       so lambda parameters assigned to record fields must also use std::any. *)
    let saved_promoted_cons = tctx.promoted_var_map in
    let saved_in_ctor_cons = tctx.in_constructor_expr in
    tctx.in_constructor_expr <- true;
    let fds = record_fields_of_type ty in
    let cons_result = match fds with
    | [] ->
      (* Propagate resolved types to nested list constructors before code
         generation. For List<nat> constructors like cons(1, cons(2, nil)), this
         ensures the nested nil gets List<nat> type instead of
         List<std::any>. *)
      let ts_updated =
        match ty with
        | Tglob (n, tys_orig, schema_opt) ->
          (* Only run type propagation for list constructors *)
          let is_list =
            try String.equal (Common.pp_global_name Type n) "list"
            with _ -> false
          in
          if not is_list then
            ts
          else (* Filter out index type args - only keep parameters *)
            let tys_filt =
              match n with
              | GlobRef.IndRef (kn, _) ->
                ( match Table.get_ind_num_param_vars_opt kn with
                | Some num_param_vars -> safe_firstn num_param_vars tys_orig
                | None -> tys_orig )
              | _ -> tys_orig
            in
            (* Resolve Tunknown from element types *)
            let has_unknown =
              List.exists
                (fun (t : ml_type) ->
                  match t with
                  | Tunknown -> true
                  | _ -> false )
                tys_filt
            in
            if
              has_unknown
              &&
              match ts with
              | [] -> false
              | _ -> true
            then
              let tys_resolved =
                List.map
                  (fun (t : ml_type) ->
                    match t with
                    | Tunknown ->
                      let first_elem =
                        List.find_opt
                          (fun a ->
                            match a with
                            | MLdummy _ -> false
                            | _ -> true )
                          ts
                      in
                      ( match first_elem with
                      | Some (MLmagic (MLcons (elem_ty, _, _))) -> elem_ty
                      | Some (MLcons (elem_ty, _, _)) -> elem_ty
                      | _ -> t )
                    | _ -> t )
                  tys_filt
              in
              (* Propagate resolved type to nested constructors *)
              let resolved_ty = Miniml.Tglob (n, tys_resolved, schema_opt) in
              let rec update_nested_ty ast =
                match ast with
                | MLcons (arg_typ, arg_c, arg_ts) ->
                  ( match arg_typ with
                  | Miniml.Tglob (arg_ref, arg_tys, _)
                    when GlobRef.CanOrd.equal arg_ref n
                         && List.exists
                              (fun t ->
                                match t with
                                | Miniml.Tunknown -> true
                                | _ -> false )
                              arg_tys ->
                    MLcons (resolved_ty, arg_c, List.map update_nested_ty arg_ts)
                  | _ ->
                    MLcons (arg_typ, arg_c, List.map update_nested_ty arg_ts) )
                | MLmagic inner -> MLmagic (update_nested_ty inner)
                | other -> other
              in
              List.map update_nested_ty ts
            else
              ts
        | _ -> ts
      in
      (* Generate: Type<temps>::ctor::Constructor_(args) *)
      let gen_ctor_call args =
        match ty with
        | Tglob (n, tys, _) ->
          (* Filter out index type args - only keep parameters *)
          let tys =
            match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys
              | None -> tys )
            | _ -> tys
          in
          (* Resolve Tunknown type args from constructor element types. For
             cons(elem, rest), elem's type provides the list's type param. *)
          let has_unknown =
            List.exists
              (fun (t : ml_type) ->
                match t with
                | Tunknown -> true
                | _ -> false )
              tys
          in
          let tys =
            if
              has_unknown
              &&
              match ts_updated with
              | [] -> false
              | _ -> true
            then
              List.map
                (fun (t : ml_type) ->
                  match t with
                  | Tunknown ->
                    (* Infer from first non-MLmagic/MLdummy constructor arg *)
                    let first_elem =
                      List.find_opt
                        (fun a ->
                          match a with
                          | MLdummy _ -> false
                          | _ -> true )
                        ts_updated
                    in
                    ( match first_elem with
                    | Some (MLmagic (MLcons (elem_ty, _, _))) -> elem_ty
                    | Some (MLcons (elem_ty, _, _)) -> elem_ty
                    | _ -> t )
                  | _ -> t )
                tys
            else
              tys
          in
          let tvars = get_current_type_vars () in
          let temps = build_template_params env tvars tys in
          (* For inductives with dependent parameters (e.g. sigT where the
             second param's type references the first), the dependent type arg
             extracts as a bare reference to the same inductive as an earlier
             arg.  Erase the duplicate to Tany to avoid mismatched template
             instantiations. *)
          let temps =
            if Table.has_dependent_params n then
              let expected_temps =
                let rec try_extract_temps cpp_ty =
                  match cpp_ty with
                  | Tglob (ret_r, ret_tys, _)
                    when Names.GlobRef.CanOrd.equal n ret_r
                         && List.length ret_tys = List.length temps ->
                    Some ret_tys
                  | Tnamespace (_, inner) -> try_extract_temps inner
                  | Tshared_ptr inner -> try_extract_temps inner
                  | Tglob (GlobRef.ConstRef kn, _, _) ->
                    (match Table.lookup_typedef_unchecked kn with
                     | Some ml_ty ->
                       let tvars = get_current_type_vars () in
                       let resolved = convert_ml_type_to_cpp_type env tvars ml_ty in
                       try_extract_temps resolved
                     | None -> None)
                  | _ -> None
                in
                match tctx.current_cpp_return_type with
                | Some rt -> try_extract_temps rt
                | None -> None
              in
              let normalize_erased_types =
                let rec go = function
                  | t when resolves_to_any_type t -> Tany
                  | Tfun (ps, r) -> Tfun (List.map go ps, go r)
                  | t -> t
                in go
              in
              match expected_temps with
              | Some exp_tys ->
                List.mapi (fun i t ->
                  let exp_t = normalize_erased_types (List.nth exp_tys i) in
                  if t <> exp_t && is_erased_type exp_t then Tany
                  else if t <> exp_t then exp_t
                  else t
                ) temps
              | None ->
                match tys with
                | [fst_ty; snd_ty] ->
                  let same_base = match fst_ty, snd_ty with
                    | Miniml.Tglob (g1, _, _), Miniml.Tglob (g2, sub2, _) ->
                      GlobRef.CanOrd.equal g1 g2 && sub2 = []
                    | _ -> false
                  in
                  if same_base then
                    match temps with
                    | [fst; _] -> [fst; Tany]
                    | _ -> temps
                  else temps
                | _ -> temps
            else temps
          in
          (* When all template params resolved to Tany (all type args were
             unresolved Tmeta), try to recover the concrete element type from
             an expected type threaded down from an enclosing constructor.
             Example: the pair (Fr [...], []) has a concrete pair annotation
             with second type arg list(parser_frame); when generating the nil
             for the second slot, expected_ml_type_for_arg = list(parser_frame),
             so we produce List<Parser_frame>::nil() instead of List<any>::nil(). *)
          let temps =
            (* Treat unnamed Tvars (Tvar(_, None)) as erased: they become
               std::any after tvar_erase_type, so we should try to recover
               the concrete type from the expected type annotation. *)
            let is_effectively_erased t =
              is_erased_type t || (match t with Tvar (_, None) -> true | _ -> false)
            in
            if List.for_all is_effectively_erased temps && temps <> [] then
              (* Resolve any metas in the expected type before matching.
                 The let-binding type may be Tmeta{Some Tglob(...)} so we
                 need to unwrap the meta to get the concrete Tglob. *)
              let expected_resolved = Option.map resolve_tmeta tctx.expected_ml_type_for_arg
              in
              (match expected_resolved with
              | Some (Miniml.Tglob (exp_n, exp_tys, _))
                when GlobRef.CanOrd.equal n exp_n
                     && List.length exp_tys = List.length tys ->
                (* Compute the recovered type with in_constructor_expr = false so
                   that promoted type vars resolve via promoted_var_map (giving
                   e.g. typename D::Defs::Parser_frame) rather than being erased
                   to std::any by the constructor-expression shortcut. *)
                let saved_ctor = tctx.in_constructor_expr in
                tctx.in_constructor_expr <- false;
                let recovered = build_template_params env tvars exp_tys in
                tctx.in_constructor_expr <- saved_ctor;
                if List.for_all (fun t -> not (is_erased_type t)) recovered
                then recovered
                else temps
              | _ -> temps)
            else temps
          in
          (* In dependent types, if a constructor arg at position i is
             [MLdummy Ktype] (a type-valued argument — e.g. [x : A] where
             [A : Type]), any template param at a later position j > i must
             also be erased to [std::any].
             Rationale: later params often have types that are functions of
             the erased type variable (e.g. [P x] for [sigT A P]).  When A
             is erased, [P x] is equally abstract and the concrete type
             inferred from the value argument (e.g. [bool] from [true : bool])
             would produce an incompatible template instantiation
             ([SigT<std::any, Bool0>] vs. the declared [SigT<std::any, std::any>]). *)
          let temps =
            let rec first_ktype_dummy i = function
              | [] -> max_int
              | (MLdummy Ktype | MLmagic (MLdummy Ktype)) :: _ -> i
              | _ :: rest -> first_ktype_dummy (i + 1) rest
            in
            let cutoff = first_ktype_dummy 0 ts_updated in
            let rec is_all_any = function
              | Tany -> true
              | Tglob (_, args, _) -> List.for_all is_all_any args
              | Tnamespace (_, inner) -> is_all_any inner
              | Tfun (ps, r) -> List.for_all is_all_any ps && is_all_any r
              | _ -> false
            in
            List.mapi (fun i t ->
              if i > cutoff && not (is_all_any t) then Tany else t
            ) temps
          in
          let ctor_struct = ctor_struct_name_of_ref r in
          let ind_type_name = Common.pp_global_name Type n in
          let fname =
            factory_name_of_ctor ~type_name:ind_type_name ctor_struct
          in
          (* Build: Type<temps>::factory(args) *)
          let type_expr = mk_cppglob n temps in
          CPPfun_call (CPPqualified (type_expr, Id.of_string fname), args)
        | _ ->
          (* Fallback for non-Tglob types *)
          let ctor_struct = ctor_struct_name_of_ref r in
          let fname = factory_name_of_ctor ctor_struct in
          CPPfun_call (CPPqualified (mk_cppglob r [], Id.of_string fname), args)
      in
      (* [CPPfun_call] stores args reversed; [List.rev_map] compensates.
         Erased proof/type args ([MLdummy]) produce [std::any{}] — the
         corresponding C++ parameter type is [std::any] and [CPPabort]
         would throw at runtime.  The same pattern is used in
         {!gen_expr_custom_cons} for inline-extracted constructors
         (e.g., [std::make_pair]). *)
      (* Generate constructor arguments with live move_dead_after so the move
         analysis from gen_tail_expr flows through.  Safety note: gen_tail_expr
         only marks variables that occur exactly once in the entire tail
         expression (nb_occur_match = 1), so a variable appearing in multiple
         constructor args is NOT in move_dead_after and cannot be moved twice. *)
      let gen_ctor_arg ?expected_ty e =
        match e with
        | MLdummy _ -> CPPconverting_ctor (Tany, [])
        | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
          wrap_void_call_as_value (gen_expr env e)
        | _ -> gen_expr ?expected_ty env e
      in
      (* When a constructor's field type is a type variable (Tvar i) that
         resolves to an owning pointer type (because T is in method_self_ns),
         the generated arg expression is a bare T value.  Wrap it so the
         field's stored type matches. *)
      (* All ML type arguments from the MLcons type — used to recover the
         actual type for fields erased to std::any when ind_nparams = 0. *)
      let ty_ml_tparams = match resolve_tmeta ty with
        | Tglob (_, tys_orig, _) -> tys_orig
        | _ -> []
      in
      let ctor_temps = match ty with
        | Tglob (n, tys_orig, _) ->
          let tys_filt = match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys_orig
              | None -> tys_orig )
            | _ -> tys_orig
          in
          let tvars = get_current_type_vars () in
          let temps = build_template_params env tvars tys_filt in
              if Table.has_dependent_params n then
            let rec try_extract_temps cpp_ty =
              match cpp_ty with
              | Tglob (ret_r, ret_tys, _)
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length temps ->
                Some ret_tys
              | Tnamespace (_, inner) -> try_extract_temps inner
              | Tshared_ptr inner -> try_extract_temps inner
              | Tglob (GlobRef.ConstRef kn, _, _) ->
                (match Table.lookup_typedef_unchecked kn with
                 | Some ml_ty ->
                   let tvars = get_current_type_vars () in
                   let resolved = convert_ml_type_to_cpp_type env tvars ml_ty in
                   try_extract_temps resolved
                 | None -> None)
              | _ -> None
            in
            let expected_temps =
              match tctx.current_cpp_return_type with
              | Some rt -> try_extract_temps rt
              | None -> None
            in
            let normalize_erased_types =
              let rec go = function
                | t when resolves_to_any_type t -> Tany
                | Tfun (ps, r) -> Tfun (List.map go ps, go r)
                | t -> t
              in go
            in
            match expected_temps with
            | Some exp_tys ->
              List.mapi (fun i t ->
                let exp_t = normalize_erased_types (List.nth exp_tys i) in
                let is_fully_erased_fun = match exp_t with
                  | Tfun (ps, r) ->
                    List.for_all (fun p -> p = Tany) ps && r = Tany
                  | _ -> false
                in
                if t <> exp_t && (is_erased_type exp_t || is_fully_erased_fun)
                then Tany
                else if t <> exp_t then exp_t
                else if is_fully_erased_fun then Tany
                else t
              ) temps
            | None -> temps
          else temps
        | _ -> []
      in
      let field_types_raw = match Table.get_ctor_ip_types_opt r with
        | Some ft -> ft
        | None -> [] in
      let field_types =
        List.filter (fun t -> not (Mlutil.isTdummy t)) field_types_raw in
      let wrap_if_needed_for_field ft ml_e expr =
        match ft with
        | Miniml.Tvar i | Miniml.Tvar' i ->
          ( try
            let ct = List.nth ctor_temps (i - 1) in
            match ct with
            | Tshared_ptr inner ->
              let inner_g = match inner with
                | Tglob (g, _, _) -> Some g | _ -> None in
              ( match inner_g with
              | Some g when Refset'.mem g tctx.method_self_ns ->
                CPPfun_call (CPPmk_shared inner, [expr])
              | _ -> expr )
            | ct when is_erased_type ct
                      || (match ct with
                          | Tglob (g, [], _) -> Table.is_erased_type_const g
                          | _ -> false) ->
              ( match expr with
              | CPPlambda (params, ret_ty_opt, body_stmts, cap) ->
                let tvars = get_current_type_vars () in
                let n_params = List.length params in
                let new_params = List.map (fun (orig_ty, orig_id) ->
                  let bare = strip_cpp_ref_const orig_ty in
                  if bare <> Tany then (Tmod (TMconst, Tref Tany), orig_id)
                  else (orig_ty, orig_id)
                ) params in
                let ml_concrete_param_tys =
                  let rec collect_lam_tys = function
                    | MLlam (_, ty, body) -> ty :: collect_lam_tys body
                    | MLmagic inner -> collect_lam_tys inner
                    | _ -> []
                  in
                  collect_lam_tys ml_e
                in
                let expand_ml_type ml_ty =
                  let abbrev r = match r with
                    | GlobRef.ConstRef kn -> Table.lookup_typedef_unchecked kn
                    | _ -> None
                  in
                  Mlutil.type_expand abbrev ml_ty
                in
                (* For custom list (deque) types, erase element types preserving
                   nested structure.  E.g., deque<pair<T1,T2>> → deque<pair<any,any>>,
                   deque<T> → deque<any>.  This matches the runtime representation:
                   when stored in any→any lambdas, pair elements are stored as
                   pair<any,any> (C++ converts T to any for each field). *)
                let erase_custom_list_elem t =
                  match t with
                  | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
                  | _ -> Tany
                in
                let erase_custom_list_elems = function
                  | Tglob (g, [elem_ty], ns) when is_list_global g && Table.is_custom g ->
                    Tglob (g, [erase_custom_list_elem elem_ty], ns)
                  | Tglob (g, _ :: _, ns) when is_list_global g && Table.is_custom g ->
                    Tglob (g, [Tany], ns)
                  | t -> t
                in
                let ml_body_ret_ty =
                  let rec get_body = function
                    | MLlam (_, _, body) -> get_body body
                    | MLmagic inner -> get_body inner
                    | body -> infer_ml_body_type body
                  in
                  get_body ml_e
                in
                let erase_inner_tparams = function
                  | Tglob (g, args, m) ->
                    let erase_t = function
                      | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
                      | _ -> Tany
                    in
                    Tglob (g, List.map erase_t args, m)
                  | t -> t
                in
                let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
                  match orig_id with
                  | None -> None
                  | Some id ->
                    let bare = strip_cpp_ref_const (fst (List.nth params j)) in
                    if bare = Tany then None
                    else
                      let concrete_ty =
                        let from_annotation =
                          match List.nth_opt ml_concrete_param_tys j with
                          | Some ml_ty ->
                            let expanded = expand_ml_type ml_ty in
                            let ct = convert_ml_type_to_cpp_type env tvars expanded in
                            erase_custom_list_elems (strip_cpp_ref_const ct)
                          | None -> bare
                        in
                        if not (resolves_to_any_type from_annotation) then from_annotation
                        else begin
                          let ret_ct = match ml_body_ret_ty with
                            | Some ret_ml ->
                              let ct = convert_ml_type_to_cpp_type env tvars ret_ml in
                              strip_cpp_ref_const ct
                            | None -> Tany
                          in
                          erase_inner_tparams ret_ct
                        end
                      in
                      if resolves_to_any_type concrete_ty then None
                      else
                        let any_id = Id.of_string ("_any_" ^ Id.to_string id) in
                        Some (id, any_id, concrete_ty)
                ) (List.mapi (fun idx p -> (idx, p)) new_params) in
                let new_body =
                  List.fold_left (fun stmts (orig_id, any_id, concrete_ty) ->
                    let cast_stmt = Sasgn (orig_id, Some concrete_ty,
                      CPPany_cast (concrete_ty, CPPvar any_id)) in
                    cast_stmt :: stmts
                  ) body_stmts (List.rev cast_bindings)
                in
                let renamed_params = List.map (fun (ty, id_opt) ->
                  match id_opt with
                  | Some id ->
                    (match List.find_opt (fun (oid, _, _) -> Id.equal oid id) cast_bindings with
                     | Some (_, any_id, _) -> (ty, Some any_id)
                     | None -> (ty, id_opt))
                  | None -> (ty, id_opt)
                ) new_params in
                let erased_ret_ty =
                  let actual_ml_ty =
                    try List.nth ty_ml_tparams (i - 1)
                    with _ -> Miniml.Tunknown
                  in
                  match strip_tarr_n n_params (resolve_tmeta actual_ml_ty) with
                  | Some ret_ml ->
                    let r = convert_ml_type_to_cpp_type env tvars ret_ml in
                    strip_cpp_ref_const r
                  | None -> Tany
                in
                let new_ret_ty = match ret_ty_opt with
                  | Some _ -> ret_ty_opt
                  | None -> if erased_ret_ty <> Tany then Some erased_ret_ty else None
                in
                let erased_param_tys = List.map (fun _ -> Tany) renamed_params in
                let new_lambda = CPPlambda (renamed_params, new_ret_ty, new_body, cap) in
                let func_ty = Tfun (safe_firstn n_params erased_param_tys, erased_ret_ty) in
                CPPconverting_ctor (func_ty, [new_lambda])
              | _ ->
                (* When a custom list literal (e.g. deque<Val>) is stored in a
                   std::any field, regenerate it with wrap_for_any_param=true so
                   elements are erased to std::any.  The stored value becomes
                   deque<any>, matching what any_cast<deque<any>> expects when
                   consuming through the erased field. *)
                let rec is_custom_list_cons = function
                  | MLcons (_, GlobRef.ConstructRef ((kn, _), _), _) ->
                    let ind = GlobRef.IndRef (kn, 0) in
                    is_list_global ind && Table.is_custom ind
                  | MLmagic inner -> is_custom_list_cons inner
                  | _ -> false
                in
                if is_custom_list_cons ml_e then begin
                  let saved_wrap = tctx.wrap_for_any_param in
                  tctx.wrap_for_any_param <- true;
                  let new_expr = gen_ctor_arg ml_e in
                  tctx.wrap_for_any_param <- saved_wrap;
                  new_expr
                end else begin
                  (* A non-lambda FUNCTION value (e.g. a forwarded callback
                     parameter [f]) stored into an erased field must be wrapped
                     into the canonical [std::function<std::any(std::any...)>]
                     representation that the application side reads back with
                     [any_cast<std::function<std::any(std::any)>>] (see
                     [eta_fun]'s [callee_is_bare_any] branch).  Storing the raw
                     closure makes the [std::any] hold the bare lambda type, so
                     that [any_cast] throws at runtime.

                     The domain/codomain of such a function are typically
                     value-dependent (erased to [std::any] in the generic ML
                     type), so the concrete argument types needed for the
                     [any_cast] inside the adapter are only known at C++
                     instantiation.  Rather than reconstruct them here, defer to
                     the [crane_erase_fn] runtime helper, which uses
                     [std::function] CTAD to deduce the callable's signature and
                     builds the [std::function<std::any(std::any...)>] adapter
                     (unbox each argument, box the result). *)
                  if ml_expr_is_function_value ml_e then begin
                    (* Wrap via the [crane_erase_fn] runtime helper (emitted as
                       [#include "crane_fn.h"] in the header preamble). *)
                    Table.mark_needs_erase_fn ();
                    CPPfun_call
                      (CPPvar (Id.of_string "crane_erase_fn"), [expr])
                  end else expr
                end )
            | Tfun (param_tys, _ret_ty) when List.exists (fun t -> t = Tany) param_tys ->
              ( match expr with
              | CPPlambda (params, ret_ty_opt, body_stmts, cap) ->
                let tvars = get_current_type_vars () in
                let n_params = List.length params in
                let new_params = List.mapi (fun j (orig_ty, orig_id) ->
                  if j < List.length param_tys && List.nth param_tys j = Tany then
                    let bare = strip_cpp_ref_const orig_ty in
                    if bare <> Tany then (Tmod (TMconst, Tref Tany), orig_id)
                    else (orig_ty, orig_id)
                  else (orig_ty, orig_id)
                ) params in
                let ml_body_ret_ty =
                  let rec get_body = function
                    | MLlam (_, _, body) -> get_body body
                    | MLmagic inner -> get_body inner
                    | body -> infer_ml_body_type body
                  in
                  get_body ml_e
                in
                let ml_concrete_param_tys =
                  let rec collect_lam_tys = function
                    | MLlam (_, ty, body) -> ty :: collect_lam_tys body
                    | MLmagic inner -> collect_lam_tys inner
                    | _ -> []
                  in
                  collect_lam_tys ml_e
                in
                let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
                  if j < List.length param_tys && List.nth param_tys j = Tany then
                    match orig_id with
                    | None -> None
                    | Some id ->
                      let concrete_ty =
                        let from_annotation =
                          match List.nth_opt ml_concrete_param_tys j with
                          | Some ml_ty ->
                            let ct = convert_ml_type_to_cpp_type env tvars ml_ty in
                            strip_cpp_ref_const ct
                          | None -> Tany
                        in
                        if not (resolves_to_any_type from_annotation) then
                          from_annotation
                        else begin
                          let ret_ct = match ml_body_ret_ty with
                          | Some ret_ml ->
                            let ct = convert_ml_type_to_cpp_type env tvars ret_ml in
                            strip_cpp_ref_const ct
                          | None -> Tany
                          in
                          let erase_inner_tparams = function
                            | Tglob (g, args, m) ->
                              let erase_t = function
                                | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
                                | _ -> Tany
                              in
                              Tglob (g, List.map erase_t args, m)
                            | t -> t
                          in
                          erase_inner_tparams ret_ct
                        end
                      in
                      if resolves_to_any_type concrete_ty then None
                      else
                        let any_id = Id.of_string ("_any_" ^ Id.to_string id) in
                        Some (id, any_id, concrete_ty)
                  else None
                ) (List.mapi (fun idx p -> (idx, p)) new_params) in
                let new_body =
                  List.fold_left (fun stmts (orig_id, any_id, concrete_ty) ->
                    let cast_stmt = Sasgn (orig_id, Some concrete_ty,
                      CPPany_cast (concrete_ty, CPPvar any_id)) in
                    cast_stmt :: stmts
                  ) body_stmts (List.rev cast_bindings)
                in
                let renamed_params = List.map (fun (ty, id_opt) ->
                  match id_opt with
                  | Some id ->
                    (match List.find_opt (fun (oid, _, _) -> Id.equal oid id) cast_bindings with
                     | Some (_, any_id, _) -> (ty, Some any_id)
                     | None -> (ty, id_opt))
                  | None -> (ty, id_opt)
                ) new_params in
                let erased_param_tys = List.map (fun _ -> Tany) renamed_params in
                let erased_ret_ty =
                  let actual_ml_ty =
                    try List.nth ty_ml_tparams (i - 1)
                    with _ -> Miniml.Tunknown
                  in
                  match strip_tarr_n n_params (resolve_tmeta actual_ml_ty) with
                  | Some ret_ml ->
                    let r = convert_ml_type_to_cpp_type env tvars ret_ml in
                    strip_cpp_ref_const r
                  | None -> Tany
                in
                let new_ret_ty = match ret_ty_opt with
                  | Some _ -> ret_ty_opt
                  | None -> if erased_ret_ty <> Tany then Some erased_ret_ty else None
                in
                let new_lambda = CPPlambda (renamed_params, new_ret_ty, new_body, cap) in
                let func_ty = Tfun (safe_firstn n_params erased_param_tys, erased_ret_ty) in
                CPPconverting_ctor (func_ty, [new_lambda])
              | _ -> expr )
            | _ -> expr
            with Failure _ | Invalid_argument _ ->
              (* Field type index is beyond ctor_temps — this field is erased
                 to std::any.  If the expression is a lambda, wrap it in
                 std::function so that std::any stores the type-erased wrapper
                 and any_cast<std::function<...>> can recover it. *)
              match expr with
              | CPPlambda (params, ret_ty_opt, body_stmts, _) ->
                let param_types = List.map (fun (ty, _) ->
                  strip_cpp_ref_const ty) params in
                (* Build a name→type map from the lambda's parameter list. *)
                let param_env =
                  List.filter_map
                    (fun (ty, id_opt) ->
                      Option.map (fun id -> (id, strip_cpp_ref_const ty)) id_opt)
                    params
                in
                (* Infer return type from the first Sreturn in the body. *)
                let rec infer_ret_from_expr = function
                  | CPPvar id ->
                    List.assoc_opt id param_env
                  | CPPbinop (_, a, b) ->
                    ( match infer_ret_from_expr a with
                    | Some _ as r -> r
                    | None -> infer_ret_from_expr b )
                  | _ -> None
                in
                let rec infer_ret_from_stmts = function
                  | [] -> None
                  | Sreturn (Some e) :: _ -> infer_ret_from_expr e
                  | Sif (_, t, f) :: rest ->
                    ( match infer_ret_from_stmts t with
                    | Some _ as r -> r
                    | None ->
                      match infer_ret_from_stmts f with
                      | Some _ as r -> r
                      | None -> infer_ret_from_stmts rest )
                  | Sblock ss :: rest ->
                    ( match infer_ret_from_stmts ss with
                    | Some _ as r -> r
                    | None -> infer_ret_from_stmts rest )
                  | _ :: rest -> infer_ret_from_stmts rest
                in
                let ret_ty = match ret_ty_opt with
                  | Some ty -> strip_cpp_ref_const ty
                  | None ->
                    (* Try the lambda body first (works when the return expression
                       contains a lambda parameter). *)
                    ( match infer_ret_from_stmts body_stmts with
                    | Some ty -> ty
                    | None ->
                      (* Fall back: recover the return type from the MLcons type
                         arguments.  For [ft = Tvar i], the actual ML type is
                         [ty_ml_tparams.(i-1)] = e.g. [nat -> nat].  Strip as many
                         arrow levels as there are C++ params to get the codomain.
                         This works for type-PARAMETER inductives (ind_nparams > 0);
                         for type-INDEXED inductives the tys list may be empty. *)
                      let actual_ml_ty =
                        try List.nth ty_ml_tparams (i - 1)
                        with Failure _ | Invalid_argument _ ->
                          Tmeta {Miniml.id = -1; Miniml.contents = None}
                      in
                      let n_params = List.length param_types in
                      let tvars = get_current_type_vars () in
                      match strip_tarr_n n_params (resolve_tmeta actual_ml_ty) with
                      | Some ret_ml ->
                        let r = convert_ml_type_to_cpp_type env tvars ret_ml in
                        strip_cpp_ref_const r
                      | None -> Tvoid )
                in
                CPPconverting_ctor (Tfun (param_types, ret_ty), [expr])
              | _ -> expr )
        | ft ->
          (* Handle arrow types containing erased type variables.
             E.g. field type Tarr(Tvar 1, Tglob(nat)) where Tvar 1 is erased:
             the concrete lambda [](uint64_t x){return x*x;} must become
             [](std::any _a0){return any_cast<uint64_t>(_a0) * any_cast<uint64_t>(_a0);}
             so it matches the factory param std::function<uint64_t(std::any)>. *)
          let tvar_is_erased i =
            try match List.nth ctor_temps (i - 1) with
              | Tany -> true | _ -> false
            with Failure _ | Invalid_argument _ -> true
          in
          let rec ft_has_erased_tvar = function
            | Miniml.Tvar i | Miniml.Tvar' i -> tvar_is_erased i
            | Miniml.Tunknown -> true
            | Miniml.Tarr (a, b) -> ft_has_erased_tvar a || ft_has_erased_tvar b
            | _ -> false
          in
          ( match ft, expr with
          | Miniml.Tarr _, CPPlambda (params, ret_ty_opt, body_stmts, cap)
            when ft_has_erased_tvar ft ->
            let tvars = get_current_type_vars () in
            let rec collect_tarr = function
              | Miniml.Tarr (a, rest) ->
                let (ps, r) = collect_tarr rest in (a :: ps, r)
              | t -> ([], t)
            in
            let (ml_param_tys, ml_ret_ty) = collect_tarr ft in
            let erase_ml_ty t =
              match t with
              | Miniml.Tvar i | Miniml.Tvar' i when tvar_is_erased i -> Tany
              | Miniml.Tunknown -> Tany
              | _ -> convert_ml_type_to_cpp_type env tvars t
            in
            let erased_param_tys = List.map erase_ml_ty ml_param_tys in
            let erased_ret_ty = erase_ml_ty ml_ret_ty in
            let n_params = List.length params in
            (* Build new params with std::any for erased positions, and add
               any_cast let-bindings for each erased parameter at the start
               of the body. *)
            let new_params = List.mapi (fun j (orig_ty, orig_id) ->
              let erased_ty =
                if j < List.length erased_param_tys
                   && List.nth erased_param_tys j = Tany
                   && strip_cpp_ref_const orig_ty <> Tany
                then
                  (* Replace concrete type with std::any, preserving const ref *)
                  Tmod (TMconst, Tref Tany)
                else orig_ty
              in
              (erased_ty, orig_id)
            ) params in
            (* Extract concrete parameter types from the MiniML lambda *)
            let ml_concrete_param_tys =
              let rec collect_lam_tys = function
                | MLlam (_, ty, body) -> ty :: collect_lam_tys body
                | MLmagic inner -> collect_lam_tys inner
                | _ -> []
              in
              collect_lam_tys ml_e
            in
            let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
              if j < List.length erased_param_tys
                 && List.nth erased_param_tys j = Tany then
                match orig_id with
                | Some id ->
                  (* Get concrete type from ML lambda param, not C++ lambda *)
                  let concrete_ty =
                    match List.nth_opt ml_concrete_param_tys j with
                    | Some ml_ty ->
                      let ct = convert_ml_type_to_cpp_type env tvars ml_ty in
                      strip_cpp_ref_const ct
                    | None -> strip_cpp_ref_const (fst (List.nth params j))
                  in
                  if concrete_ty <> Tany && concrete_ty <> Tauto then
                    let any_param_id = Id.of_string
                      ("_any_" ^ Id.to_string id) in
                    Some (j, id, any_param_id, concrete_ty)
                  else None
                | None -> None
              else None
            ) (List.mapi (fun j p -> (j, p)) params) in
            let new_params = List.mapi (fun j (ty, id) ->
              match List.find_opt (fun (j', _, _, _) -> j = j') cast_bindings with
              | Some (_, _, any_id, _) -> (ty, Some any_id)
              | None -> (ty, id)
            ) new_params in
            let cast_stmts = List.map (fun (_, orig_id, any_id, concrete_ty) ->
              Sasgn (orig_id, Some concrete_ty,
                CPPany_cast (concrete_ty, CPPvar any_id))
            ) cast_bindings in
            let new_body = cast_stmts @ body_stmts in
            let new_ret_ty = match ret_ty_opt with
              | Some _ -> ret_ty_opt
              | None -> if erased_ret_ty <> Tany then Some erased_ret_ty else None
            in
            let new_lambda = CPPlambda (new_params, new_ret_ty, new_body, cap) in
            let func_ty = Tfun (safe_firstn n_params erased_param_tys, erased_ret_ty) in
            CPPconverting_ctor (func_ty, [new_lambda])
          | _ -> expr )
      in
      let gen_and_wrap i e =
        let saved_ret = tctx.current_cpp_return_type in
        tctx.current_cpp_return_type <- None;
        let ft_opt =
          try Some (List.nth field_types i)
          with Failure _ | Invalid_argument _ -> None
        in
        (* A constructor field with a CONCRETE type receiving an argument that
           is an erased ([std::any]) pattern variable (e.g. a leaf destructured
           from a deeply-erased [pair<any,any>] via [any_cast]) needs a final
           [any_cast<concrete>] — otherwise the bare [std::any] is forwarded
           straight into a concrete-typed factory parameter and fails to
           compile.  Thread the field's concrete C++ type as the expected type
           so the erased-[MLrel] path (see [gen_expr]'s [MLrel] case) inserts
           the cast.  [Tvar]/[Tvar'] fields are left to
           [wrap_if_needed_for_field], which handles the erased-field cases. *)
        let expected_for_arg =
          match ft_opt with
          | Some ft ->
            let is_erased_rel =
              match e with
              | MLrel j | MLmagic (MLrel j) ->
                Escape.IntSet.mem j tctx.cpp_erased_env
              | _ -> false
            in
            ( match ft with
            | Miniml.Tvar _ | Miniml.Tvar' _ -> None
            | _ when is_erased_rel ->
              let tvars = get_current_type_vars () in
              let ct = convert_ml_type_to_cpp_type env tvars ft in
              if is_erased_type ct then None else Some ct
            | _ -> None )
          | None -> None
        in
        let expr = gen_ctor_arg ?expected_ty:expected_for_arg e in
        tctx.current_cpp_return_type <- saved_ret;
        match ft_opt with
        | Some ft -> wrap_if_needed_for_field ft e expr
        | None -> expr
      in
      gen_ctor_call (List.rev (List.mapi gen_and_wrap ts_updated))
    | _ ->
      (* Records: clear [promoted_var_map] because record structs use erased
         types (std::any) for promoted fields.  Lambda parameters assigned to
         record fields must use std::any to match the field types. *)
      tctx.promoted_var_map <- [];
      let nstempmod args =
        match ty with
        | Tglob (n, tys, _) ->
          (* Filter out index type args - only keep parameters *)
          let tys =
            match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys
              | None -> tys )
            | _ -> tys
          in
          let temps = build_template_params env [] tys in
          if Table.is_coinductive n then
            CPPfun_call
              (CPPmk_shared (Tglob (n, temps, [])), [CPPstruct (n, temps, args)])
          else
            (* Value-type records: direct construction, no make_shared *)
            CPPstruct (n, temps, args)
        | _ ->
          CErrors.anomaly
            (Pp.str
               "gen_expr: non-record MLcons with matching type expected Tglob" )
      in
      (* Defense-in-depth: same safeguard as for non-record constructors above *)
      let saved_dead = tctx.move_dead_after in
      tctx.move_dead_after <- Escape.IntSet.empty;
      let record_arg_exprs =
        let field_types_rec =
          match Table.get_ctor_ip_types_opt r with
          | Some ft -> ft
          | None -> []
        in
        let tvars = get_current_type_vars () in
        (* A record field with a CONCRETE type receiving an argument that is an
           erased ([std::any]) pattern variable (e.g. a leaf destructured from a
           deeply-erased [pair<any,any>]) needs a final [any_cast<concrete>] —
           otherwise the bare [std::any] is aggregate-brace-initialized into a
           concrete field and fails to compile.  Thread the field's concrete C++
           type as the expected type so the erased-[MLrel] path (see [gen_expr]'s
           [MLrel] case) inserts the cast.  This mirrors the equivalent handling
           for value-type (variant) constructors in [gen_and_wrap]. *)
        let expected_for_field i e =
          match List.nth_opt field_types_rec i with
          | Some ft ->
            let is_erased_rel =
              match e with
              | MLrel j | MLmagic (MLrel j) ->
                Escape.IntSet.mem j tctx.cpp_erased_env
              | _ -> false
            in
            ( match ft with
            | Miniml.Tvar _ | Miniml.Tvar' _ -> None
            | _ when is_erased_rel ->
              let ct = convert_ml_type_to_cpp_type env tvars ft in
              if is_erased_type ct then None else Some ct
            | _ -> None )
          | None -> None
        in
        let base_args =
          List.mapi
            (fun i e ->
              match e with
              | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
                wrap_void_call_as_value (gen_expr env e)
              | _ -> gen_expr ?expected_ty:(expected_for_field i e) env e)
            ts
        in
        match ty with
        | Tglob (n, _, _) ->
          let field_types = field_types_rec in
          List.mapi
            (fun i expr ->
              match List.nth_opt field_types i with
              | Some ft ->
                let storage_ty =
                  convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton n) tvars ft
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env tvars ft
                in
                wrap_storage_expr ~storage_ty ~api_ty expr
              | None -> expr)
            base_args
        | _ -> base_args
      in
      let result = nstempmod record_arg_exprs in
      tctx.move_dead_after <- saved_dead;
      result
    in
    tctx.promoted_var_map <- saved_promoted_cons;
    tctx.in_constructor_expr <- saved_in_ctor_cons;
    cons_result
  | MLcase (typ, t, pv) when is_custom_match pv ->
    let tvars = get_current_type_vars () in
    let iife_ret =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = convert_ml_type_to_cpp_type env tvars branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_unit (ml_result_type branch_rty)
      then Tvoid else r
    in
    let saved_ret = tctx.current_cpp_return_type in
    if iife_ret = Tvoid then
      tctx.current_cpp_return_type <- Some Tvoid;
    let stmts = gen_custom_cpp_case env (fun x -> Sreturn (Some x)) typ t pv in
    tctx.current_cpp_return_type <- saved_ret;
    CPPfun_call (CPPlambda ([], Some iife_ret, stmts, false), [])
  | MLcase (typ, t, pv)
    when (not (record_fields_of_type typ == [])) && Array.length pv == 1 ->
    let ids, r, pat, body = pv.(0) in
    let n = List.length ids in
    let is_typeclass = Table.is_typeclass_type typ in
    (* Build lists that correctly account for erased fields.
       record_fields_of_type includes None entries for erased fields; ids only
       contains non-erased bindings. So MLrel i refers to the i-th non-erased
       field. We filter out None entries for correct indexing. *)
    let all_fields = record_fields_of_type typ in
    let non_erased_fields = List.filter_map Fun.id all_fields in
    let all_field_types =
      match typ with
      | Tglob (r, _, _) -> Table.record_field_types r
      | _ -> []
    in
    let non_erased_field_types =
      filter_value_types all_field_types
    in
    let record_ref_opt =
      match typ with Tglob (r, _, _) -> Some r | _ -> None
    in
    let wrap_record_field_to_api idx access =
      match (record_ref_opt, List.nth_opt non_erased_field_types idx) with
      | Some record_ref, Some ml_ty ->
        let tvars = get_current_type_vars () in
        let storage_ty =
          convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton record_ref)
            tvars
            ml_ty
        in
        let api_ty =
          convert_ml_type_to_cpp_type env tvars ml_ty
        in
        wrap_api_expr ~storage_ty ~api_ty access
      | _ -> access
    in
    (* For type classes, use qualified access (::) instead of arrow (->) since
       type class instances are template type parameters, not runtime values *)
    let make_field_access base_expr fld =
      if is_typeclass then
        let fld_name = Id.of_string (Common.pp_global_name Term fld) in
        CPPqualified (base_expr, fld_name)
      else
        CPPget' (base_expr, fld)
    in
    (* Strip MLmagic wrappers from the body — promoted dependent records may
       wrap field references in MLmagic due to Tvar/Tglob mismatches *)
    let body' =
      match body with
      | MLmagic b -> b
      | b -> b
    in
    ( match body' with
    | MLrel i when i <= n ->
      let fld =
        try Some (List.nth non_erased_fields (n - i)) with _ -> None
      in
      ( match fld with
      | Some fld ->
        let access = make_field_access (gen_expr env t) fld in
        let access = wrap_record_field_to_api (n - i) access in
        if is_typeclass then
          (* For typeclasses, non-function value fields (like m_id : carrier)
             are generated as nullary static methods, so we need () to call
             them *)
          let fld_ty =
            try List.nth non_erased_field_types (n - i)
            with _ -> Miniml.Tunknown
          in
          let is_value_field =
            match fld_ty with
            | Miniml.Tarr _ -> false
            | _ -> true
          in
          if is_value_field then
            CPPfun_call (access, [])
          else
            access
        else
          access
      | _ ->
        CErrors.anomaly (Pp.str "record field index out of bounds") )
    | MLapp ((MLrel i | MLmagic (MLrel i)), args) when i <= n ->
      let fld =
        try Some (List.nth non_erased_fields (n - i)) with _ -> None
      in
      let _, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      ( match fld with
      (* [CPPfun_call] expects args in reverse order; [List.rev_map] both
         converts and reverses.  Filter [MLdummy] args — these are erased type
         parameters (e.g. [A : Type] in [f : forall A, A -> A]) with no C++
         runtime representation.  When the field's codomain erases to [std::any]
         (see [ml_codomain_erases_to_any]), wrap the result with
         [std::any_cast<T>] to recover the caller's concrete return type. *)
      | Some fld ->
        let value_args =
          List.filter (fun a -> match a with MLdummy _ -> false | _ -> true) args
        in
        let call =
          CPPfun_call
            ( make_field_access (gen_expr env t) fld,
              List.rev_map (gen_expr env') value_args )
        in
        let fld_ty_opt =
          try Some (List.nth non_erased_field_types (n - i)) with _ -> None
        in
        let n_value_args = List.length value_args in
        let erased_cod =
          match fld_ty_opt with
          | Some ft -> ml_codomain_erases_to_any n_value_args ft
          | None -> false
        in
        ( match (erased_cod, tctx.current_cpp_return_type) with
        | (true, Some ty) when ty <> Tany && not (is_erased_type ty) && ty <> Tvoid ->
          CPPany_cast (ty, call)
        | _ -> call )
      | _ -> CErrors.anomaly (Pp.str "record field index out of bounds") )
    | _ ->
      (* Destructure record fields into local variables, then evaluate the body
         in an IIFE. push_vars' may rename variables to avoid shadowing
         identifiers already in scope — e.g. when a record has a field
         [rn_value] and the enclosing struct also has an accessor method
         [rn_value], push_vars' renames the local to [rn_value0].

         We must use the renamed ids from push_vars' for the assignment
         declarations so that they are consistent with env' (which the body is
         generated under). Otherwise the declarations would use the original
         names while the body references the renamed ones. *)
      let renamed_ids, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      (* renamed_ids is in reversed order (from List.rev_map above). Reverse it
         back so it aligns with ids (constructor / field order). *)
      let renamed_ids_fwd = List.rev renamed_ids in
      let asgns =
        List.concat_map
          (fun (i, ((renamed_name, _), (_, ty))) ->
            let fld =
              try Some (List.nth non_erased_fields i) with _ -> None
            in
            let e =
              match fld with
              | Some fld -> make_field_access (gen_expr env t) fld
              | _ -> CErrors.anomaly (Pp.str "record field index out of bounds")
            in
            let e =
              match typ with
              | Tglob (record_ref, _, _) ->
                let storage_ty =
                  convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton record_ref)
                    []
                    ty
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env [] ty
                in
                wrap_api_expr ~storage_ty ~api_ty e
              | _ -> e
            in
            let decl_ty =
              convert_ml_type_to_cpp_type env [] ty
            in
            match lift_iife_assignment renamed_name decl_ty e with
            | Some stmts -> stmts
            | None -> [Sasgn (renamed_name, Some decl_ty, e)])
          (List.mapi (fun i x -> (i, x)) (List.combine renamed_ids_fwd ids))
      in
      CPPfun_call
        ( CPPlambda
            ( [],
              None,
              asgns @ gen_stmts env' (fun x -> Sreturn (Some x)) body,
              false ),
          [] ) )
    (* Known limitation: simultaneous pattern matching on record fields is not
       supported — each field is destructured individually. *)
  | MLcase (typ, t, pv) when lang () == Cpp -> gen_cpp_case typ t env pv
  | MLletin (_, ty, _, _) as a ->
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLfix _ as a ->
    (* Bare fixpoint in expression context — wrap in IIFE, delegate to
       gen_stmts. *)
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLstring s -> CPPstring s
  | MLuint x -> CPPuint x
  | MLfloat f -> CPPfloat f
  | MLparray (elems, def) ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    CPPparray (elems, def)
  | MLmagic t ->
    let inner = gen_expr env t in
    ( match expected_ty with
      | Some ty when not (is_erased_type ty) && ty <> Tvoid
                    && not (match ty with Tglob (g, _, _) -> Table.is_erased_type_const g | _ -> false) ->
        let is_cpp_erased_var = match t with
          | MLrel i -> Escape.IntSet.mem i tctx.cpp_erased_env
          | _ -> false
        in
        if is_cpp_erased_var then
          let erase_top_args = function
            | Tglob (g, [elem_ty], _) when is_list_global g && Table.is_custom g ->
              let erased_elem = erase_type_to_any elem_ty in
              Tglob (g, [erased_elem], [])
            | Tglob (g, args, ns) when args <> [] ->
              Tglob (g, List.map erase_type_to_any args, ns)
            | Tnamespace (ns_g, inner_ty) ->
              Tnamespace (ns_g, erase_type_to_any inner_ty)
            | t -> t
          in
          let cast_ty = erase_top_args ty in
          ( match inner with
            | CPPany_cast _ -> inner
            | _ -> CPPany_cast (cast_ty, inner) )
        else if ml_expr_is_erased env t then
          ( match inner with
            | CPPany_cast _ -> inner
            | _ -> CPPany_cast (ty, inner) )
        else inner
      | _ -> inner )
  | MLdummy _ ->
    (* Erased proof or type argument.  [CPPabort] is safe here because this
       case only fires in dead code positions (absurd match branches).
       Evaluated positions — constructor args and custom-constructor args —
       are handled before reaching this point: see [gen_ctor_arg] in the
       [MLcons] case and in {!gen_expr_custom_cons}, which produce
       [std::any{}] instead.  The reuse optimization in {!gen_cpp_case}
       skips [MLdummy] fields entirely. *)
    CPPabort "unreachable"
  | MLexn msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    CPPabort msg
  | MLaxiom s -> CPPabort ("unrealized axiom: " ^ s)
  | _ -> CErrors.anomaly (Pp.str "gen_expr: unhandled ML AST node")

(** Handle eta expansion, curried function application, and promoted type arg
    resolution. Recovers erased template type args at call sites where C++ can't
    deduce them from lambda arguments, using the enclosing function's return
    type.

    In the normal (exact-application) case, also detects calls that return
    [std::any] because the callee is higher-rank polymorphic — either a record
    field (e.g. [apply : forall A, A -> A] stored as
    [std::function<std::any(std::any)>]) or an [MLrel] callback with a
    [Tdummy]-guarded [Tvar] codomain.  When such a call is made in a context
    where the enclosing function's return type is a concrete C++ type [T], the
    result is wrapped with [std::any_cast<T>].  See [ml_codomain_erases_to_any]. *)
and eta_fun env f args =
  let rec get_eta_args dom args =
    match (dom, args) with
    | _ :: dom, _ :: args -> get_eta_args dom args
    | _, _ -> dom
  in
  (* Check if an ML arg is a type class instance (a reference to a struct that
     implements a type class) *)
  let is_typeclass_instance_arg ml_arg =
    match ml_arg with
    | MLglob (r, _) ->
      ( match find_type_opt r with
      | Some arg_ty -> Table.is_typeclass_type arg_ty
      | None -> false )
      || ref_returns_skipped r
    | MLrel i ->
      (* Check if the referenced parameter is a type class instance *)
      ( try
          let db, _ = env in
          let _name = List.nth db (pred i) in
          (* Look up the type of this de Bruijn variable in the env's type context *)
          (* Check if the name matches our typeclass instance naming: _tcI0, _tcI1, etc. *)
          (* This is a heuristic - ideally we'd track types in the env *)
          let name_str = Id.to_string _name in
          String.length name_str >= 5 && String.sub name_str 0 4 = "_tcI"
        with _ -> false )
    | MLapp (MLglob (r, _), _) ->
      (* Parameterized instance application, e.g. numList A H. Check if r's
         return type (after stripping Tarr) is a typeclass type, or if it
         returns a skipped type (e.g. ReSum instances where the Class is a
         ConstRef not recognized by is_typeclass). *)
      ref_returns_typeclass r || ref_returns_skipped r
    | MLcase (case_ty, _scrutinee, branches) when Array.length branches = 1 ->
      (* Single-branch case = record field projection.  If the projected
         field's type is itself a typeclass, this is a typeclass instance
         arg — e.g., [base_category(PS)] projects a [PreCategory]-typed
         field from a [PreStableCategory] record.
         Look up the record's field types from the case type rather than
         relying on branch binding types (which may be Tunknown). *)
      let (binds, _, _, br_body) = branches.(0) in
      ( match br_body with
      | MLrel j when j >= 1 && j <= List.length binds ->
        let idx = List.length binds - j in
        (* Try to get the field type from the record definition *)
        let field_is_tc =
          match case_ty with
          | Tglob (r, _, _) when Table.is_typeclass r ->
            let field_types = Table.record_field_types r in
            let non_dummy =
              filter_value_types field_types
            in
            ( try
                let fty = List.nth non_dummy idx in
                Table.is_typeclass_type fty
              with _ -> false )
          | _ -> false
        in
        field_is_tc
      | _ -> false )
    | _ -> false
  in
  (* Save and clear the single-use closure flag so that nested eta_fun calls
     (from processing args) do not inherit it. The saved value is used when
     this eta_fun constructs a partial-application lambda. *)
  let eta_keep_moves = tctx.eta_keep_moves in
  tctx.eta_keep_moves <- false;
  match f with
  | MLglob (id, tys) ->
    (* When the call has more args than the function's ML value-domain, the
       excess args are curried applications to the result. This is common with
       Rocq's Function vernacular _correct proof terms, where the extraction
       produces e.g. div2_rect f f0 f1 n _res __ but div2_rect only has 4
       value-domain params (f, f0, f1, n). The trailing _res and __ are applied
       to the result via currying.

       Split into: - primary_args: first n_value_dom args (passed to the
       function) - excess_args: remaining non-dummy args (curried onto the
       result) Only activates when n_args > n_value_dom; otherwise unchanged. *)
    let args, excess_args =
      let is_value_arg = function
        | MLdummy _ -> false
        | _ -> true
      in
      let is_value_dom t =
        match resolve_tmeta t with
        | Miniml.Tdummy _ -> false
        | _ -> true
      in
      let rec collect_tarr_dom acc = function
        | Miniml.Tarr (t1, t2) -> collect_tarr_dom (resolve_tmeta t1 :: acc) t2
        | _ -> List.rev acc
      in
      match find_type_opt id with
      | Some ml_ty ->
        let all_dom = collect_tarr_dom [] ml_ty in
        (* Count value-domain entries by filtering out ALL [Tdummy] positions
           (both [Ktype] for erased type params and [Kprop] for erased proofs).
           Symmetrically, filter the arg list to exclude [MLdummy] entries.
           Comparing these two filtered counts avoids false excess detection
           when erased params appear in [args] as [MLdummy] instead of (or in
           addition to) being carried in [tys]. *)
        let n_value_dom = List.length (List.filter is_value_dom all_dom) in
        let value_args = List.filter is_value_arg args in
        let n_value_args = List.length value_args in
        if n_value_args > n_value_dom then
          let primary =
            List.filteri (fun i _ -> i < n_value_dom) value_args
          in
          let excess =
            List.filteri (fun i _ -> i >= n_value_dom) value_args
          in
          (primary, excess)
        else
          (value_args, [])
      | None -> (List.filter is_value_arg args, [])
    in
    (* Partition args into type class instances and regular args *)
    let typeclass_ml_args, regular_ml_args =
      List.partition is_typeclass_instance_arg args
    in
    (* Reverse typeclass args to match template param order from gen_dfun:
       gen_dfun iterates collect_lams output (reversed from source) so the first
       typeclass in that order becomes 'i'. Call sites have args in source
       order, so we reverse to match. *)
    let typeclass_ml_args = List.rev typeclass_ml_args in
    (* Convert type class instance args to template type arguments *)
    let rec ml_arg_to_template_type ml_arg =
      match ml_arg with
      | MLglob (r, ts) ->
        if ref_returns_skipped r then
          (* Skipped infrastructure (e.g. ReSum_id) — erase to void *)
          Tvoid
        else
          (* Use the instance struct as a type - convert to Tglob *)
          Tglob (r, build_template_params env [] ts, [])
      | MLrel i ->
        (* The instance is a lambda parameter - look up its name in the env and
           create a Tvar reference to the template parameter *)
        let db, _ = env in
        let name = List.nth db (pred i) in
        Tvar (0, Some name)
      | MLapp (MLglob (r, _), _) when ref_returns_skipped r ->
        (* Skipped infrastructure (e.g. ReSum_inl applied to args) — the inner
           args are complex and cannot be converted to C++ template types.
           Erase to void since these type args are never referenced. *)
        Tvoid
      | MLapp (MLglob (r, ts), inner_args) ->
        (* Parameterized instance application, e.g. numList A H. Convert to
           Tglob(r, template_args, []) where template_args are built from the
           inner args. *)
        let template_args =
          List.filter_map
            (fun arg ->
              match arg with
              | MLdummy _ -> None (* Erased type param — skip *)
              | _ -> Some (ml_arg_to_template_type arg) )
            inner_args
        in
        Tglob (r, build_template_params env [] ts @ template_args, [])
      | MLcase (_, scrutinee, branches)
        when Array.length branches = 1 ->
        (* Record field projection — e.g., [base_category(PS)].
           Resolve to [Tqualified(scrutinee_type, field_name)]. *)
        let (binds, _, _, br_body) = branches.(0) in
        let base_ty = ml_arg_to_template_type scrutinee in
        ( match br_body with
        | MLrel j when j >= 1 && j <= List.length binds ->
          let idx = List.length binds - j in
          let (field_id, _) = List.nth binds idx in
          ( match field_id with
          | Id name | Tmp name -> Tqualified (base_ty, name)
          | Dummy -> Tany )
        | _ -> Tany )
      | MLapp (f, args) ->
        (* Parameterized instance application with non-glob head.
           Resolve head, then add arg types. *)
        let head_ty = ml_arg_to_template_type f in
        let arg_tys =
          List.filter_map
            (fun arg ->
              match arg with
              | MLdummy _ -> None
              | _ -> ( try Some (ml_arg_to_template_type arg)
                        with _ -> None ) )
            args
        in
        ( match head_ty with
        | Tglob (r, existing, es) ->
          Tglob (r, existing @ arg_tys, es)
        | _ -> head_ty )
      | MLdummy _ -> Tany (* Should not happen at top level, but be safe *)
      | _ ->
        CErrors.anomaly
          (Pp.str
             "ml_arg_to_template_type: unexpected ML term after \
              is_typeclass_instance_arg filter" )
    in
    let typeclass_type_args =
      List.map ml_arg_to_template_type typeclass_ml_args
    in
    (* Filter out MLdummy entries from regular args — these are erased proof
       arguments that would generate CPPabort "unreachable" expressions and
       inflate the argument count for eta expansion. *)
    let regular_ml_args =
      List.filter
        (fun x ->
          match x with
          | MLdummy _ -> false
          | _ -> true )
        regular_ml_args
    in
    (* Compute the function's ML type after type arg substitution, to detect
       arguments that return std::any (from erased record fields like
       Functor::object_of) but where the parameter expects a concrete type
       (e.g., unsigned int after resolving a promoted type var). *)
    let fn_ml_ty = find_type id in
    ();
    let fn_ml_ty_subst = try type_subst_list tys fn_ml_ty with _ -> fn_ml_ty in
    let fn_param_ml_tys =
      let rec collect = function
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with Miniml.Tdummy _ -> collect rest | t -> t :: collect rest)
        | _ -> []
      in
      collect fn_ml_ty_subst
    in
    (* Non-substituted parameter types: used to detect whether a callback's
       codomain is a type variable (needs adapter wrapping) vs concrete unit
       (C++ definition already uses void in the is_invocable_v requires clause). *)
    let fn_param_ml_tys_orig =
      let rec collect = function
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with Miniml.Tdummy _ -> collect rest | t -> t :: collect rest)
        | _ -> []
      in
      collect fn_ml_ty
    in
    (* {b Concrete T1 for excess-arg calls.}  When [tys = []] and there
       are excess args, the callee's polymorphic return type [Tvar i] can't
       be resolved by substitution.  We compute the concrete type [T1]
       from the enclosing function's return type and the excess args' types:
       [T1 = excess_arg_types -> enclosing_return_type].

       This value is used in two places:
       1. Lambda arity limiting: to annotate the split outer lambda's
          return type (needed for [is_invocable_r_v] concept checking).
       2. Template arg recovery: as an explicit template argument at the
          call site (C++ can't deduce [T1] from lambda args). *)
    let tvars = get_current_type_vars () in
    let concrete_tvar_type =
      if tys <> [] || excess_args = [] then
        None
      else
        let resolve_tmeta_local = function
          | Miniml.Tmeta {contents = Some t} -> t
          | t -> t
        in
        match tctx.current_cpp_return_type with
        | None -> None
        | Some ret_ty ->
          match find_type_opt id with
          | None -> None
          | Some ml_ty_orig ->
            let ret = resolve_tmeta_local (ml_return_type ml_ty_orig) in
            ( match ret with
            | Miniml.Tvar _ | Miniml.Tvar' _ ->
              (* Compute excess arg C++ types from de Bruijn lookup. *)
              let excess_cpp_tys =
                List.filter_map
                  (fun ml_arg ->
                    match ml_arg with
                    | MLrel i ->
                      Option.map (convert_ml_type_to_cpp_type env tvars)
                        (get_param_type_by_index i)
                    | _ -> None )
                  excess_args
              in
              if List.length excess_cpp_tys = List.length excess_args then
                Some (Tfun (excess_cpp_tys, ret_ty))
              else
                None
            | _ -> None )
    in
    (* When the function is typeclass-parameterized and call-site args include
       concrete instances, compute a promoted-var→concrete-type map so that
       custom constructors (nil/cons) inside arg expressions use concrete
       element types instead of std::any.  E.g., [mfold nat_monoid [1;2;3]]
       resolves m_carrier → uint64_t for the list construction. *)
    let instance_promoted_map =
      List.concat_map (fun tc_arg ->
        match tc_arg with
        | MLglob (r, _) ->
          List.filter_map (fun (var_name, ml_ty) ->
            let tvars = get_current_type_vars () in
            let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
            if is_erased_type cpp_ty then None
            else Some (var_name, cpp_ty)
          ) (Table.get_instance_promoted_types r)
        | _ -> []
      ) typeclass_ml_args
    in
    let saved_promoted_map = tctx.promoted_var_map in
    if instance_promoted_map <> [] then
      tctx.promoted_var_map <- instance_promoted_map @ tctx.promoted_var_map;
    let args = List.mapi (fun i ml_arg ->
      (* {b Lambda arity limiting.}  When a lambda argument has more binders
         than the callee's parameter type has top-level arrows, the extra
         binders come from the return type being a function (instantiated
         from a type variable).  For example, [fold_right]'s callback type
         is [B -> A -> A]; when [A = nat -> nat], the lambda
         [fun t acc => fun x => body] has 3 binders but the parameter has
         only 2 arrows.  Flattening all 3 into a single C++ lambda produces
         a 3-arg function, which doesn't match the 2-arg is_invocable_v constraint.

         Fix: insert an [MLmagic] barrier after the expected number of
         binders so that [collect_lams] in [gen_expr] stops there.  The
         inner binders become a returned inner lambda.  We use the
         {i non-substituted} parameter type to count arrows, because type
         variable substitution would inflate the count (e.g. [Tvar A]
         becoming [Tarr(nat, nat)] adds a spurious arrow).

         Additionally, annotate the outer lambda with an explicit return
         type derived from the {i substituted} parameter type's codomain.
         Without this, the deduced return type is the inner lambda's
         unique closure type, and [is_invocable_r_v<std::function<...>,
         closure_type>] may evaluate to [false] in concept checking
         (C++ lambda-to-[std::function] conversion is not recognized
         during SFINAE in some implementations). *)
      let ml_arg, split_ret_ty =
        match ml_arg with
        | MLlam _ ->
          ( match List.nth_opt fn_param_ml_tys_orig i with
          | Some param_ty ->
            let rec count_arrows = function
              | Miniml.Tarr (_, rest) -> 1 + count_arrows rest
              | _ -> 0
            in
            let expected = count_arrows param_ty in
            let actual = Mlutil.nb_lams ml_arg in
            if expected > 0 && actual > expected then
              let outer_ids, inner_body =
                Mlutil.collect_n_lams expected ml_arg
              in
              let barrier =
                Mlutil.named_lams outer_ids (MLmagic inner_body)
              in
              (* Compute the return type from the substituted param type by
                 stripping [expected] top-level arrows.  The remaining type
                 is the function-typed codomain that the inner lambda
                 implements.

                 When the substituted codomain is still a [Tvar] (happens
                 when [tys = []] so substitution is a no-op), use the
                 [concrete_tvar_type] computed above — it holds the
                 concrete [T1] type derived from the excess args and the
                 enclosing function's return type. *)
              let ret_ty =
                match List.nth_opt fn_param_ml_tys i with
                | Some subst_pt ->
                  let rec codomain_after n = function
                    | Miniml.Tarr (_, rest) when n > 0 ->
                      codomain_after (n - 1) rest
                    | ty -> ty
                  in
                  let ret_ml = codomain_after expected subst_pt in
                  ( match resolve_tmeta ret_ml with
                  | Miniml.Tvar _ | Miniml.Tvar' _ -> concrete_tvar_type
                  | _ ->
                    Some (convert_ml_type_to_cpp_type env tvars ret_ml) )
                | None -> None
              in
              (barrier, ret_ty)
            else
              (ml_arg, None)
          | None -> (ml_arg, None) )
        | _ -> (ml_arg, None)
      in
      let arg_expected_ty =
        match ml_arg with
        | MLmagic _ ->
          (match List.nth_opt fn_param_ml_tys i with
           | Some ml_ty ->
             let tvars = get_current_type_vars () in
             let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
             if is_erased_type cpp_ty then None else Some cpp_ty
           | None -> None)
        | _ -> None
      in
      let saved_expected_for_arg = tctx.expected_ml_type_for_arg in
      ( match List.nth_opt fn_param_ml_tys i with
        | Some ml_ty ->
          if not (ml_type_contains_erased ml_ty) then
            tctx.expected_ml_type_for_arg <- Some ml_ty
        | _ -> () );
      let expr = gen_expr ?expected_ty:arg_expected_ty env ml_arg in
      tctx.expected_ml_type_for_arg <- saved_expected_for_arg;
      (* Annotate the outer lambda with the explicit return type computed
         during the split, so that C++ concept checking sees the concrete
         [std::function<...>] return type instead of the raw closure type. *)
      let expr =
        match split_ret_ty, expr with
        | Some ret_ty, CPPlambda (params, None, body, cap) ->
          CPPlambda (params, Some ret_ty, body, cap)
        | _ -> expr
      in
      let expr =
        match (List.nth_opt fn_param_ml_tys i, expr) with
        | Some param_ty, CPPlambda (params, ret_opt, body, cap) ->
          let param_cpp_ty =
            convert_ml_type_to_cpp_type env tvars param_ty
          in
          ( match param_cpp_ty with
          | Tfun (_, Tshared_ptr inner) ->
            let rec wrap_stmt = function
              | Sreturn (Some e) ->
                Sreturn (Some (CPPfun_call (CPPmk_shared inner, [e])))
              | s -> map_stmt Fun.id wrap_stmt Fun.id s
            in
            CPPlambda
              (params, Some (Tshared_ptr inner), List.map wrap_stmt body, cap)
          | _ -> expr )
        | _ -> expr
      in
      (* Wrap void calls as values only when the expression will be used
         as a value (not in monadic parameter handler which places it in
         statement position inside a lambda). *)
      let as_value () =
        match ml_arg with
        | MLapp (f, _) when ml_callee_is_void f ->
          (* Don't wrap eta-expanded lambdas (partial applications) — they
             are function VALUES, not void call results. *)
          ( match expr with
          | CPPlambda _ -> expr
          | _ -> wrap_void_call_as_value expr )
        | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
          ( match expr with
          | CPPlambda _ -> expr
          | _ -> wrap_void_call_as_value expr )
        | _ -> expr
      in
      (* A bare local variable known to be boxed as [std::any]
         ([cpp_erased_env]) — e.g. a leaf pulled out of an erased-pair
         destructure — passed directly to a plain global function whose
         parameter type is concrete.  Mirrors the equivalent check for
         non-global callees (~[MLrel j when Escape.IntSet.mem ...] above). *)
      let ml_arg_is_erased_rel =
        match ml_arg with
        | MLrel j | MLmagic (MLrel j) -> Escape.IntSet.mem j tctx.cpp_erased_env
        | _ -> false
      in
      match List.nth_opt fn_param_ml_tys i with
      | Some param_ty
        when (ml_body_returns_erased_field ml_arg || ml_arg_is_erased_rel)
             && not (match param_ty with
                     | Miniml.Tglob (g, _, _) -> Table.is_promoted_type_var g
                     | _ -> false)
             (* [param_ty] comes from the callee's own (call-site-substituted)
                type signature, whose [Tvar] indices are not anchored to this
                function's [tvars] scope. When conversion produces an
                unresolved [Tvar (_, None)] (would print as a bogus template
                parameter like "T3"), we cannot build a meaningful concrete
                cast here — skip this branch and fall back to [as_value ()]
                unchanged; a later pass (e.g. [gen_match_branch]'s field
                substitution) supplies the correct cast at its own,
                properly-scoped [tvars]. *)
             && erase_unresolved_tvars (convert_ml_type_to_cpp_type env tvars param_ty)
                = convert_ml_type_to_cpp_type env tvars param_ty ->
        let cpp_ty = convert_ml_type_to_cpp_type env tvars param_ty in
        let strip_ns_tg = function
          | Tnamespace (_, (Tglob _ as inner)) -> inner
          | t -> t
        in
        ( match strip_ns_tg cpp_ty with
        | Tglob (g, [_], _) when is_list_global g && not (Table.is_custom g) ->
          let list_any_ty =
            match cpp_ty with
            | Tnamespace (ns_g, _) -> Tnamespace (ns_g, Tglob (g, [Tany], []))
            | _ -> Tglob (g, [Tany], [])
          in
          CPPconverting_ctor (cpp_ty, [CPPany_cast (list_any_ty, as_value ())])
        | Tglob (g, [_], _) when is_list_global g && Table.is_custom g ->
          (* Custom-extracted list (e.g. [std::deque]) still boxed as
             [std::any] with erased elements at runtime — casting straight
             to the concrete element type here would double-wrap: any_cast
             on the (already concrete) result of a prior any_cast implicitly
             re-boxes it into a fresh [std::any] and then fails to match.
             Cast to the erased-element type instead, matching what
             [gen_match_branch]'s field substitution actually stores. *)
          let erased_ty =
            match cpp_ty with
            | Tnamespace (ns_g, Tglob (g, [elem_ty], _)) ->
              Tnamespace (ns_g, Tglob (g, [Ml_type_util.erase_type_to_any elem_ty], []))
            | Tglob (g, [elem_ty], _) ->
              Tglob (g, [Ml_type_util.erase_type_to_any elem_ty], [])
            | _ -> cpp_ty
          in
          let inner = CPPany_cast (erased_ty, as_value ()) in
          (* When the callee's parameter has a CONCRETE element type (e.g.
             [triples_le_max(const std::deque<rgb>&)]), the erased-element value
             cannot convert to it and, unlike Crane's own [List<A>],
             [std::deque] has no element-converting ctor — unbox each element via
             the [crane_container_cast] runtime helper.

             This is only valid when the element was erased WHOLESALE to
             [std::any] (an opaque/no-args type such as a record — the runtime
             container is [deque<any>] and per-element [any_cast<Elt>] recovers
             it).  A STRUCTURALLY-erased element (e.g. [pair<any,any>] from
             [nat*nat]) is not a boxed [std::any] and would need component-wise
             conversion the helper does not do; inline-custom callees (e.g.
             [length]'s [.size()]) impose no concrete element type at all.  In
             both cases keep the erased value ([inner]) unchanged. *)
          let elem_needs_unbox =
            (* Inline-custom callees splice the argument into a template (e.g.
               [length]'s [%a0.size()]) and work fine on the erased container,
               so no element unboxing is needed there — only a REAL function
               whose parameter is a typed [deque<Elt>] requires it. *)
            (not (Table.is_inline_custom id))
            &&
            match strip_ns_tg cpp_ty with
            | Tglob (_, [et], _) ->
              et <> Tany && Ml_type_util.erase_type_to_any et = Tany
            | _ -> false
          in
          if elem_needs_unbox then begin
            Table.mark_needs_erase_fn ();
            CPPcontainer_cast (cpp_ty, inner)
          end
          else inner
        | _ -> CPPany_cast (cpp_ty, as_value ()) )
      (* Monadic parameter (reified mode only): the callee expects
         [shared_ptr<ITree<R>>].  If the argument already produces a reified
         tree, pass through as-is; otherwise wrap in [ITree<R>::ret()]. *)
      | Some param_ty when tctx.itree_mode = Reified
          && is_monadic_ml_type param_ty
          && not (is_reified_monadic_expr ml_arg) ->
        Table.require_itree_header ();
        let r_ml = extract_itree_result_ml param_ty in
        let r_cpp = convert_ml_type_to_cpp_type env tvars r_ml in
        (* Voidify unit result type in ITree wrapper *)
        let r_cpp = if ml_type_is_unit r_ml then Tvoid else r_cpp in
        let itree_ty = mk_itree_type r_cpp in
        let ret_expr = mk_itree_ret_for_value r_cpp r_ml expr in
        (* Void/unit effects need their side-effect evaluated before ret(). *)
        let body =
          if r_cpp = Tvoid || ml_type_is_unit_or_void r_ml then
            [Sexpr expr; Sreturn (Some ret_expr)]
          else
            [Sreturn (Some ret_expr)]
        in
        CPPfun_call (CPPlambda ([], Some itree_ty, body, false), [])
      (* Void-ified function reference passed as callback to polymorphic
         HOF where the ORIGINAL (non-substituted) parameter codomain is a
         type variable (not concrete unit).  The C++ definition uses a
         template type parameter constrained with is_invocable_v, so the void
         function needs wrapping to return std::monostate.  When the original
         codomain IS concrete unit, the constraint uses void which already
         accepts void-returning functions. *)
      | Some param_ty
        when (match ml_arg with
              | MLglob (r, _) | MLmagic (MLglob (r, _)) -> is_void_ified_ref r
              | _ -> false)
             && (match param_ty with Miniml.Tarr _ -> true | _ -> false)
             && ml_type_is_unit (ml_codomain param_ty)
             && (match List.nth_opt fn_param_ml_tys_orig i with
                 | Some orig_pt ->
                   not (ml_type_is_unit (ml_codomain orig_pt))
                 | None -> false) ->
        let dom_mls =
          let rec collect acc = function
            | Miniml.Tarr (t, rest) ->
              ( match resolve_tmeta t with
              | Miniml.Tdummy _ -> collect acc rest
              | t -> collect (t :: acc) rest )
            | _ -> List.rev acc
          in
          collect [] param_ty
        in
        let dom_cpps =
          List.map
            (fun t -> convert_ml_type_to_cpp_type env tvars t)
            dom_mls
        in
        let params =
          List.mapi
            (fun j ty ->
              (Tref (Tmod (TMconst, ty)), Some (Id.of_string (Printf.sprintf "_wa%d" j))))
            dom_cpps
        in
        let args =
          List.rev_map (fun (_, id) -> CPPvar (Option.get id)) params
        in
        let body =
          [ Sexpr (CPPfun_call (expr, args));
            Sreturn (Some (mk_tt_expr ())) ]
        in
        CPPlambda (List.rev params, None, body, false)
      | _ -> as_value ()
    ) regular_ml_args in
    tctx.promoted_var_map <- saved_promoted_map;
    let ty = fn_ml_ty_subst in
    let ty = convert_ml_type_to_cpp_type env tvars ty in
    (* Combine: instance types first, then regular type args. If any regular
       type arg is Tany or a dummy type glob (from erased params), drop ALL
       regular type args via filter_erased_type_args and let the compiler deduce
       them. See filter_erased_type_args for why we must drop all args rather
       than just the erased ones.

       Exception: when the callee's return type depends on an erased type var,
       C++ can't deduce it from lambda arguments (lambdas don't participate in
       template argument deduction). In that case, recover the concrete type
       from the enclosing function's return type. *)
    let regular_type_args =
      List.map
        (fun ty ->
          let t =
            convert_ml_type_to_cpp_type env tvars (type_simpl ty)
          in
          if has_unnamed_tvar t then
            Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
          else
            t )
        tys
    in
    (* Recover erased type args that C++ cannot deduce. Two cases: (a) tys is
       non-empty but all entries were erased (Tdummy Ktype) →
       filter_erased_type_args drops them all. (b) tys is empty — the Rocq
       extraction didn't supply type args at the call site, but the callee has
       Tdummy Ktype domain entries (erased type params).

       In both cases, if the callee's ML return type is a Tvar that refers to
       one of those erased type params, and we know the concrete return type
       from the enclosing function context (current_cpp_return_type), we can
       supply it as an explicit C++ template arg.

       This is needed because C++ cannot deduce template type params from lambda
       arguments — lambdas don't participate in template argument deduction. *)
    let regular_type_args =
      let filtered =
        filter_erased_type_args
          ~preserve_positions:(Table.is_inline_custom id)
          regular_type_args
      in
      (* Check if the callee's return type is a Tvar pointing to an erased
         (Tdummy Ktype) domain position, and if so, return the position index,
         the concrete C++ type to use, and the full ML domain. *)
      let try_recover_erased_return_type () =
        let rec resolve_tmeta = function
          | Miniml.Tmeta {contents = Some t} -> resolve_tmeta t
          | t -> t
        in
        match tctx.current_cpp_return_type with
        | None -> None
        | Some ret_ty ->
        match find_type_opt id with
        | None -> None
        | Some ml_ty_orig ->
          let ret = resolve_tmeta (ml_return_type ml_ty_orig) in
          ( match ret with
          | Miniml.Tvar i | Miniml.Tvar' i ->
            let rec collect_dom acc = function
              | Miniml.Tarr (t1, t2) -> collect_dom (resolve_tmeta t1 :: acc) t2
              | _ -> List.rev acc
            in
            let all_dom = collect_dom [] ml_ty_orig in
            (* Tvar uses 1-based indexing (matching type_subst_list); convert to
               0-based for list access. *)
            let idx = i - 1 in
            if idx >= 0 && idx < List.length all_dom then
              match
                List.nth all_dom idx
              with
              | Miniml.Tdummy Miniml.Ktype -> Some (idx, ret_ty, all_dom)
              | _ -> None
            else
              None
          | _ -> None )
      in
      if filtered = [] && regular_type_args <> [] then
        (* Case (a): tys was non-empty but all got filtered. Only attempt
           recovery when there are no non-erased value args — if there are value
           args, C++ can deduce the template types from them (and injecting
           explicit type args may conflict with the template signature, e.g.
           hk_map's F0/F1 are function types). *)
          match
            if args = [] then try_recover_erased_return_type () else None
          with
        | Some (idx, ret_ty, _) ->
          (* Replace the erased position with the concrete return type, then
             filter out any remaining erased entries. *)
          List.mapi (fun j t -> if j = idx then ret_ty else t) regular_type_args
          |> List.filter (fun t -> not (is_erased_type t))
        | None -> filtered
      else if tys = [] then
        (* Case (b): tys is empty — synthesize type args from scratch. Build one
           entry per Tdummy Ktype domain position.

           Recovery is attempted when:
           - [args = []] — no value args, so C++ can't deduce types.
           - [concrete_tvar_type <> None] — the callee's return type [Tvar]
             was resolved from excess args + enclosing return type. *)
        let should_recover = args = [] || concrete_tvar_type <> None in
          match
            if should_recover then try_recover_erased_return_type () else None
          with
        | Some (_idx, _ret_ty, all_dom) ->
          (* Use [concrete_tvar_type] when available (excess args case),
             otherwise fall back to the enclosing function's return type. *)
          let t1 = match concrete_tvar_type with
            | Some t -> t
            | None -> _ret_ty
          in
          List.filter_map
            (function
              | Miniml.Tdummy Miniml.Ktype -> Some t1
              | _ -> None )
            all_dom
        | None -> filtered
      else
        filtered
    in
    (* Promoted type vars ([Tvar(1000, Some name)]) are no longer separate
       template parameters — they're resolved through typeclass instance
       access (e.g. [typename _tcI0::Obj]) by [gen_dfun]'s promoted var
       resolution.  No additional template type arguments are needed at
       call sites. *)
    let promoted_type_args = [] in
    (* Filter out Tvoid entries from typeclass_type_args — these arise from
       skipped infrastructure (e.g. ReSum instances) that we classified as
       typeclass args just to remove them from regular_ml_args. They should
       not become actual template type parameters. *)
    let typeclass_type_args =
      List.filter (fun t -> t <> Tvoid) typeclass_type_args
    in
    let all_type_args =
      typeclass_type_args @ regular_type_args @ promoted_type_args
    in
    let cglob = mk_cppglob id all_type_args in
    (* Check if this is a typeclass instance used as a type (for :: access).
       When all args are consumed (domain and args both empty after filtering),
       return just the type reference, not a function call. This avoids
       generating numOption<numNat, unsigned int>() instead of numOption<numNat,
       unsigned int> for qualified access like ::to_nat. *)
    let id_is_typeclass_instance = ref_returns_typeclass id in
    (* {b Curried excess args.}  When a call site provides more value args
       than the callee's ML type has arrows, the extras are curried onto the
       result: [f(primary_args)(excess_args)].

       This is valid when the callee genuinely returns a function:
       - Its codomain is a type alias ([Tglob]) that may expand to [Tarr]
         (e.g. [State S A = S -> A * S]).
       - Its codomain is a type variable ([Tvar]) that, after instantiation
         with the call-site type args [tys], becomes [Tarr] (e.g.
         [fold_right] with [B = nat -> nat]).
       - It is an inlined custom constant (e.g. [fst], [snd]).

       When the codomain is a type variable that instantiates to a
       non-function type (e.g. [div2_rect] with [T1 = R_div2]), the excess
       args come from proof-certificate functions ([Function] vernacular
       [_correct] terms) that are never called at runtime.  We emit an abort
       placeholder for those. *)
    let wrap_excess base =
      if excess_args = [] then
        base
      else (
        let ret_is_chainable =
          is_inline_custom id
          ||
          match find_type_opt id with
          | Some ml_ty ->
            let cod = ml_codomain ml_ty in
            ( match resolve_tmeta cod with
            | Miniml.Tglob _ -> true
            | Miniml.Tarr _ -> true
            | Miniml.Tunknown -> true
            | Miniml.Tvar _ ->
              (* Type variable: instantiate with the call-site type args to
                 determine if the return type is actually a function.
                 [cod] is already the function's codomain (all arrows
                 stripped), so after substitution we check [cod_inst]
                 directly — NOT [ml_codomain cod_inst], which would strip
                 another layer of arrows and reject valid cases like
                 [fold_right] instantiated at [A = nat -> nat].

                 When [tys] is empty (type args carried as [MLdummy] in
                 [args] rather than in the [MLglob] type-arg list),
                 substitution is a no-op and the [Tvar] stays unresolved.
                 In this case, chain unconditionally: Rocq's type system
                 guarantees that excess {i value} args (non-[MLdummy]) can
                 only exist when the return type instantiates to a function.
                 Proof-level excess args are already removed by the
                 [MLdummy] filter above. *)
              if tys = [] then
                true
              else
                let cod_inst = Mlutil.type_subst_list tys cod in
                ( match resolve_tmeta cod_inst with
                | Miniml.Tarr _ -> true
                | Miniml.Tglob _ -> true
                | Miniml.Tdummy Miniml.Ktype -> true
                | Miniml.Tunknown -> true
                | _ -> false )
            | _ -> false )
          | None -> false
        in
        if ret_is_chainable then
          CPPfun_call (base, List.rev (List.map (gen_expr env) excess_args))
        else
          CPPabort "untranslatable curried proof term" )
    in
    let primary_result =
      match ty with
      | Tfun (dom, cod) ->
        (* Filter domain to exclude type class types (they're now template
           params) and erased types. Use has_hkt_erasure for deep checking:
           proof params like wf witnesses may extract as function types
           containing dummy_type (e.g. Tfun([List<T1>], dummy_type)) rather than
           plain dummy_type. These entries must be removed to match the ML arg
           list which already filters out MLdummy entries. *)
        let dom =
          List.filter
            (fun t ->
              (not (Table.is_typeclass_type_cpp t))
              && not (is_erased_type t)
              && not (is_skipped_cpp_type t) )
            dom
        in
        let missing_args = get_eta_args dom args in
        (* When excess args exist (from the ML-level arity split above), do
           NOT eta-expand even if the flattened C++ type has more domain
           elements than ML args.  The mismatch occurs when the callee's
           return type is itself a function type (e.g. [fst] returning
           [Obj -> Path<Obj>]): convert_ml_type_to_cpp_type merges the
           return-type arrows into the domain, inflating [dom_len] beyond the
           ML-level arity.  The excess args will be chained by [wrap_excess]
           below. *)
        if missing_args == [] || excess_args <> [] then
          if (id_is_typeclass_instance || is_inline_custom id) && args = [] then
            (* Typeclass instance or zero-arg inline custom — return
               the glob directly so the template renders as-is. *)
            cglob
          else
            CPPfun_call (cglob, List.rev args)
        else
          (* Substitute promoted type vars in eta-expanded lambda params. When
             partially applying a function like pick_op<nat_magma>, the domain
             types may contain Tvar(1000, Some "carrier") — a promoted type var.
             We resolve these to the concrete type from the typeclass instance
             (e.g., unsigned int from nat_magma::carrier). *)
          let missing_args, cod =
            if typeclass_ml_args <> [] && missing_args <> [] then
              let subst_map =
                List.concat_map
                  (fun tc_arg ->
                    match tc_arg with
                    | MLglob (r, _) ->
                      let bindings = Table.get_instance_promoted_types r in
                      List.map
                        (fun (var_name, ml_ty) ->
                          let cpp_ty =
                            convert_ml_type_to_cpp_type env tvars ml_ty
                          in
                          (var_name, cpp_ty) )
                        bindings
                    | _ -> [] )
                  typeclass_ml_args
              in
              if subst_map <> [] then
                let rec subst_promoted = function
                  | Tvar (1000, Some name) ->
                    ( match
                        List.find_opt
                          (fun (vid, _) -> Id.equal vid name)
                          subst_map
                      with
                    | Some (_, concrete) -> concrete
                    | None -> Tvar (1000, Some name) )
                  | Tmod (m, t) -> Tmod (m, subst_promoted t)
                  | Tfun (d, c) ->
                    Tfun (List.map subst_promoted d, subst_promoted c)
                  | Tshared_ptr t -> Tshared_ptr (subst_promoted t)
                  | t -> t
                in
                (List.map subst_promoted missing_args, subst_promoted cod)
              else
                (missing_args, cod)
            else
              (missing_args, cod)
          in
          let eta_args =
            List.mapi
              (fun i ty ->
                let wrapped =
                  match ty with
                  | Tshared_ptr _ -> Tref (Tmod (TMconst, ty))
                  | _ -> ty
                in
                (wrapped, Some (eta_param_id i)) )
              missing_args
          in
          (* When eta_keep_moves is set (single-use closure from MLletin),
             keep CPPmove wrappers and capture by reference for zero-copy.
             Otherwise strip CPPmove recursively: the closure may be called
             multiple times, so captured variables must not be consumed.
             A top-level strip is insufficient when moves appear inside
             constructor calls, e.g. cons(std::move(t1), rest) — those
             moves would fire on the closure's own captured copy on every
             invocation. *)
          let rec strip_moves_deep = function
            | CPPmove inner -> strip_moves_deep inner
            | CPPfun_call (f, fargs) ->
              CPPfun_call (f, List.map strip_moves_deep fargs)
            | e -> e
          in
          let captured_args =
            if eta_keep_moves then args
            else List.map strip_moves_deep args
          in
          let call_args =
            captured_args
            @ List.mapi (fun i _ -> CPPvar (eta_param_id i)) eta_args
          in
          let call = CPPfun_call (cglob, List.rev call_args) in
          let ret_ty, body =
            if cod = Tvoid then
              (* Void-returning function: execute for side effects, then
                 return without a value. *)
              (None, [Sexpr call; Sreturn None])
            else
              (Some cod, [Sreturn (Some call)])
          in
          CPPlambda (List.rev eta_args, ret_ty, body, not eta_keep_moves)
      | _ ->
        if id_is_typeclass_instance && args = [] then
          cglob
        else if is_inline_custom id && args = [] then
          (* Zero-arg inline custom: return the glob directly so the
             template string renders as-is, without an appended (). *)
          cglob
        else
          CPPfun_call (cglob, args)
    in
    (* Collapse identity inline customs (%a0) at AST level.  This prevents
       unnecessary IIFE wrapping when a void call passes through an identity
       wrapper (e.g. Ceval) and then appears in statement position. *)
    let primary_result =
      match primary_result with
      | CPPfun_call (CPPglob (_, _, Some ci), [single_arg])
        when ci.ci_inline = Some "%a0" ->
        single_arg
      | _ -> primary_result
    in
    (* Wrap pair-accessor inline custom arguments in any_cast when the
       argument's ML type is erased.  E.g. [fst vs] where [vs : std::any]
       generates [any_cast<pair<any,any>>(vs).first] instead of [vs.first].
       This is the inline-custom analog of the scrutinee any_cast in
       [gen_custom_cpp_case]. *)
    let primary_result =
      match primary_result with
      | CPPfun_call (CPPglob (n, _, Some ci) as cglob', [single_arg])
        when ( match ci.ci_inline with
               | Some s -> Common.contains_substring s ".first"
                        || Common.contains_substring s ".second"
               | None -> false ) ->
        let arg_ml_erased =
          let rec has_magic = function
            | MLmagic _ -> true
            | MLapp (MLglob (r, _), args) ->
              (* If the callee is itself a pair accessor (.first/.second) and
                 its product arg was coerced, result is also std::any *)
              let is_pair_accessor =
                match Table.find_custom_opt r with
                | Some s -> Common.contains_substring s ".first"
                         || Common.contains_substring s ".second"
                | None -> false
              in
              if is_pair_accessor then
                let inner_args =
                  List.filter (fun x -> match x with MLdummy _ -> false | _ -> true) args
                in
                List.exists has_magic inner_args
              else false
            | MLapp (MLmagic _, _) -> true
            | MLrel i ->
              (match get_env_type_opt i with
               | Some ty -> is_erased_ml_type (resolve_tmeta ty)
               | None -> false)
            | _ -> false
          in
          if List.length regular_ml_args > 0 then
            has_magic (List.nth regular_ml_args 0)
          else false
        in
        if arg_ml_erased then
          let prod_g_opt =
            try
              let ml_ty = Table.find_type n in
              let rec find_prod = function
                | Miniml.Tarr (t, rest) ->
                  ( match resolve_tmeta t with
                  | Miniml.Tglob (g, _, _) when is_prod_global g -> Some g
                  | Miniml.Tdummy _ -> find_prod rest
                  | _ -> None )
                | _ -> None
              in
              find_prod ml_ty
            with Not_found -> None
          in
          ( match prod_g_opt, single_arg with
          | _, CPPany_cast _ -> primary_result
          | Some g, _ ->
            tctx.last_pair_accessor_any_cast <- true;
            CPPfun_call (cglob',
              [CPPany_cast (Tglob (g, [Tany; Tany], []), single_arg)])
          | None, _ -> primary_result )
        else
          primary_result
      | _ -> primary_result
    in
    wrap_excess primary_result
  | _ ->
    (* Non-global callee (e.g., a local variable from MLrel). Filter out MLdummy
       args — these are erased type/prop parameters that have no runtime
       representation. Unlike the MLglob case above, there is no type-arg list
       to filter here; we only need to drop value-level dummies. *)
    let args =
      List.filter
        (fun x ->
          match x with
          | MLdummy _ -> false
          | _ -> true )
        args
    in
    let callee_param_tys =
      let rec extract_params = function
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with Miniml.Tdummy _ -> extract_params rest | t -> t :: extract_params rest)
        | Miniml.Tmeta {contents = Some t} -> extract_params t
        | _ -> []
      in
      let fty_opt = match f with
        | MLglob (r, tys) when tys <> [] ->
          (match find_type_opt r with
           | Some ty -> Some (ml_subst_tvars (Array.of_list tys) ty)
           | None -> infer_ml_body_type f)
        | _ -> infer_ml_body_type f
      in
      match fty_opt with Some fty -> extract_params fty | None -> []
    in
    let callee_rel_idx = match f with
      | MLrel i | MLmagic (MLrel i) -> Some i
      | _ -> None
    in
    let callee_env_ty =
      match callee_rel_idx with
      | Some i -> (try Some (get_env_type i) with _ -> None)
      | None -> None
    in
    let callee_cpp_erased =
      match callee_rel_idx with
      | Some i -> Escape.IntSet.mem i tctx.cpp_erased_env
      | None -> false
    in
    let callee_is_bare_any =
      callee_cpp_erased ||
      (match callee_env_ty with
      | Some ty -> is_ml_erased_ty ty
      | None -> false)
    in
    let callee_has_erased_params =
      callee_is_bare_any ||
      (match callee_env_ty with
      | Some (Miniml.Tarr (param, _)) -> is_ml_erased_ty param
      | _ -> false) ||
      (match callee_rel_idx with
       | Some i ->
         (match IntMap.find_opt i tctx.cpp_erased_type_env with
          | Some (Tfun (params, _)) -> List.exists (fun p -> p = Tany) params
          | _ -> false)
       | None -> false)
    in
    let saved_wrap = tctx.wrap_for_any_param in
    if callee_has_erased_params then
      tctx.wrap_for_any_param <- true;
    (* [has_unresolved_boxed_arg]: set when an argument is statically known to
       be boxed as [std::any] ([cpp_erased_env]) but the callee's parameter
       type at this position can't be resolved to a concrete C++ type (it is
       itself abstract/erased, e.g. a value-dependent type scheme like
       [S.sem a]).  This happens when the callee is a genuinely-concrete
       function only at C++ template instantiation time (e.g. a functor
       parameter instantiated with a concrete inlined function) — the OCaml
       side cannot know the concrete type to [any_cast] to.  Such calls are
       routed through the [crane_call_erased] runtime helper instead of a
       direct call, so the concrete parameter types can be recovered via
       [std::function] CTAD once C++ instantiates the template. *)
    let has_unresolved_boxed_arg = ref false in
    let args = List.mapi (fun i x ->
      match x with
      | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
        wrap_void_call_as_value (gen_expr env x)
      | MLmagic _ ->
        let expected = match List.nth_opt callee_param_tys i with
          | Some ml_ty ->
            let tvars = get_current_type_vars () in
            let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
            if is_erased_type cpp_ty then None else Some cpp_ty
          | None -> None
        in
        gen_expr ?expected_ty:expected env x
      | MLrel j when Escape.IntSet.mem j tctx.cpp_erased_env ->
        let inner = gen_expr env x in
        let expected = match List.nth_opt callee_param_tys i with
          | Some ml_ty ->
            let tvars = get_current_type_vars () in
            let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
            if is_erased_type cpp_ty then None else Some cpp_ty
          | None -> None
        in
        ( match expected with
          | Some ty ->
            let rec erase_type_to_any = function
              | Tglob (g, args, ns) when args <> [] ->
                Tglob (g, List.map erase_type_to_any args, ns)
              | Tglob (_, [], _) as t -> t
              | Tnamespace (ns_g, inner) ->
                Tnamespace (ns_g, erase_type_to_any inner)
              | _ -> Tany
            in
            CPPany_cast (erase_type_to_any ty, inner)
          | None ->
            has_unresolved_boxed_arg := true;
            inner )
      | _ -> gen_expr env x) args in
    tctx.wrap_for_any_param <- saved_wrap;
    (* Detect over-application: when a local variable's C++ type has fewer
       value-domain arrows than the number of ML args, the call must be split
       into a primary call and a chained application of excess args. Example: [f
       : A -> State S B] applied as [f(a, s')] becomes [f(a)(s')]. *)
    let n_value_dom =
      let rel_idx_f = match f with
        | MLrel i | MLmagic (MLrel i) -> Some i
        | _ -> None
      in
      match rel_idx_f with
      | Some i ->
        ( try
            let ty = get_env_type i in
            let n = count_ml_value_arrows ty in
            if n < List.length args && ml_codomain_is_tvar ty then
              List.length args
            else n
          with _ -> List.length args )
      | None -> List.length args
    in
    let n_args = List.length args in
    if n_args = 0 then
      (* All args were erased (MLdummy): no function call, just the
         expression itself.  This arises when erased proof arguments
         (e.g. [le n 0] in [Function]-generated [_rect] bodies) are
         applied to a local variable — the proofs are filtered out,
         leaving an empty arg list.  Generating [f()] would be wrong
         because the C++ type has no 0-arg overload. *)
      gen_expr env f
    else if n_args < n_value_dom && n_value_dom > 0 then
      (* Under-application (partial application due to proof erasure).
         The callee expects [n_value_dom] args but only [n_args] are
         provided — the rest were erased proofs in the same
         [MLapp] that have been filtered out.

         Generate a lambda wrapper that captures the provided args and
         forwards them along with fresh parameters for the remaining
         args.  E.g., [f2(n1)] where [f2 : (nat, T1) -> T1] becomes:
         [[&](T1 _pa0) { return f2(n1, _pa0); }]. *)
      let remaining_ml_tys =
        match f with
        | MLrel i ->
          ( try
              let ml_ty = get_env_type i in
              (* Skip [n_args] non-dummy domain entries to find the
                 remaining value-domain types. *)
              let rec skip_and_collect n = function
                | Miniml.Tarr (t, rest) ->
                  ( match resolve_tmeta t with
                  | Miniml.Tdummy _ -> skip_and_collect n rest
                  | t ->
                    if n > 0 then skip_and_collect (n - 1) rest
                    else t :: skip_and_collect 0 rest )
                | Miniml.Tmeta {contents = Some t} -> skip_and_collect n t
                | _ -> []
              in
              skip_and_collect n_args ml_ty
            with _ -> [] )
        | _ -> []
      in
      if remaining_ml_tys <> [] then
        let callee = gen_expr env f in
        let tvars = get_current_type_vars () in
        let pa_params = List.mapi (fun j ml_ty ->
          let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
          (cpp_ty, Some (Id.of_string (Printf.sprintf "_pa%d" j))) )
          remaining_ml_tys
        in
        let pa_exprs = List.map (fun (_, id_opt) ->
          CPPvar (Option.get id_opt)) pa_params in
        (* CPPlambda stores params in reverse (de Bruijn) order;
           the printer reverses them for display.  Reverse pa_params
           so the printed output matches source order. *)
        CPPlambda (List.rev pa_params, None,
          [Sreturn (Some (CPPfun_call (callee,
              List.rev (args @ pa_exprs))))],
          true)
      else
        CPPfun_call (gen_expr env f, List.rev args)
    else if n_args > n_value_dom && n_value_dom > 0 then
      let primary = List.rev (safe_firstn n_value_dom args) in
      let excess = List.rev (List.skipn n_value_dom args) in
      CPPfun_call (CPPfun_call (gen_expr env f, primary), excess)
    else
      (* When the callee is a local variable whose ML type is a bare type
         variable (Tvar/Tvar'/Tunknown), its C++ type is std::any.  std::any
         is not callable, so we must wrap it with std::any_cast to recover the
         std::function type before calling.  Both arg and return types
         default to std::any since the original types are erased.
         The MLmagic wrapper is transparent — peel it to find the MLrel. *)
      let callee_expr =
        if callee_is_bare_any then
          let arg_tys = List.init n_args (fun _ -> Tany) in
          CPPany_cast (Tfun (arg_tys, Tany), gen_expr env f)
        else
          gen_expr env f
      in
      (* Check whether this call returns [std::any] (erased type) but the
         enclosing function expects a concrete type, requiring an
         [std::any_cast<T>] wrapper.  See [ml_codomain_erases_to_any].
         Two callee forms are handled:
         - [MLcase] single-branch record projection whose field type has a
           higher-rank codomain (e.g. [apply : forall A, A -> A] stored as
           [std::function<std::any(std::any)>]).
         - [MLrel] higher-rank callback whose env-type has a [Tvar] codomain
           guarded by [Tdummy] (e.g. [f : forall A, A -> A]). *)
      let result =
        if !has_unresolved_boxed_arg && not callee_is_bare_any then begin
          Table.mark_needs_erase_fn ();
          CPPfun_call
            (CPPvar (Id.of_string "crane_call_erased"), List.rev args @ [callee_expr])
        end
        else CPPfun_call (callee_expr, List.rev args)
      in
      let n = n_args in
      let erased_cod =
        match f with
        | MLcase (case_ty, _, pv) when Array.length pv = 1 ->
          let (binds, _, _, br_body) = pv.(0) in
          let n_binds = List.length binds in
          let proj_idx =
            match br_body with
            | MLrel i when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | MLmagic (MLrel i) when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | _ -> None
          in
          ( match proj_idx with
          | Some idx ->
            ( match case_ty with
            | Tglob (r, _, _) ->
              let all_ft = Table.record_field_types r in
              let non_erased = filter_value_types all_ft in
              ( try ml_codomain_erases_to_any n (List.nth non_erased idx)
                with _ -> false )
            | _ -> false )
          | None -> false )
        | MLrel i ->
          (match get_env_type_opt i with Some ty -> ml_codomain_erases_to_any n ty | None -> false)
        | _ -> false
      in
      ( match (erased_cod, tctx.current_cpp_return_type) with
      | (true, Some ty) when ty <> Tany && not (is_erased_type ty) && ty <> Tvoid ->
        CPPany_cast (ty, result)
      | _ -> result )

(** Build the qualified constructor struct type for a pattern match branch.

    For [list<int>::Cons], this produces
    [Tqualified(Tnamespace(r, Tglob(r, temps, \[\])), ctor_name)].
    Local inductives omit the namespace wrapper to avoid double qualification. *)
and ctor_type_of_match env (typ : ml_type) (cname : GlobRef.t) : cpp_type =
  let tvars = get_current_type_vars () in
  let ctor_name = ctor_struct_id_of_ref cname in
  match typ with
  | Tglob (r, tys, _) ->
    let tys = List.map type_simpl tys in
    let tys =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars -> safe_firstn num_param_vars tys
        | None -> tys )
      | _ -> tys
    in
    let temps = build_template_params env tvars tys in
    let is_local_ind =
      List.exists
        (globref_equal r)
        (get_local_inductives ())
    in
    let ind_type =
      if is_local_ind then Tglob (r, temps, [])
      else Tnamespace (r, Tglob (r, temps, []))
    in
    Tqualified (ind_type, ctor_name)
  | _ -> Tid (ctor_name, [])

(** Generate a single branch of an {!Smatch} if/else-if pattern match chain.

    Produces an {!smatch_branch} record whose body statements live directly
    in the enclosing if-block.

    {b Structured bindings.}  Field accesses use
    [const auto& [d_f0, d_f1] = std::get<T>(v)].  The reference binding is
    required so that [[=]]-capturing closures copy the struct value rather
    than a raw pointer that could dangle after the match scope ends.

    {b [match_i] suffix generation.}  [match_i] is the match-level counter
    (0 for the outermost match).  Nested matches increment the counter so
    binding names get suffixed (e.g. [d_a00], [d_a10]) to avoid shadowing
    outer bindings.

    {b [dummies] mask.}  A [bool list] parallel to [ids]: [true] means the
    pattern variable is actually used (gets a binding); [false] means it is
    [Dummy] (omitted from the structured binding with a placeholder).  This
    avoids generating unused variable warnings in the C++ output.

    @param env      current name environment
    @param typ      the scrutinee's ML type (used to resolve the inductive)
    @param rty      the branch's return type
    @param cname    the constructor's [GlobRef.t]
    @param ids      renamed pattern variable names with types
    @param dummies  parallel mask: [true] = non-Dummy (used), [false] = Dummy
    @param body     the branch body AST
    @param sname    scrutinee expression name (for structured binding access)
    @param match_i  nesting level counter for name suffixing
    @param scrut_v  the [scrut->v()] or [scrut.v()] accessor expression *)
and gen_match_branch env (typ : ml_type) rty cname ids dummies body sname
    match_i scrut_v ~is_value_type ~is_owned ~scrut_db ~is_flat =
  let ctor_type = ctor_type_of_match env typ cname in
  let ctor_name = ctor_struct_id_of_ref cname in
  let ctor_struct_name = Id.to_string ctor_name in
  let n_pat_vars = List.length ids in
  (* When the scrutinee is an owned variable (is_owned = true) and we create
     const-ref structured bindings into it ([const auto& [d_a0, d_a1] = ...]),
     moving the scrutinee inside the branch would leave those references
     dangling.  Exclude the shifted scrutinee index from move_owned_vars for
     the duration of the branch so move insertion cannot fire on it. *)
  let exclude_scrutinee =
    if is_owned then Option.map (fun db -> db + n_pat_vars) scrut_db
    else None
  in
  (* Compute ind_ref and field self-reference info early so pat_var_owned
     can exclude shared_ptr-wrapped fields from move tracking. *)
  let ind_ref =
    match cname with
    | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
    | r -> r
  in
  let def_site_field_tys =
    match Table.get_ctor_ip_types_opt cname with
    | Some tys -> tys
    | None -> []
  in
  let non_erased_def_site_field_tys =
    List.filter (fun t -> not (isTdummy t)) def_site_field_tys
  in
  let ind_kn_opt =
    match ind_ref with
    | GlobRef.IndRef (kn, _) -> Some kn
    | _ -> None
  in
  let is_self_or_mutual r =
    globref_equal r ind_ref
    || match r, ind_kn_opt with
       | GlobRef.IndRef (kn2, _), Some kn ->
         MutInd.CanOrd.equal kn2 kn
       | _ -> false
  in
  let field_is_self_or_mutual_ref_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some (Miniml.Tglob (r, _, _)) -> is_self_or_mutual r
    | Some (Miniml.Tmeta {contents = Some (Miniml.Tglob (r, _, _))}) ->
      is_self_or_mutual r
    | _ -> false
  in
  let rec ml_has_self_ref = function
    | Miniml.Tglob (r, args, _) ->
      is_self_or_mutual r || List.exists ml_has_self_ref args
    | Miniml.Tmeta {contents = Some t} -> ml_has_self_ref t
    | Miniml.Tarr (t1, t2) ->
      ml_has_self_ref t1 || ml_has_self_ref t2
    | _ -> false
  in
  let field_has_nested_self_ref_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some (Miniml.Tglob (r, args, _)) when not (is_self_or_mutual r) ->
      List.exists ml_has_self_ref args
    | Some (Miniml.Tmeta {contents = Some (Miniml.Tglob (r, args, _))})
      when not (is_self_or_mutual r) ->
      List.exists ml_has_self_ref args
    | _ -> false
  in
  let field_is_uptr i =
    not (Table.is_coinductive ind_ref)
    && (field_is_self_or_mutual_ref_at_def i
        || field_has_nested_self_ref_at_def i)
  in
  let pat_var_owned =
    if is_owned then
      List.fold_left (fun (acc, j) _ ->
          let db = j + 1 in
          let def_field_idx = n_pat_vars - 1 - j in
          let acc' =
            if not (field_is_uptr def_field_idx) then
              Escape.IntSet.add db acc
            else acc
          in
          (acc', j + 1))
        (Escape.IntSet.empty, 0) ids
      |> fst
    else Escape.IntSet.empty
  in
  (* Compute structured binding names BEFORE the body, so that inner nested
     matches see these names in their avoid set and won't produce shadowing
     C++ variable names (e.g. two nested [Char] branches both naming [t0]).
     For match_i=0 the binding name equals the struct field name (e.g. [d_a0]);
     for deeper nesting a numeric suffix prevents collisions
     (e.g. [d_a00] at level 1, [d_a01] at level 2). *)
  let suffix =
    if match_i = 0 then "" else string_of_int (match_i - 1)
  in
  let rev_ids = List.rev ids in
  let dummies_arr = Array.of_list dummies in
  let outer_avoid = snd env in
  let binding_names_arr =
    let avoid = ref outer_avoid in
    Array.init (List.length rev_ids) (fun i ->
      let field_id = lookup_ctor_bind_name ctor_struct_name i in
      let base = Id.of_string (Id.to_string field_id ^ suffix) in
      let name =
        if Id.Set.mem base !avoid then rename_id base !avoid else base
      in
      avoid := Id.Set.add name !avoid;
      name)
  in
  (* Extend env's avoid set with the binding names so inner matches can
     see them and avoid generating the same names (prevents C++ shadowing). *)
  let env_for_body =
    let binding_avoid =
      Array.fold_left (fun acc n -> Id.Set.add n acc)
        outer_avoid binding_names_arr
    in
    (fst env, binding_avoid)
  in
  let body_stmts =
    with_shifted_move_tracking n_pat_vars ~clear_dead:true
      ~add_owned_set:pat_var_owned ?exclude_owned:exclude_scrutinee
      (fun () ->
      let saved_match_counter = tctx.match_param_counter in
      let saved_cs_counter = tctx.cs_counter in
      let saved_return_type = tctx.current_cpp_return_type in
      ( if tctx.current_cpp_return_type = Some Tvoid then
          tctx.current_cpp_return_type <- None );
      populate_erased_field_env ~cname ~typ ~env ~n_pat_vars
        ~n_fields:(List.length rev_ids)
        ~non_erased_def_site_field_tys;
      let body_stmts = gen_stmts env_for_body (fun x -> Sreturn (Some x)) body in
      tctx.current_cpp_return_type <- saved_return_type;
      tctx.match_param_counter <- saved_match_counter;
      tctx.cs_counter <- saved_cs_counter;
      body_stmts)
  in
  let tvars = get_current_type_vars () in
  let field_bindings =
    List.mapi
      (fun i (_var_name, ml_ty) ->
        let binding_name = binding_names_arr.(i) in
        (* A field needs dereferencing if:
           1. It's a direct self/mutual ref at the definition site
              (stored as shared_ptr in the struct), OR
           2. The def-site field type is Tvar (type parameter) that resolves
              to shared_ptr<T> via template substitution, where T is a
              value-type inductive in method_self_ns.  This happens when a
              container like List<shared_ptr<tree>> stores elements via
              template parameter t_A = shared_ptr<tree>. Direct struct
              fields (Tglob at def-site) are bare value types. *)
        (* Convert using empty ns.  For value-type self/mutual fields the
           expression substituted into the branch body is dereferenced, but the
           structured binding itself still has the stored field type
           [shared_ptr<T>].  Loopify uses this metadata to infer frame field
           types for expressions like [d_a0.get()] and [*d_a0]. *)
        let bare_field_cpp_ty =
          convert_ml_type_to_cpp_type env tvars ml_ty
        in
        let storage_field_cpp_ty =
          convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton ind_ref)
            tvars
            ml_ty
        in
        (* A non-coinductive field is shared_ptr-wrapped only for UNIFORM
           self-recursion.  Non-uniform recursion (e.g. tree<pair<T,T>> inside
           tree<T>) stores as a bare value type.  Find the self/mutual reference
           anywhere in the ML type (direct or nested in type args) and check if
           its type arguments match the parent's params uniformly. *)
        let is_uniform_self_ref_at_def i =
          match List.nth_opt non_erased_def_site_field_tys i with
          | Some ty -> begin
            match find_self_ref_args ~is_self_or_mutual ty with
            | Some args ->
              let n_params = Table.get_ctor_num_param_vars cname in
              List.length args = n_params
              && List.for_all (fun (j, arg) ->
                match arg with
                | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
                | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
                | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} -> k = j + 1
                | _ -> false
              ) (List.mapi (fun j a -> (j, a)) args)
            | None -> true  (* no self-ref found: treat as uniform *)
          end
          | _ -> true
        in
        let is_sptr_self_ref =
          ( field_is_self_or_mutual_ref_at_def i
            || field_has_nested_self_ref_at_def i )
          && not (Table.is_coinductive ind_ref)
          && is_uniform_self_ref_at_def i
        in
        let field_cpp_ty =
          if is_sptr_self_ref then
            (* All self/mutual refs (direct or nested-in-custom): struct field
               is shared_ptr<bare>.  After deref, the binding has type bare_ty
               which matches the API type directly — no element-wise conversion
               needed.  Using storage_field_cpp_ty here would store inner
               self-refs as shared_ptr<T> inside the custom container, but
               there is no element-wise converter from List<shared_ptr<T>> to
               List<T>, so we must keep elements as bare values. *)
            Tshared_ptr bare_field_cpp_ty
          else
            (* Use storage_field_cpp_ty but correct false-positive shared_ptr
               wrapping: when storage wraps with shared_ptr but the def-site
               check says NOT a self-ref, use bare type instead.
               This happens when a type parameter is instantiated to the same
               inductive (e.g. element List<T> inside List<List<T>>): the element
               field's def-site type is a bare Tvar (not self-ref), but at the
               use site it resolves to List<T> which ns-wraps to shared_ptr. *)
            if non_erased_def_site_field_tys <> []
               && not (field_is_self_or_mutual_ref_at_def i)
               && not (field_has_nested_self_ref_at_def i)
               && contains_shared_ptr storage_field_cpp_ty
            then bare_field_cpp_ty
            else storage_field_cpp_ty
        in
        (* For coinductive types, fields with nested self-refs are stored
           as shared_ptr to break circular template dependencies (e.g.
           colist<cotree<A>> inside cotree<A>).  Apply the same wrapping
           that gen_ind_header_v2 applies. *)
        let field_cpp_ty =
          if Table.is_coinductive ind_ref
             && field_has_nested_self_ref_at_def i
          then Tshared_ptr bare_field_cpp_ty
          else field_cpp_ty
        in
        let used = dummies_arr.(i) in
        (binding_name, field_cpp_ty, is_sptr_self_ref, used))
      rev_ids
  in
  let field_bindings_arr = Array.of_list field_bindings in
  let rec expr_has_lambda = function
    | CPPfun_call (CPPlambda (_, _, body, _), _) ->
      (* IIFE: lambda is invoked immediately, so reference captures are safe.
         Only check the lambda body for nested non-IIFE lambdas. *)
      List.exists stmt_has_lambda body
    | CPPlambda (_, _, _, true) ->
      (* [=] value-capture: non-coinductive self-ref fields (shared_ptr) need
         pre-extraction into a value binding before the lambda is entered. *)
      true
    | CPPlambda (_, _, body, false) ->
      (* [&] ref-capture: shared_ptr fields are captured by reference — fine.
         Check the body for nested [=] lambdas that would need pre-extraction. *)
      List.exists stmt_has_lambda body
    | e ->
      let found = ref false in
      iter_expr_children
        ~on_expr:(fun e' -> if expr_has_lambda e' then found := true)
        ~on_stmts:(fun stmts ->
          if List.exists stmt_has_lambda stmts then found := true)
        e;
      !found
  and stmt_has_lambda = function
    | Sreturn (Some e) | Sexpr e -> expr_has_lambda e
    | Sasgn (_, _, e) | Sderef_asgn (_, e) -> expr_has_lambda e
    | Sif (c, t, f) ->
      expr_has_lambda c || List.exists stmt_has_lambda t
      || List.exists stmt_has_lambda f
    | Sswitch (scrut, _, branches, default) ->
      expr_has_lambda scrut
      || List.exists (fun (_, body) -> List.exists stmt_has_lambda body) branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Smatch (branches, default) ->
      List.exists
        (fun br ->
          expr_has_lambda br.smb_scrutinee
          || List.exists stmt_has_lambda br.smb_body)
        branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Scustom_case (_, scrut, _, branches, _) ->
      expr_has_lambda scrut
      || List.exists
           (fun (_, _, body) -> List.exists stmt_has_lambda body)
           branches
    | Sassign_field (obj, _, e) -> expr_has_lambda obj || expr_has_lambda e
    | Swhile (c, body) -> expr_has_lambda c || List.exists stmt_has_lambda body
    | Sblock body -> List.exists stmt_has_lambda body
    | Sblock_custom (_, _, _, _, args, _) -> List.exists expr_has_lambda args
    | _ -> false
  in
  let branch_has_lambda = List.exists stmt_has_lambda body_stmts in
  (* True when the enclosing function returns a coinductive type and will
     wrap each branch result in a [lazy_] thunk via [cofix_wrap].  The
     thunk is a [CPPlambda] that captures by [=], so non-coinductive
     self-ref (shared_ptr) fields bound in the branch need pre-extraction
     before the lambda to ensure they are captured as value types.
     This flag triggers pre-extraction even when [branch_has_lambda] is
     false (because the lambda is added externally by [inline_iife]). *)
  let return_type_is_coinductive =
    match tctx.current_cpp_return_type with
    | Some (Tglob (r, _, _)) -> Table.is_coinductive r
    | _ -> false
  in
  let branch_needs_sptr_preextract =
    branch_has_lambda || return_type_is_coinductive
  in
  (* A non-self-referential field in a type-indexed inductive (no template
     params) whose def-site type contains an unnamed Tvar is stored as
     [std::any] in the struct.  At the match site we recover the ML-known
     type with [std::any_cast<bare_ty>].  This handles every access pattern
     uniformly — fst, snd, or any other function — because the cast is
     applied at the binding site, not at individual use sites. *)
  let scrut_template_args_lazy = lazy (
    let tvars = get_current_type_vars () in
    let scrut_cpp_ty = convert_ml_type_to_cpp_type env tvars typ in
    extract_template_args scrut_cpp_ty
  ) in
  let field_is_wholesale_erased =
    let num_pv = Table.get_ctor_num_param_vars cname in
    fun i ->
      not (field_is_self_or_mutual_ref_at_def i)
      && not (field_has_nested_self_ref_at_def i)
      && (match List.nth_opt non_erased_def_site_field_tys i with
          | Some def_ty when num_pv = 0 ->
            let cpp_ty =
              convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton ind_ref) [] def_ty
            in
            has_unnamed_tvar cpp_ty
          | Some (Miniml.Tvar k | Miniml.Tvar' k) ->
            let scrut_targs = Lazy.force scrut_template_args_lazy in
            (match List.nth_opt scrut_targs (k - 1) with
             | Some t -> resolves_to_any_type t
             | None -> false)
          | _ -> false)
  in
  (* Substitute pattern variable references with the structured-binding
     names.  For non-coinductive self-ref fields (stored as shared_ptr),
     the structured binding gives [const shared_ptr<T>& d_field]; we
     dereference it so the body sees a value reference [const T&] instead.
     This ensures method calls use [.] not [->]. *)
  let body_stmts =
    List.fold_left
      (fun stmts (i, (var_name, _ml_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, is_uptr, _) = field_bindings_arr.(i) in
          let bare_ty = convert_ml_type_to_cpp_type env tvars _ml_ty in
          (* Pre-extract fields stored as shared_ptr when the branch body
             contains a lambda (or the return type is coinductive), so the
             lambda captures the value type rather than the shared_ptr.
             Only non-coinductive self-refs (is_uptr = true) need this:
             all formerly-unique_ptr fields have is_uptr set, and shared_ptr
             (coinductive or generic container fields) is copyable and can
             be captured directly. *)
          let is_uptr_field = is_uptr in
          let subst_expr =
            if is_uptr_field && branch_needs_sptr_preextract then
              CPPvar (Id.of_string (Id.to_string binding_name ^ "_value"))
            else if is_uptr_field then
              (* field_ty = Tshared_ptr storage_inner.  Deref the outer
                 shared_ptr, then convert storage_inner → bare_ty if they
                 differ (e.g. optional<shared_ptr<T>> → optional<T>). *)
              let deref = CPPderef (CPPvar binding_name) in
              (match field_ty with
               | Tshared_ptr storage_inner when storage_inner <> bare_ty ->
                 gen_type_conversion_expr ~src_ty:storage_inner ~dst_ty:bare_ty deref
               | _ -> deref)
            else if field_ty <> bare_ty
                    && contains_shared_ptr field_ty then
              gen_type_conversion_expr ~src_ty:field_ty ~dst_ty:bare_ty
                (CPPvar binding_name)
            else if field_is_wholesale_erased i
                    && not (is_erased_type bare_ty) then
              let strip_ns_tg = function
                | Tnamespace (_, (Tglob _ as inner)) -> inner
                | t -> t
              in
              (match strip_ns_tg bare_ty with
               | Tglob (g, [_], _) when is_list_global g && not (Table.is_custom g) ->
                 let list_any_ty =
                   match bare_ty with
                   | Tnamespace (ns_g, _) -> Tnamespace (ns_g, Tglob (g, [Tany], []))
                   | _ -> Tglob (g, [Tany], [])
                 in
                 CPPconverting_ctor (bare_ty, [CPPany_cast (list_any_ty, CPPvar binding_name)])
               | Tglob (g, [elem_ty], _) when is_list_global g && Table.is_custom g ->
                 let erased_elem = erase_type_to_any elem_ty in
                 let cast_ty =
                   if erased_elem = Tany then bare_ty
                   else Tglob (g, [erased_elem], [])
                 in
                 CPPany_cast (cast_ty, CPPvar binding_name)
               | _ -> CPPany_cast (bare_ty, CPPvar binding_name))
            else
              CPPvar binding_name
          in
          List.map (local_var_subst_stmt var_name subst_expr) stmts
        else
          stmts )
      body_stmts
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let uptr_value_bindings =
    List.filter_map
      (fun (i, (_var_name, ml_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, is_uptr, _) =
            field_bindings_arr.(i)
          in
          let is_uptr_field = is_uptr in
          if is_uptr_field && branch_needs_sptr_preextract then
            let bare_ty =
              convert_ml_type_to_cpp_type env tvars ml_ty
            in
            let value_id =
              Id.of_string (Id.to_string binding_name ^ "_value")
            in
            (* Bind as [const T& a_value = *a] rather than [T a_value = *a].
               [=] capture of a ref-typed local copies the referenced object
               into the closure (same semantics, no intermediate copy).
               [&] capture is safe because shared_ptr pre-extracts only occur
               inside non-escaping lambda scopes.
               When the stored type (storage_inner) differs from bare_ty,
               apply a conversion (e.g. optional<shared_ptr<T>> → optional<T>). *)
            let deref = CPPderef (CPPvar binding_name) in
            let (binding_name', field_ty', _, _) = field_bindings_arr.(i) in
            let _ = binding_name' in
            let rhs =
              match field_ty' with
              | Tshared_ptr storage_inner when storage_inner <> bare_ty ->
                gen_type_conversion_expr ~src_ty:storage_inner ~dst_ty:bare_ty deref
              | _ -> deref
            in
            Some
              (Sasgn
                 ( value_id,
                   Some (Tref (Tmod (TMconst, bare_ty))),
                   rhs ))
          else None
        else None)
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let body_stmts = uptr_value_bindings @ body_stmts in
  (* Use std::get (smb_var = Some) when any constructor field is actually used;
     otherwise use holds_alternative only (smb_var = None). *)
  let has_used_fields = List.exists Fun.id dummies in
  { smb_scrutinee = scrut_v;
    smb_ctor_type = ctor_type;
    smb_var = (if has_used_fields then Some sname else None);
    smb_field_bindings =
      (if has_used_fields then
         List.map (fun (n, ty, _is_uptr, used) -> (n, ty, used)) field_bindings
       else []);
    smb_extra_conds = [];
    smb_is_value_type = is_value_type;
    smb_is_owned = is_owned;
    smb_is_flat = is_flat;
    smb_body = body_stmts }

(** Generate C++ pattern matching for an [MLcase].

    Dispatches based on the inductive's structure:
    - {b Enum types}: generate a [switch] statement on tag values
      ({!gen_enum_branches}).
    - {b Variant types}: generate an if/else-if chain using
      [std::holds_alternative] guards and [std::get] structured bindings
      ({!gen_match_branch}).

    {b Type resolution.}  When the match type contains unresolved [Tvar]s,
    attempts to resolve them from [env_types] so that field types and
    constructor type parameters are concrete for code generation. *)
and gen_cpp_case (typ : ml_type) t env pv =
  (* When the match type annotation has unresolved Tvars, try to resolve from
     context. This handles monomorphic functions where MLcase has Tvar but the
     concrete type is known. *)
  let resolve_tvar_type typ candidate =
    match (typ, candidate) with
    | Miniml.Tglob (r1, _, _), Miniml.Tglob (r2, _, _)
      when globref_equal r1 r2
           && has_tvar typ
           && not (has_tvar candidate) -> candidate
    | _ -> typ
  in
  let typ =
    match t with
    | MLrel i | MLmagic (MLrel i) ->
      (* Scrutinee is a variable reference — use its concrete type. Try
         env_types first (correctly tracks let-bound variables with shifted de
         Bruijn indices), then fall back to param_types. Unwrap Tmeta wrappers
         since env_types may store types in Tmeta form. *)
      let rec unwrap_tmeta = function
        | Miniml.Tmeta {contents = Some t} -> unwrap_tmeta t
        | t -> t
      in
      let env_ty_opt =
        try
          let env_ty = unwrap_tmeta (get_env_type i) in
          match env_ty with
          | Miniml.Tglob _ -> Some env_ty
          | _ -> None
        with _ -> None
      in
      ( match env_ty_opt with
      | Some let_ty -> resolve_tvar_type typ let_ty
      | None ->
      match get_param_type_by_index i with
      | Some (Miniml.Tglob _ as param_ty) -> resolve_tvar_type typ param_ty
      | _ -> typ )
    | MLapp (func_expr, _) | MLmagic (MLapp (func_expr, _)) ->
      (* Scrutinee is a function call — use function's return type *)
      let func_ref =
        match func_expr with
        | MLglob (r, _) | MLmagic (MLglob (r, _)) -> Some r
        | _ -> None
      in
      ( match func_ref with
      | Some r ->
        ( match find_type_opt r with
        | Some ty ->
          let ret_ty = ml_return_type ty in
          resolve_tvar_type typ ret_ty
        | None -> typ )
      | None -> typ )
    | _ -> typ
  in
  (* When the type is still unresolved (Tunknown / Tdummy / non-Tglob) but the
     scrutinee is MLmagic (erased at runtime), recover the inductive type from
     the first branch's constructor pattern.  This handles dependent fields
     (e.g. sigT's second projection) stored as std::any. *)
  let scrut_is_mlmagic_case = match t with MLmagic _ -> true | _ -> false in
  let typ =
    match typ with
    | Miniml.Tglob _ -> typ
    | _ when scrut_is_mlmagic_case ->
      ( try
          let _, _, pat0, _ = pv.(0) in
          match pat0 with
          | Pusual (GlobRef.ConstructRef (ip, _))
          | Pcons (GlobRef.ConstructRef (ip, _), _) ->
            Miniml.Tglob (GlobRef.IndRef ip, [], [])
          | _ -> typ
        with _ -> typ )
    | _ -> typ
  in
  (* Check if this is an enum inductive type *)
  let is_enum =
    match typ with
    | Miniml.Tglob (GlobRef.IndRef (kn, i), _, _) ->
      is_enum_inductive (GlobRef.IndRef (kn, i))
    | _ -> false
  in
  (* Check if this is a flat single-constructor inductive type *)
  let is_flat_match =
    match typ with
    | Miniml.Tglob (r, _, _) -> Table.is_flat_inductive r
    | _ -> false
  in
  if is_enum then (* Generate switch-based matching wrapped in IIFE *)
    let ind_ref =
      match typ with
      | Miniml.Tglob (r, _, _) -> r
      | _ ->
        CErrors.anomaly (Pp.str "gen_case_cpp: enum type expected to be Tglob")
    in
    let scrutinee = gen_expr env t in
    let rec gen_enum_branches = function
      | [] -> []
      | (ids, _rty, p, body) :: cs ->
      match p with
      | Pusual r | Pcons (r, _) ->
        let _ids', env' =
          push_vars'
            (List.rev_map
               (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
               ids )
            env
        in
        let ctor_name =
          match r with
          | GlobRef.ConstructRef ((kn, i), cidx) ->
            Id.of_string (Table.enum_ctor_name_of_ref kn i cidx)
          | _ -> Id.of_string (Common.enum_ctor_name_of_id
                   (Table.safe_basename_of_global r))
        in
        let body_stmts = gen_stmts env' (fun x -> Sreturn (Some x)) body in
        (ctor_name, body_stmts) :: gen_enum_branches cs
      | Pwild | Prel _ | Ptuple _ -> gen_enum_branches cs
    in
    let gen_default_stmts () =
      let wild_br =
        Array.to_list pv
        |> List.find_opt (fun (_, _, p, _) -> match p with Pwild -> true | _ -> false)
      in
      Option.map (fun (_, _, _, body) -> gen_stmts env (fun x -> Sreturn (Some x)) body) wild_br
    in
    let tvars = get_current_type_vars () in
    (* Compute IIFE return type.  Void: [-> void] is required when the lambda
       may have no return statement.  Function-typed ([Tfun _]): emit the
       explicit [std::function<R(A...)>] type so that branches returning
       distinct lambda closure types can all be implicitly converted via
       [std::function]'s converting constructor; without it, C++ cannot deduce
       a common return type from distinct closures.  Other non-void: [None]
       lets C++ deduce, which avoids leaking unresolved Tvars (e.g. [T1])
       from the ML type annotation into non-template contexts. *)
    let iife_ret_opt =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = convert_ml_type_to_cpp_type env tvars branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_unit (ml_result_type branch_rty)
      then Some Tvoid
      else match r with
        | Tfun _ -> Some r
        | _ -> None
    in
    let saved_ret = tctx.current_cpp_return_type in
    if iife_ret_opt = Some Tvoid then
      tctx.current_cpp_return_type <- Some Tvoid;
    let branches = gen_enum_branches (Array.to_list pv) in
    let default = gen_default_stmts () in
    tctx.current_cpp_return_type <- saved_ret;
    CPPfun_call
      (CPPlambda ([], iife_ret_opt, [Sswitch (scrutinee, ind_ref, branches, default)], false), [])
  else
    (* Generate if/else-if pattern matching using [std::holds_alternative]
       and [std::get].  Produces an {!Smatch} node wrapped in an IIFE. *)
    let scrut_db =
      match t with
      | MLrel i -> Some i
      | MLmagic (MLrel i) -> Some i
      | _ -> None
    in
    (* Allocate a unique [_m] name for this match level.  All branches of
       the same match reuse this name (each [if (auto* _m = ...)] creates
       its own scope); nested matches get the next name ([_m0], [_m1]). *)
    let match_i = tctx.match_param_counter in
    tctx.match_param_counter <- match_i + 1;
    let sname =
      Id.of_string
        ( if match_i = 0 then "_m"
          else "_m" ^ string_of_int (match_i - 1) )
    in
    (* Generate scrutinee expression.  Clear [move_dead_after] to prevent
       [std::move(x)->v()] use-after-move — the scrutinee is referenced
       across all branches. *)
    let saved_dead_visit = tctx.move_dead_after in
    tctx.move_dead_after <- Escape.IntSet.empty;
    let scrut_expr = gen_expr env t in
    tctx.move_dead_after <- saved_dead_visit;
    (* When the scrutinee is MLmagic (runtime std::any) and we recovered a
       concrete inductive type from branch patterns, wrap with any_cast. *)
    let scrut_expr =
      if scrut_is_mlmagic_case then
        let tvars = get_current_type_vars () in
        let cpp_ty = convert_ml_type_to_cpp_type env tvars typ in
        if not (is_erased_type cpp_ty) then
          CPPany_cast (cpp_ty, scrut_expr)
        else scrut_expr
      else scrut_expr
    in
    (* Methodification rewrites the receiver parameter to [this] (or [*this]
       when the value is needed).  Ownership analysis may still mark the
       original parameter as owned, but a const method cannot decompose the
       receiver through [v_mut()].  Treat receiver matches as borrowed so
       generated access goes through [v()]. *)
    let scrut_is_owned =
      match scrut_expr with
      | CPPthis | CPPderef CPPthis -> false
      | _ -> (
        match scrut_db with
        | Some i -> Escape.IntSet.mem i tctx.move_owned_vars
        | None -> false )
    in
    (* Build variant accessor.  All inductives (including coinductives)
       are value types and use [scrut.v()] (dot access).  Exception:
       [this] is always a pointer, so method bodies use [this->v()].
       For flat types (no variant wrapper), use the scrutinee directly. *)
    let scrut_is_ptr =
      match scrut_expr with CPPthis -> true | _ -> false
    in
    let scrut_v =
      if is_flat_match then
        scrut_expr
      else if scrut_is_ptr then
        CPPmethod_call (scrut_expr, Id.of_string "v", [])
      else
        CPPfun_call (CPPmember (scrut_expr, Id.of_string "v"), [])
    in
    (* Push renamed pattern variables into the environment, register their
       types in [env_types], and compute a dummies mask (true = non-Dummy).
       The caller is responsible for saving/restoring env_types. *)
    let process_match_pattern_vars ids env =
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      let env_ids' = retype_dependent_params typ ids' in
      push_env_types env_ids';
      let dummies =
        List.map (fun (x, _) -> match x with Dummy -> false | _ -> true) ids
      in
      (ids', env', dummies)
    in
    (* Generate one {!smatch_branch} per constructor pattern, collecting
       a wildcard body from [Pwild] / [Prel]. *)
    let rec gen_branches = function
      | [] -> ([], None)
      | (ids, rty, p, body) :: cs ->
      match p with
      | Pusual r | Pcons (r, _) ->
        let saved_env_types = tctx.env_types in
        let saved_erased = save_erased_env () in
        let ids', env', dummies = process_match_pattern_vars ids env in
        let br =
          gen_match_branch env' typ rty r ids' dummies body sname
            match_i scrut_v
            ~is_value_type:true
            ~is_owned:scrut_is_owned
            ~scrut_db
            ~is_flat:is_flat_match
        in
        tctx.env_types <- saved_env_types;
        restore_erased_env saved_erased;
        let rest, wild = gen_branches cs in
        (br :: rest, wild)
      | Pwild | Prel _ ->
        let body_stmts =
          gen_stmts env (fun x -> Sreturn (Some x)) body
        in
        ([], Some body_stmts)
      | Ptuple _ -> gen_branches cs
    in
    let branches, wildcard = gen_branches (Array.to_list pv) in
    (* Compute IIFE return type.  Void: [-> void] is required when the lambda
       may have no return statement.  Function-typed ([Tfun _]): emit the
       explicit [std::function<R(A...)>] type so that branches returning
       distinct lambda closure types can all be implicitly converted via
       [std::function]'s converting constructor; without it, C++ cannot deduce
       a common return type from distinct closures.  Other non-void: [None]
       lets C++ deduce, which avoids leaking unresolved Tvars (e.g. [T1])
       from the ML type annotation into non-template contexts. *)
    let tvars = get_current_type_vars () in
    let iife_ret_opt =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = convert_ml_type_to_cpp_type env tvars branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_unit (ml_result_type branch_rty)
      then Some Tvoid
      else match r with
        | Tfun _ -> Some r
        | _ -> None
    in
    CPPfun_call
      ( CPPlambda ([], iife_ret_opt,
          [Smatch (branches, wildcard)], false),
        [] )

(** Generate a custom match body using user-provided custom extraction syntax.
    Wraps the body in a lambda with pattern-bound variables for std::visit. *)
and collect_recursive_ns ml_ty =
  (* Collect self-recursive inductive types that appear *nested inside* ml_ty
     and return them as a namespace set so convert_ml_type_to_cpp_type wraps
     them with Tshared_ptr when they appear as field references.

     The top-level type itself is NOT added: a binding variable h : T has the
     same C++ type as the deque element (e.g. `const T&` from `front()`), not
     `shared_ptr<T>`.  Recursive wrapping is only needed when T appears as a
     *field* of an enclosing composite type (e.g. `pair<string, json_value>`
     → field `json_value` wrapped as `shared_ptr<json_value>`). *)
  let rec collect_nested acc = function
    | Miniml.Tglob (GlobRef.IndRef _ as g, args, _) ->
      let acc' =
        if Table.has_recursive_fields g && not (Table.is_custom g)
        then Refset'.add g acc
        else acc
      in
      List.fold_left collect_nested acc' args
    | Miniml.Tarr (a, b) -> collect_nested (collect_nested acc a) b
    | Miniml.Tmeta {contents = Some t} -> collect_nested acc t
    | _ -> acc
  in
  (* Start from the args of the top-level type so the top-level itself
     is never added to the namespace. *)
  match ml_ty with
  | Miniml.Tglob (_, args, _) ->
    List.fold_left collect_nested Refset'.empty args
  | Miniml.Tarr (a, b) ->
    collect_nested (collect_nested Refset'.empty a) b
  | Miniml.Tmeta {contents = Some t} -> collect_recursive_ns t
  | _ -> Refset'.empty

(** True when environment variable at de Bruijn index [i] has an erased C++
    type (i.e. [std::any] or a dummy type, arising from dependent-parameter
    collapse).  Returns [false] if [i] is out of range. *)
and is_env_var_erased env tvars i =
  match get_env_type_opt i with
  | Some ml_ty ->
    is_erased_type (convert_ml_type_to_cpp_type env tvars ml_ty)
  | None -> false

and gen_cpp_custom_body env k rty ids body scrut_ind_opt =
  let tvars = get_current_type_vars () in
  let ret = convert_ml_type_to_cpp_type env tvars rty in
  let ids =
    List.map
      (fun (x, ty) ->
        let ns =
          match scrut_ind_opt with
          | Some g_scrut when not (is_prod_global g_scrut) ->
            (* Use {g_scrut} as the namespace so that type args that are
               self-references of the scrutinee get shared_ptr wrapping —
               matching struct field storage.  Exception 1: when the
               scrutinee is a product/pair (grammar production context),
               fall through to collect_recursive_ns which correctly uses
               the binding variable's own type to find recursive inductives.
               Exception 2: when the binding type IS g_scrut directly (a
               non-parametric direct self-ref dereferenced by the custom
               match template), use empty ns so the binding is a value type
               rather than shared_ptr. *)
            let is_direct_self_ref =
              match ty with
              | Miniml.Tglob (g, [], _) -> GlobRef.CanOrd.equal g g_scrut
              | _ -> false
            in
            if is_direct_self_ref then Refset'.empty
            else Refset'.singleton g_scrut
          | _ -> collect_recursive_ns ty
        in
        (x, convert_ml_type_to_cpp_type env ~ns tvars ty) )
      (List.rev ids)
  in
  (* Wrap erased variables with any_cast when returned as a template parameter. *)
  let k =
    match ret with
    | Tvar _ ->
      let body_is_erased =
        match body with
        | MLrel i ->
          not (Escape.IntSet.mem i tctx.cpp_erased_env) && is_env_var_erased env tvars i
        | Miniml.MLmagic (MLrel i) ->
          not (Escape.IntSet.mem i tctx.cpp_erased_env) && is_env_var_erased env tvars i
        | _ -> false
      in
      if body_is_erased then (fun e -> k (CPPany_cast (ret, e)))
      else k
    | _ -> k
  in
  let body = gen_stmts env k body in
  (ids, ret, body)

(** Test whether a C++ expression is "trivial" — a simple variable or member
    access that can safely be duplicated without side effects.  Non-trivial
    expressions (function calls, constructor applications, etc.) should be
    cached in a temporary when the custom match template uses [%scrut] more
    than once. *)
and is_trivial_scrut = function
  | CPPvar _ | CPPget _ | CPPget' _ | CPParrow _ | CPPmember _
  | CPPqualified _ | CPPderef _ | CPPenum_val _ | CPPglob _ -> true
  | _ -> false

(** Generate a custom case expression using user-provided extraction syntax.
    Entry point for custom pattern match generation.
    Returns a [cpp_stmt list]: when the scrutinee is non-trivial and the
    template uses [%scrut] more than once, a cache declaration
    [auto _cs = expr;] is prepended before the [Scustom_case] node. *)
and gen_custom_cpp_case env k (typ : ml_type) t pv =
  let tvars = get_current_type_vars () in
  (* Save the ML type for temps computation after fix_a_fired is known. *)
  let ml_typ = typ in
  (* [scrut_is_magic]: true when the scrutinee is erased at runtime (stored as
     [std::any]) even though the ML AST may carry a concrete type annotation.
     Covers both explicit [Obj.magic] wrappers and variables retyped to [Tany]
     by an outer [fix_a_fired] pair match (detected via [env_types]). *)
  let scrut_is_mlmagic = match t with MLmagic _ -> true | _ -> false in
  let scrut_is_cpp_erased = match t with
    | MLrel i -> Escape.IntSet.mem i tctx.cpp_erased_env
    | _ -> false
  in
  let scrut_is_magic = match t with
    | MLmagic _ -> true
    | MLrel i ->
      Escape.IntSet.mem i tctx.cpp_erased_env
      || (match get_env_type_opt i with
          | Some ty -> is_erased_ml_type ty
          | None -> false)
    | _ -> false
  in
  let typ = convert_ml_type_to_cpp_type env tvars typ in
  (* [concrete_match_type]: when [typ] is erased ([std::any]), recover the
     actual inductive type from the first branch's pattern constructor and
     its field types.  Used for non-pair matches (e.g. option, variant) where
     we need to emit [any_cast<ConcreteType>(scrut)]. *)
  let concrete_match_type =
    if is_erased_type typ then
      try
        let _, _, pat0, _ = pv.(0) in
        let ind_ref = match pat0 with
          | Pusual (GlobRef.ConstructRef (ip, _))
          | Pcons (GlobRef.ConstructRef (ip, _), _) -> GlobRef.IndRef ip
          | _ -> raise Not_found
        in
        let ids0, _, _, _ = pv.(0) in
        let tyargs = List.rev_map (fun (_, ty) ->
          erase_unresolved_tvars (convert_ml_type_to_cpp_type env tvars ty)
        ) ids0 in
        Tglob (ind_ref, tyargs, [])
      with _ -> typ
    else typ
  in
  (* Custom match templates may use %scrut multiple times (e.g., option: "if
     (%scrut.has_value()) { ... *%scrut; ... }"). Each occurrence re-prints the
     scrutinee C++ expression, so any std::move in the scrutinee would fire
     multiple times. Suppress moves when the template duplicates the
     scrutinee. *)
  let cmatch = find_custom_match pv in
  let scrut_uses =
    let plen = 6 in
    (* length of "%scrut" *)
    let n = String.length cmatch in
    let rec count i acc =
      if i + plen > n then
        acc
      else if String.sub cmatch i plen = "%scrut" then
        count (i + plen) (acc + 1)
      else
        count (i + 1) acc
    in
    count 0 0
  in
  let pair_g_opt_early = match concrete_match_type with
    | Tglob (g, _, _) when is_prod_global g -> Some g
    | _ -> None
  in
  (* [scrut_is_owned_pair]: true when the scrutinee is a pair whose binding
     is dead after destructuring — enables by-value structured binding to move
     the fields out instead of taking a const reference. *)
  let scrut_is_owned_pair = match t with
    | MLrel i | MLmagic (MLrel i) ->
      Escape.IntSet.mem i tctx.move_owned_vars
      && Array.length pv = 1
      && (let (ids, _, _, body) = pv.(0) in
          let n = List.length ids in
          Escape.nb_occur_match (i + n) body = 0)
    | _ ->
      Array.length pv = 1
      && pair_g_opt_early <> None
  in
  (* Before generating the scrutinee, mark owned vars that are dead after
     the scrutinee (not used in any branch body) so they get std::move. *)
  let saved_dead = tctx.move_dead_after in
  let dead_in_scrut =
    if Escape.IntSet.is_empty tctx.move_owned_vars then
      Escape.IntSet.empty
    else
      let branch_free =
        Array.fold_left (fun acc (ids, _, _, body) ->
          let n = List.length ids in
          Escape.IntSet.union acc (Escape.free_rels n body))
          Escape.IntSet.empty pv
      in
      Escape.IntSet.filter (fun i ->
        not (Escape.IntSet.mem i branch_free)
        && Escape.nb_occur_match i t = 1)
        tctx.move_owned_vars
  in
  let scrut_is_trivial_ml = match t with
    | MLrel _ | MLmagic (MLrel _) -> true
    | _ -> false
  in
  if scrut_uses > 1 && scrut_is_trivial_ml then
    tctx.move_dead_after <- Escape.IntSet.empty
  else
    tctx.move_dead_after <- Escape.IntSet.union saved_dead dead_in_scrut;
  let t = gen_expr env t in
  tctx.move_dead_after <- saved_dead;
  let pair_g_opt = match concrete_match_type with
    | Tglob (g, _, _) when is_prod_global g -> Some g
    | _ -> None
  in
  (* Insert [any_cast] on the scrutinee when the runtime value is [std::any]
     but the template needs a typed expression.

     For pair matches: the runtime encoding is always [pair<any,any>] at every
     nesting level (built by [concat_tuple]/[rev_tuple_cons_case]).  Cast to
     [pair<any,any>] regardless of the static type and set [fix_a_fired=true]
     so downstream passes know the fields are [std::any].

     For non-pair matches (option, variant, etc.) when [scrut_is_magic]: cast
     to [concrete_match_type] recovered from the branch pattern.

     Otherwise: no cast needed; the scrutinee already has the correct type. *)
  let t, fix_a_fired =
    let needs_pair_any_cast =
      pair_g_opt <> None &&
      ( scrut_is_cpp_erased || scrut_is_mlmagic
        || (scrut_is_magic && is_erased_type typ)
        || (is_erased_type typ || is_all_erased typ) &&
           ( Ml_type_util.has_tany_in_type concrete_match_type
             || (match concrete_match_type with
                 | Tglob (_, args, _) -> List.exists resolves_to_any_type args
                 | _ -> false) ) )
    in
    if needs_pair_any_cast then begin
      let g = Option.get pair_g_opt in
      (CPPany_cast (Tglob (g, [Tany; Tany], []), t), true)
    end
    else if (scrut_is_mlmagic || (scrut_is_magic && is_erased_type typ)
             || scrut_is_cpp_erased)
            && not (is_erased_type concrete_match_type) then
      (* Erase template args one level deep, preserving nested generic structure.
         E.g., deque<pair<T1,T2>> → deque<pair<any,any>>, deque<T> → deque<any>.
         This ensures runtime types match: a deque<pair<any,any>> stored as any
         must be cast as deque<pair<any,any>>, not deque<any>. *)
      let erase_tparams = function
        | Tglob (_, [], _) -> Tany
        | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
        | _ -> Tany
      in
      let cast_ty = match concrete_match_type with
        | Tglob (g, (_ :: _ as args), ns) when scrut_is_mlmagic ->
          Tglob (g, List.map erase_tparams args, ns)
        | _ -> concrete_match_type
      in
      (CPPany_cast (cast_ty, t), false)
    else
      (t, false)
  in
  (* When [fix_a_fired], pass [pair<any,any>] as the [Scustom_case] type so
     that [wrap_any_cast_if_needed] in [cpp_print.ml] generates
     [any_cast<pair<any,any>>] instead of using the concrete nested pair type. *)
  let case_typ =
    if fix_a_fired then
      match pair_g_opt with
      | Some g -> Tglob (g, [Tany; Tany], [])
      | None -> typ
    else typ
  in
  (* Compute template type parameters ([%t0], [%t1], ...) after [fix_a_fired]
     is known.  When [fix_a_fired], the scrutinee is cast to [pair<any,any>],
     so all fields are [std::any] regardless of the original field types.
     Force [Tauto] so the binding uses [auto] and C++ deduces the type.
     Also force [Tauto] when a type contains erased positions ([Tany]),
     since an explicit type annotation would block valid concrete-type calls. *)
  let temps =
    match ml_typ with
    | Tglob (_, tys, _) ->
      let raw = build_template_params env tvars tys in
      List.map (fun ty ->
        if fix_a_fired || has_tany_in_type ty then Tauto else ty) raw
    | _ -> []
  in
  (* When the template uses %scrut more than once and the scrutinee is a
     non-trivial expression (function call, constructor, etc.), cache it in
     a temporary to avoid double evaluation. *)
  let scrut, cache_prefix =
    if scrut_uses > 1 && not (is_trivial_scrut t) then begin
      let n = tctx.cs_counter in
      tctx.cs_counter <- n + 1;
      let cache_id =
        Id.of_string (if n = 0 then "_cs" else "_cs" ^ string_of_int n)
      in
      match lift_iife_assignment cache_id Ttodo t with
      | Some stmts -> (CPPvar cache_id, stmts)
      | None -> (CPPvar cache_id, [Sasgn (cache_id, Some Ttodo, t)])
    end else begin
      (t, [])
    end
  in
  (* When the scrutinee is an owned pair (last use), override the template
     with a by-value structured binding to move the fields out. *)
  let cmatch =
    if scrut_is_owned_pair && pair_g_opt <> None && not fix_a_fired then
      "auto [%b0a0, %b0a1] = %scrut; %br0"
    else cmatch
  in
  (* Generate [(params, ret_ty, body)] triples for each branch.  Handles env
     retyping for [fix_a_fired], move tracking for owned pairs, use-site
     [any_cast] insertion, and template-arg stripping for erased arguments. *)
  let rec gen_cases = function
    | [] -> []
    | (ids, rty, p, t) :: cs ->
    match p with
    | Pusual r | Pcons (r, _) ->
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      (* When [fix_a_fired], all pair fields are [std::any] at runtime.
         Variables whose C++ type is a pair (e.g. [pair<any,pair<any,…>>]) are
         also [std::any] — they came from [.second] of a [pair<any,any>].
         Re-type them as [Tany] so that:
         (1) inner pair matches see an erased scrutinee and emit [any_cast],
         (2) [cpp_print.ml] registers them as any-typed for
             [wrap_any_cast_if_needed].
         Non-pair leaf types (e.g. [List<any>]) are left unchanged so the
         use-site [any_cast] pass can still insert the correct cast. *)
      let ids' =
        if fix_a_fired then
          let tvars = get_current_type_vars () in
          List.map (fun (x, ty) ->
            let cpp_ty = convert_ml_type_to_cpp_type env tvars ty in
            match cpp_ty with
            | Tglob (g, (_ :: _), _) when is_prod_global g ->
              (x, Tdummy Ktype)
            | Tglob (g, _, _) when is_list_global g ->
              (x, ty)
            | _ when is_erased_type cpp_ty ->
              (x, ty)
            | _ ->
              (x, Tdummy Ktype))
            ids'
        else ids'
      in
      let scrut_elems_are_any =
        (scrut_is_mlmagic || scrut_is_magic)
        && (match ml_typ with
            | Tglob (g, _ :: _, _) when is_list_global g && Table.is_custom g -> true
            | _ -> false)
      in
      let ids' = retype_dependent_params ml_typ ids' in
      let n_pat_vars = List.length ids in
      let saved_env_types = tctx.env_types in
      let saved_owned = tctx.move_owned_vars in
      push_env_types ids';
      (* When [fix_a_fired] and the outer scrutinee was truly [pair<any,any>]
         at runtime (i.e. outer [typ] was erased, not just magic-wrapped),
         ALL fields are [std::any] at runtime.  Mark them in [cpp_erased_env]
         so that [gen_expr] emits [any_cast<T>] when they're used at concrete
         types, and so inner pair matches emit [any_cast<pair<any,any>>].
         Use original [ids] types (not the retyped [ids']) to detect field types. *)
      if fix_a_fired then begin
        List.iteri (fun field_i _ ->
          let db_idx = n_pat_vars - field_i in
          tctx.cpp_erased_env <- Escape.IntSet.add db_idx tctx.cpp_erased_env)
          ids
      end;
      let non_erased_def_tys =
        let def_site_field_tys =
          match Table.get_ctor_ip_types_opt r with
          | Some tys -> tys | None -> []
        in
        List.filter (fun t -> not (isTdummy t)) def_site_field_tys
      in
      populate_erased_field_env ~cname:r ~typ:ml_typ ~env ~n_pat_vars
        ~n_fields:(List.length ids)
        ~non_erased_def_site_field_tys:non_erased_def_tys;
      if scrut_elems_are_any then begin
        let n_fields = List.length ids in
        List.iteri (fun field_i _ ->
          let is_self_ref =
            match List.nth_opt non_erased_def_tys field_i with
            | Some (Tglob (g, _, _)) -> is_list_global g
            | _ -> false
          in
          if not is_self_ref then begin
            let db_idx = n_pat_vars - field_i in
            tctx.cpp_erased_env <- Escape.IntSet.add db_idx tctx.cpp_erased_env
          end)
          (List.init n_fields Fun.id)
      end;
      let pat_owned =
        if scrut_is_owned_pair && pair_g_opt <> None && not fix_a_fired then
          let ids_rev = List.rev ids in
          List.fold_left (fun acc j ->
            let (_, ty) = List.nth ids_rev j in
            if is_nontrivial_value_ml_type ty
               || Escape.is_shared_ptr_type ty then
              Escape.IntSet.add (j + 1) acc
            else acc)
            Escape.IntSet.empty (List.init n_pat_vars Fun.id)
        else Escape.IntSet.empty
      in
      let scrut_ind_opt =
        match ml_typ with
        | Tglob (GlobRef.IndRef _ as g, _, _) -> Some g
        | _ -> None
      in
      let (br_ids, br_ret, br_stmts) =
        with_shifted_move_tracking n_pat_vars ~add_owned_set:pat_owned (fun () ->
          gen_cpp_custom_body env' k rty ids' t scrut_ind_opt)
      in
      tctx.env_types <- saved_env_types;
      tctx.move_owned_vars <- saved_owned;
      (* Use-site [any_cast] insertion: when [fix_a_fired], pair fields are all
         [std::any] at the binding site.  Pattern variables whose C++ type is
         concrete need [any_cast<T>] at each use site so the body compiles.
         Special cases:
         - Pair-typed vars use [pair<any,any>] (not the static type) because
           the runtime encoding always nests [pair<any,any>].
         - List vars use a converting constructor [List<T>(any_cast<List<any>>)]
           so element types are cast correctly.
         - Opaque type aliases / qualified member types are passed through
           as-is (the stored value IS the payload, not wrapped in [any]). *)
      let br_stmts =
        if fix_a_fired then
          List.fold_left
            (fun stmts (name, cpp_ty) ->
               if not (is_erased_type cpp_ty) then
                 let strip_ns_tglob = function
                   | Tnamespace (_, (Tglob _ as inner)) -> inner
                   | t -> t
                 in
                 let stripped = strip_ns_tglob cpp_ty in
                 let cast_expr =
                   match stripped with
                   | Tglob (g, _, _) when is_prod_global g ->
                     CPPany_cast (Tglob (g, [Tany; Tany], []), CPPvar name)
                   | Tglob (g, [_], _) when is_list_global g && not (Table.is_custom g) ->
                     (* List<T> is stored as List<any> by grammar productions —
                        use the converting constructor List<T>(any_cast<List<any>>(v))
                        so each element is any_cast'd correctly.
                        Preserve any Tnamespace wrapper for correct rendering. *)
                     let list_any_ty =
                       match cpp_ty with
                       | Tnamespace (ns_g, _) ->
                         Tnamespace (ns_g, Tglob (g, [Tany], []))
                       | _ -> Tglob (g, [Tany], [])
                     in
                     CPPconverting_ctor (cpp_ty,
                       [CPPany_cast (list_any_ty, CPPvar name)])
                   | Tglob (g, [_], _) when is_list_global g && Table.is_custom g ->
                     CPPvar name
                   | Tqualified _ | Tglob (GlobRef.ConstRef _, _, _) ->
                     (* Opaque type alias (e.g. nt_semty = std::any) or
                        qualified member type (e.g. typename Ty::sym_semty):
                        the stored value IS the concrete payload, NOT a std::any
                        wrapping it. any_cast<std::any>(any(V)) throws; pass
                        the std::any value as-is. *)
                     CPPvar name
                   | _ -> CPPany_cast (cpp_ty, CPPvar name)
                 in
                 List.map
                   (local_var_subst_stmt name cast_expr)
                   stmts
               else stmts)
            br_stmts
            br_ids
        else br_stmts
      in
      (* Strip explicit template type args from function calls where any
         argument has erased-type content (either wrapped in [any_cast<T>]
         with [Tany] inside, or a pattern var whose C++ type contains [Tany]).
         Lets C++ deduce the correct type from the argument itself instead of
         using a stale concrete annotation that conflicts with the erased
         runtime type. *)
      let br_stmts =
        let tany_pat_var_names =
          if not fix_a_fired then
            List.fold_left (fun acc (name, cpp_ty) ->
              if has_tany_in_type cpp_ty then Id.Set.add name acc else acc)
              Id.Set.empty br_ids
          else Id.Set.empty
        in
        let should_strip args =
          List.exists (function
            | CPPany_cast (ty, _) -> has_tany_in_type ty
            | CPPvar name -> Id.Set.mem name tany_pat_var_names
            | _ -> false) args
        in
        if fix_a_fired || not (Id.Set.is_empty tany_pat_var_names) then
          let rec fix_expr e = match e with
            | CPPfun_call (CPPglob (r, _ :: _, ci), args)
              when should_strip args ->
              CPPfun_call (CPPglob (r, [], ci), List.map fix_expr args)
            | _ -> map_expr fix_expr fix_stmt Fun.id e
          and fix_stmt s = map_stmt fix_expr fix_stmt Fun.id s in
          List.map fix_stmt br_stmts
        else br_stmts
      in
      (* Wrap erased pattern variables with any_cast when returned as a template parameter. *)
      let br_stmts =
        match br_ret with
        | Tvar _ ->
          let erased_pat_vars =
            List.fold_left (fun acc (name, cpp_ty) ->
              if is_erased_type cpp_ty then Id.Set.add name acc else acc)
              Id.Set.empty br_ids
          in
          if Id.Set.is_empty erased_pat_vars then br_stmts
          else
            List.map (function
              | Sreturn (Some (CPPvar name))
                when Id.Set.mem name erased_pat_vars ->
                Sreturn (Some (CPPany_cast (br_ret, CPPvar name)))
              | s -> s)
              br_stmts
        | _ -> br_stmts
      in
      (br_ids, br_ret, br_stmts) :: gen_cases cs
    | Pwild | Prel _ | Ptuple _ -> gen_cases cs
  in
  cache_prefix @
  [Scustom_case (case_typ, scrut, temps, gen_cases (Array.to_list pv), cmatch)]

(** {2 IIFE Inlining}

    When [gen_expr] wraps multi-statement code in an immediately-invoked
    function expression (IIFE):
    {[
      [&]() \{
        unsigned int x = p->px;
        unsigned int y = p->py;
        return (x + y);
      \}()
    ]}
    and the result is consumed at statement level (e.g. by [Sreturn] or
    [Sasgn]), the lambda wrapper is unnecessary.  {!inline_iife} detects
    this pattern and flattens the body statements, replacing the final
    [return] with the enclosing continuation:
    {[
      unsigned int x = p->px;
      unsigned int y = p->py;
      return (x + y);
    ]}
    This produces more readable C++ and avoids interfering with compiler
    optimisations (e.g. copy elision / RVO through a lambda boundary). *)

(** Extract block template info from an inline custom expression.
    Returns [Some(ref, template, args, tyargs)] if the expression is
    an inline custom whose template contains [%result]. *)
and extract_block_template = function
  | CPPglob (ref, tys, Some ci) -> begin
    match ci.ci_inline with
    | Some tmpl when Common.contains_substring tmpl "%result" ->
      Some (ref, tmpl, [], tys)
    | _ -> None
    end
  | CPPfun_call (CPPglob (ref, tys, Some ci), args) -> begin
    match ci.ci_inline with
    | Some tmpl when Common.contains_substring tmpl "%result" ->
      Some (ref, tmpl, List.rev args, tys)
    | _ -> None
    end
  | _ -> None

(** [inline_iife k expr] checks whether [expr] is an IIFE
    ([CPPfun_call(CPPlambda(\[\], _, body, _), \[\])]).  If so, it replaces
    the final [Sreturn(Some v)] in [body] with [k v] and returns the
    inlined statement list.  Otherwise it falls back to [\[k expr\]].

    Only zero-argument, zero-parameter IIFEs are inlined — parameterised
    lambdas and those with explicit return-type annotations involving
    captures are left untouched, since they may have name-scoping or
    type-deduction side-effects.

    @param k     the statement-level continuation (e.g. [Sreturn], [Sasgn])
    @param expr  the expression produced by [gen_expr] *)
and inline_iife (k : cpp_expr -> cpp_stmt) = function
  | CPPfun_call (CPPlambda ([], ret_ty, body, _), []) when body <> [] ->
    let k_is_return =
      match k (CPPint 0) with Sreturn _ -> true | _ -> false
    in
    if not k_is_return then
      (* Non-return continuations (e.g. Sasgn for let-bindings) keep the
         IIFE to prevent name clashes between variables from separately
         inlined IIFEs in the same block scope. *)
      [k (CPPfun_call (CPPlambda ([], ret_ty, body, false), []))]
    else
    (* Replace each [Sreturn(Some v)] in the IIFE body with [k(v)] and
       emit the body statements directly, eliminating the lambda wrapper.

       Since k is guaranteed to produce [Sreturn], inlining into
       [Sswitch] and [Scustom_case] is safe — [return] preserves the
       "exit the enclosing case" semantics.  [Sif] is always safe
       because if/else branches are mutually exclusive. *)
    let map_all_or_none transform branches =
      let results = List.map transform branches in
      if List.for_all (fun x -> x <> None) results then
        Some (List.filter_map Fun.id results)
      else None
    in
    let rec replace_last_return = function
      | [Sreturn (Some v)] -> Some [k v]
      | [Sreturn None] -> None  (* void return — cannot apply k *)
      | [Sif (c, then_br, else_br)] ->
        ( match (replace_last_return then_br, replace_last_return else_br) with
        | Some then_br', Some else_br' -> Some [Sif (c, then_br', else_br')]
        | _ -> None )
      | [Sswitch (scrut, ind_ref, branches, default)] ->
        let default' =
          match default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (id, stmts) ->
              Option.map (fun stmts' -> (id, stmts')) (replace_last_return stmts))
            branches, default')
        with
        | Some branches', Some default' -> Some [Sswitch (scrut, ind_ref, branches', default')]
        | _ -> None )
      | [Scustom_case (ty, scrut, tyargs, branches, cmatch)] ->
        Option.map
          (fun branches' -> [Scustom_case (ty, scrut, tyargs, branches', cmatch)])
          (map_all_or_none
            (fun (args, bty, stmts) ->
              Option.map (fun stmts' -> (args, bty, stmts')) (replace_last_return stmts))
            branches)
      | [Smatch (branches, default)] ->
        let default' =
          match default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun br ->
              Option.map (fun body' -> { br with smb_body = body' }) (replace_last_return br.smb_body))
            branches, default')
        with
        | Some branches', Some default' ->
          Some [Smatch (branches', default')]
        | _ -> None )
      | stmt :: rest when rest <> [] ->
        Option.map (fun rest' -> stmt :: rest') (replace_last_return rest)
      | _ -> None
    in
    ( match replace_last_return body with
    | Some stmts -> stmts
    | None -> [k (CPPfun_call (CPPlambda ([], ret_ty, body, false), []))] )
  | expr -> [k expr]

(** Escape analysis for local fixpoint variables.

    Determines whether [target_id] appears in any position other than the
    callee of a direct call [CPPfun_call(CPPvar target_id, args)].  If so,
    the fixpoint "escapes" and must use the [shared_ptr<std::function>]
    pattern (see {!gen_local_fix_shared_ptr}) instead of the simpler [\[&\]]
    capture pattern (see {!gen_local_fix_by_ref}).

    Escape positions include: function argument, constructor field, return
    value, record field, or binding RHS.

    Lambda bodies are treated conservatively: {b any} reference to the
    fixpoint inside a lambda body — even in call position — counts as an
    escape.  This is because the lambda captures the [std::function] value,
    and a [\[&\]]-captured [std::function]'s internal lambda still holds
    dangling stack references when the lambda outlives the fixpoint's scope.

    @param target_id  The fixpoint variable to track.
    @param stmts      The statement list (typically the continuation after
                      the fixpoint's let-binding) to scan.
    @return [true] if the fixpoint escapes. *)
and fixpoint_escapes_in_stmts target_id stmts =
  let rec check_expr e =
    match e with
    | CPPfun_call (CPPvar id, args) when Id.equal id target_id ->
      (* Safe: direct call.  But check the arguments for escapes. *)
      List.exists check_expr args
    | CPPvar id when Id.equal id target_id ->
      true  (* Escape: bare reference outside call position *)
    | CPPlambda (_, _, body, _) ->
      (* Any reference inside a lambda means the fixpoint is captured.
         Even if only called, the capture copies the std::function whose
         internal lambda still has dangling [&] references.
         Must use a properly recursive walker since map_expr/map_stmt
         only do one level of descent. *)
      let rec has_var_in_expr e =
        match e with
        | CPPvar id when Id.equal id target_id -> true
        | _ ->
          let found = ref false in
          let fe e' = if not !found then found := has_var_in_expr e'; e' in
          let fs s' = if not !found then found := has_var_in_stmt s'; s' in
          ignore (Minicpp.map_expr fe fs Fun.id e);
          !found
      and has_var_in_stmt s =
        let found = ref false in
        let on_expr e = if not !found then found := has_var_in_expr e in
        let on_stmts ss =
          if not !found then found := List.exists has_var_in_stmt ss
        in
        Minicpp.iter_stmt_children ~on_expr ~on_stmts s;
        !found
      in
      List.exists has_var_in_stmt body
    | _ ->
      (* Recurse into sub-expressions *)
      let found = ref false in
      let fe e = if not !found then found := check_expr e; e in
      ignore (Minicpp.map_expr fe Fun.id Fun.id e);
      !found
  in
  let rec check_stmt s =
    let found = ref false in
    let on_expr e = if not !found then found := check_expr e in
    let on_stmts ss = if not !found then found := check_stmts ss in
    Minicpp.iter_stmt_children ~on_expr ~on_stmts s;
    !found
  and check_stmts ss = List.exists check_stmt ss
  in
  check_stmts stmts

(** Generate local fixpoint declarations using the [\[&\]]-capture pattern.

    Used when {!fixpoint_escapes_in_stmts} returns [false], meaning the
    fixpoint variable is only used in direct call position and never
    escapes into a closure or data structure.  The [\[&\]] capture is
    lightweight (no heap allocation, no indirection) but creates dangling
    references if the closure outlives the enclosing scope.

    Uses a Y-combinator pattern to avoid [std::function] type erasure
    overhead (heap allocation, virtual dispatch).  Parameters are passed
    by value (same as the old pattern) to preserve move/mutation semantics.

    Generated C++:
    {v
      auto f_impl = [&](auto& _self_f, A a, B b) -> R {
        ... _self_f(_self_f, a', b') ...
      };
      auto f = [&](A a, B b) -> R {
        return f_impl(f_impl, a, b);
      };
    v}

    @return [(decls, defs)] — declaration and definition statement lists.
    @see gen_local_fix_shared_ptr for the escaping-fixpoint alternative. *)
and gen_local_fix_by_ref env renamed_ids funs_with_params owned_flags_per_fun =
  let tvars = get_current_type_vars () in
  let ret_ty ty =
    match convert_ml_type_to_cpp_type env tvars ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (_, None) -> None
      | _ -> Some t )
    | _ -> None
  in
  let self_ids =
    List.map
      (fun (id, _) -> Id.of_string ("_self_" ^ Id.to_string id))
      renamed_ids
  in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  let self_vars_rev = List.rev_map (fun id -> CPPvar id) self_ids in
  let find_self_id id =
    let rec aux ids sids =
      match (ids, sids) with
      | (fix_id, _) :: _, sid :: _ when Id.equal id fix_id -> Some sid
      | _ :: ids', _ :: sids' -> aux ids' sids'
      | _ -> None
    in
    aux renamed_ids self_ids
  in
  let rec rewrite_expr e =
    match e with
    | CPPfun_call (CPPvar id, args) -> (
      match find_self_id id with
      | Some self_id ->
        CPPfun_call
          (CPPvar self_id, List.map rewrite_expr args @ self_vars_rev)
      | None -> CPPfun_call (CPPvar id, List.map rewrite_expr args) )
    | _ -> map_expr rewrite_expr rewrite_stmt Fun.id e
  and rewrite_stmt s = map_stmt rewrite_expr rewrite_stmt Fun.id s in
  let impl_stmts =
    List.map2
      (fun (((_fix_id, fty), impl_id), owned_flags) (args, body) ->
        let self_params =
          List.rev_map (fun sid -> (Tref Tauto, Some sid)) self_ids
        in
        let orig_params =
          List.map2
            (fun (id, ty) owned ->
              let cpp_ty =
                convert_ml_type_to_cpp_type env tvars ty
              in
              ( wrap_param_by_ownership ~is_owned:owned cpp_ty,
                Some id ))
            args owned_flags
        in
        Sasgn
          ( impl_id,
            Some Tauto,
            CPPlambda
              ( orig_params @ self_params,
                ret_ty fty,
                List.map rewrite_stmt body,
                false ) ))
      (List.combine (List.combine renamed_ids impl_ids) owned_flags_per_fun)
      funs_with_params
  in
  let impl_vars_rev = List.rev_map (fun id -> CPPvar id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun (((fix_id, fty), _impl_id), owned_flags) (args, _body) ->
        let orig_params =
          List.map2
            (fun (id, ty) owned ->
              let cpp_ty =
                convert_ml_type_to_cpp_type env tvars ty
              in
              ( wrap_param_by_ownership ~is_owned:owned cpp_ty,
                Some id ))
            args owned_flags
        in
        let fwd_args =
          List.map (fun (id, _) -> CPPvar id) args @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call = CPPfun_call (CPPvar _impl_id, fwd_args) in
        let wrapper_body =
          match rty with
          | None -> [Sexpr call]
          | _ -> [Sreturn (Some call)]
        in
        Sasgn
          ( fix_id,
            Some Tauto,
            CPPlambda (orig_params, rty, wrapper_body, false) ))
      (List.combine (List.combine renamed_ids impl_ids) owned_flags_per_fun)
      funs_with_params
  in
  (impl_stmts @ wrapper_stmts, [])

(** Generate local fixpoint declarations using the shared_ptr fixpoint
    pattern for escaping fixpoints.

    Used when {!fixpoint_escapes_in_stmts} returns [true], meaning the
    fixpoint variable is captured by a closure, stored in a data structure,
    or otherwise outlives its defining scope.  The [\[=\]] capture copies the
    [shared_ptr] into the lambda, keeping the [std::function] alive on the
    heap.  Recursive calls dereference the shared pointer before invoking.

    Generated C++ (schematic):
    - [auto f = make_shared<function<R(A...)>>()] allocates the shared cell.
    - [*f = \[=\](A... args) mutable { ... }] assigns the closure body.
    - Inside the closure, the recursive call dereferences [f] before invoking.

    The lambda is marked [mutable] because the captured [shared_ptr] must be
    non-const to allow the internal [std::function] to be invoked.

    @return [(decls, defs, deref_subst)] where [deref_subst] is a function
    that rewrites [CPPvar fix_id] to [CPPderef(CPPvar fix_id)] in a
    statement list, so that call sites in the continuation use the
    dereferenced form.
    @see gen_local_fix_by_ref for the non-escaping alternative.
    @see Minicpp.Sderef_asgn for the dereference assignment node. *)
and gen_local_fix_shared_ptr env renamed_ids funs_with_params =
  let tvars = get_current_type_vars () in
  let fix_func_type ty =
    match ty with
    | Minicpp.Tfun (params, Minicpp.Tvar (_, None)) ->
      Minicpp.Tfun (params, Minicpp.Tvoid)
    | _ -> ty
  in
  let deref_subst stmts =
    List.fold_left
      (fun s (fix_id, _) ->
        List.map
         (local_var_subst_stmt
             fix_id
             (CPPderef (CPPvar fix_id)))
          s )
      stmts renamed_ids
  in
  let ret_ty ty =
    match convert_ml_type_to_cpp_type env tvars ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (_, None) -> None
      | _ -> Some t )
    | _ -> None
  in
  let decls =
    List.map
      (fun (id, ty) ->
        Sasgn
          ( id,
            Some Tauto,
            CPPfun_call
              ( CPPmk_shared
                  (fix_func_type
                     (convert_ml_type_to_cpp_type env tvars ty)),
                [] ) ) )
      renamed_ids
  in
  let defs =
    List.map2
      (fun (id, _fty) (args, body) ->
        Sderef_asgn
          ( CPPvar id,
            CPPlambda
              ( List.map
                  (fun (id, ty) ->
                    ( convert_ml_type_to_cpp_type env tvars ty,
                      Some id ) )
                  args,
                ret_ty _fty,
                deref_subst body,
                true ) ) )
      renamed_ids funs_with_params
  in
  (decls, defs, deref_subst)

(** Generate local fixpoint declarations using the Y-combinator pattern
    for escaping fixpoints.

    Replaces the [shared_ptr<std::function>] pattern with a generic-lambda
    self-passing pattern:
    {v
      auto go_impl = [=](auto &_self, A... args) mutable -> R {
        ... _self(_self, args) ...
      };
      auto go = [=](A... args) mutable -> R {
        return go_impl(go_impl, args...);
      };
    v}

    No heap allocation, no [std::function] type erasure.  The [auto &_self]
    parameter uses C++14 generic lambdas.

    For mutual recursion with N functions, each impl takes N self parameters:
    {v
      auto f_impl = [=](auto &_sf, auto &_sg, A...) { ... _sg(_sf, _sg, ...) ... };
      auto g_impl = [=](auto &_sf, auto &_sg, A...) { ... _sf(_sf, _sg, ...) ... };
      auto f = [=](A...) { return f_impl(f_impl, g_impl, ...); };
      auto g = [=](A...) { return g_impl(f_impl, g_impl, ...); };
    v}

    @return [(decls, defs, deref_subst)] where [defs] is empty and
    [deref_subst] is the identity function (no dereferencing needed).
    @see gen_local_fix_by_ref for the non-escaping alternative. *)
and gen_local_fix_ycomb env renamed_ids funs_with_params =
  let tvars = get_current_type_vars () in
  let ret_ty ty =
    match convert_ml_type_to_cpp_type env tvars ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (_, None) -> None
      | _ -> Some t )
    | _ -> None
  in
  (* Create self-parameter IDs and impl IDs for each fixpoint. *)
  let self_ids =
    List.map
      (fun (id, _) -> Id.of_string ("_self_" ^ Id.to_string id))
      renamed_ids
  in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  (* The self-parameter CPP vars, in reversed order for prepending to
     reversed arg lists in CPPfun_call nodes. *)
  let self_vars_rev = List.rev_map (fun id -> CPPvar id) self_ids in
  (* Rewrite recursive calls in a body: for each fix_id, replace
     CPPfun_call(CPPvar fix_id, args) with
     CPPfun_call(CPPvar self_id, args @ self_vars_rev). *)
  let find_self_id id =
    let rec aux ids sids =
      match (ids, sids) with
      | (fix_id, _) :: _, sid :: _ when Id.equal id fix_id -> Some sid
      | _ :: ids', _ :: sids' -> aux ids' sids'
      | _ -> None
    in
    aux renamed_ids self_ids
  in
  let rec rewrite_expr e =
    match e with
    | CPPfun_call (CPPvar id, args) -> (
      match find_self_id id with
      | Some self_id ->
        CPPfun_call
          (CPPvar self_id, List.map rewrite_expr args @ self_vars_rev)
      | None -> CPPfun_call (CPPvar id, List.map rewrite_expr args) )
    | _ -> map_expr rewrite_expr rewrite_stmt Fun.id e
  and rewrite_stmt s = map_stmt rewrite_expr rewrite_stmt Fun.id s in
  (* Generate impl lambdas: each takes all self params (auto &) + original params. *)
  let impl_stmts =
    List.map2
      (fun ((_fix_id, fty), impl_id) (args, body) ->
        let self_params =
          List.rev_map (fun sid -> (Tref Tauto, Some sid)) self_ids
        in
        let orig_params =
          List.map
            (fun (id, ty) ->
              (convert_ml_type_to_cpp_type env tvars ty, Some id))
            args
        in
        Sasgn
          ( impl_id,
            Some Tauto,
            CPPlambda
              ( orig_params @ self_params,
                ret_ty fty,
                List.map rewrite_stmt body,
                true ) ))
      (List.combine renamed_ids impl_ids)
      funs_with_params
  in
  (* Generate wrapper lambdas: forward to impl with all impl_ids prepended. *)
  let impl_vars_rev = List.rev_map (fun id -> CPPvar id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun ((fix_id, fty), impl_id) (args, _body) ->
        let orig_params =
          List.map
            (fun (id, ty) ->
              (convert_ml_type_to_cpp_type env tvars ty, Some id))
            args
        in
        let fwd_args =
          List.map (fun (id, _) -> CPPvar id) args @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call = CPPfun_call (CPPvar impl_id, fwd_args) in
        let wrapper_body =
          match rty with
          | None -> [Sexpr call]
          | _ -> [Sreturn (Some call)]
        in
        Sasgn
          ( fix_id,
            Some Tauto,
            CPPlambda (orig_params, rty, wrapper_body, true) ))
      (List.combine renamed_ids impl_ids)
      funs_with_params
  in
  let deref_subst stmts = stmts in
  (impl_stmts @ wrapper_stmts, [], deref_subst)

(** Generate C++ statements from an ML AST. The continuation [k] transforms the
    final expression into a statement (e.g., return, assignment). Handles
    let-bindings, pattern matching, fix expressions, and monadic operations. *)
and gen_stmts env (k : cpp_expr -> cpp_stmt) ast =
  match ast with
  | MLletin (_, _, MLfix (x, ids, funs, _), b) as _whole ->
    (* Special case for let-fix: the let binding name is the fix function name *)
    (* Resolve unresolved metas in fix function types to Tvars using mgu. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    (* Collect all Tvar indices from the fixpoint types *)
    let fix_tvar_indices =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
    in
    let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    (* Check if fixpoint introduces Tvars beyond the outer scope *)
    let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function. Build tvar
         names for all Tvars used in the fixpoint type: - Tvars 1..n_outer reuse
         the outer function's template param names - Tvars beyond n_outer get
         fresh names T<i> *)
      let all_tvar_names = build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
      (* Generate the lifted function name *)
      let fix_name = fst ids.(x) in
      let outer_name =
        match tctx.current_outer_function_name with
        | Some n -> n
        | None -> "anon"
      in
      let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
      let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
      (* Save and set current_type_vars to the full tvar list for the lifted
         function *)
      let saved_tvars = get_current_type_vars () in
      set_current_type_vars all_tvar_names;
      (* Generate the fixpoint body using gen_fix, passing all mutual fixpoint
         names *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      (* Restore outer type vars *)
      set_current_type_vars saved_tvars;
      (* Build a lifted Dfundef for each fixpoint function (usually just one) *)
      let n_fix = Array.length funs in
      List.iteri
        (fun i ((renamed_id, fix_ty), params, body) ->
          let cpp_ty =
            convert_ml_type_to_cpp_type env all_tvar_names fix_ty
          in
          let _, cod =
            match cpp_ty with
            | Tfun (dom, cod) -> (dom, cod)
            | _ -> ([], cpp_ty)
          in
          (* Detect params that are not simply forwarded at recursive call
             sites — these must keep std::function type to avoid infinite
             recursive template instantiation. *)
          let non_fwd_source_indices =
            let lam_params, stripped_body =
              Mlutil.collect_lams funs.(i)
            in
            detect_non_forwarded_params_fix
              (List.length lam_params) n_fix i stripped_body
          in
          let cpp_params, all_temps_with_funs =
            build_lifted_cpp_params
              ~non_fwd_source_indices
              (convert_ml_type_to_cpp_type env all_tvar_names)
              all_temps
              params
          in
          (* Replace recursive self-references (CPPvar renamed_n) with calls to
             the lifted function *)
          let rec_call =
            mk_cppglob
              lifted_ref
              (List.map (fun id -> Tvar (0, Some id)) all_tvar_names)
          in
          let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
          let inner = Dfundef ([(lifted_ref, [])], cod, cpp_params, body, false) in
          let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
          add_lifted_decl lifted_decl )
        funs_compiled;
      (* In the continuation body b, the fixpoint name should resolve to a call
         to the lifted function with appropriate type arguments. We push the fix
         name into the env so that MLrel references in b resolve correctly. *)
      let projected_fix_id = (fst ids.(x), snd ids.(x)) in
      let _, env_with_fix = push_vars' [projected_fix_id] env in
      push_env_types [projected_fix_id];
      (* Generate b, then replace references to the fixpoint var with calls to
         the lifted function. Build explicit type args: outer tvars stay as Tvar
         references, extra tvars are resolved to concrete types from the
         enclosing function's return type. *)
      let call_type_args =
        let extra_tvar_names =
          List.filter
            (fun id -> not (List.exists (Id.equal id) outer_tvars))
            all_tvar_names
        in
        if extra_tvar_names = [] then
          List.map (fun id -> Tvar (0, Some id)) outer_tvars
        else
          let fix_ty = snd ids.(0) in
          let tmpl_cpp_ty =
            convert_ml_type_to_cpp_type env all_tvar_names fix_ty
          in
          let tmpl_cod =
            match tmpl_cpp_ty with
            | Tfun (_, cod) -> cod
            | t -> t
          in
          let outer_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
          let tvar_map =
            match tctx.current_cpp_return_type with
            | Some conc_ret -> extract_tvar_map tmpl_cod conc_ret
            | None -> []
          in
          let extra_args =
            List.map
              (fun tvar_name ->
                match List.find_opt
                        (fun (id, _) -> Id.equal id tvar_name)
                        tvar_map with
                | Some (_, ty) -> ty
                | None ->
                  match tctx.current_cpp_return_type with
                  | Some ret_ty -> ret_ty
                  | None -> Tvar (0, Some tvar_name) )
              extra_tvar_names
          in
          outer_args @ extra_args
      in
      let lifted_call = mk_cppglob lifted_ref call_type_args in
      (* Phase 2: shift owned vars for the single let binding *)
      let saved_owned_lifted = tctx.move_owned_vars in
      tctx.move_owned_vars <-
        Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
      let result = gen_stmts env_with_fix k b in
      tctx.move_owned_vars <- saved_owned_lifted;
      List.map (local_var_subst_stmt fix_name lifted_call) result )
    else
      (* No extra Tvars — proceed with local fixpoint approach.

         Three sub-steps:
         1. Compile all mutual fixpoint bodies via {!gen_fix}.
         2. Push only the PROJECTED fixpoint (the one this [MLletin]
            binds) into the continuation environment — not all mutual
            fix names, which would shift de Bruijn indices by [n]
            instead of the correct [1].
         3. Run escape analysis ({!fixpoint_escapes_in_stmts}) on the
            compiled continuation to decide between the [\[&\]] pattern
            ({!gen_local_fix_by_ref}) and the [shared_ptr] pattern
            ({!gen_local_fix_shared_ptr}).

         Move tracking: variables captured by the fixpoint bodies
         ({!Escape.free_rels}) are removed from [move_owned_vars] so
         that [dead_in_a] does not [std::move] them while the fixpoint's
         [\[&\]] lambda still holds references ([fix_move_capture]). *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body) -> (params, body)) funs_compiled
      in
      (* Add only the PROJECTED fixpoint id to the continuation env.
         MLletin binds ONE variable (the projected fixpoint), not all mutual
         fix functions.  Pushing all fix names would shift de Bruijn indices
         by n instead of 1, corrupting references in the continuation.
         However, ALL fix names are added to the avoid set to prevent
         name clashes in subsequent fixpoints (e.g., when the same mutual
         block is instantiated again with a different projection). *)
      let projected_id = List.nth renamed_ids x in
      (* Add non-projected fix names to the avoid set so that subsequent
         fixpoints (e.g., a second MLfix with a different projection from
         the same mutual block) will rename conflicting names. *)
      let env_for_cont =
        let (db, avoid) = env in
        let avoid' = List.fold_left
          (fun acc (i, (id, _)) ->
            if i <> x then Id.Set.add id acc else acc)
          avoid (List.mapi (fun i x -> (i, x)) renamed_ids)
        in
        (db, avoid')
      in
      let _, env_with_fix = push_vars' [projected_id] env_for_cont in
      push_env_types [projected_id];
      (* Compute outer variables captured by the fixpoint bodies.
         If the fixpoint ends up using [&] capture, these variables must
         not be moved in the continuation — the fixpoint holds references
         to them. Even if the fixpoint later uses [=] (escape path),
         suppressing moves is safe (just conservative: copies instead
         of moves for those vars). *)
      let fix_captured =
        Array.fold_left
          (fun acc body ->
            Escape.IntSet.union acc
              (Escape.free_rels (Array.length ids) body))
          Escape.IntSet.empty funs
      in
      (* Shift captured indices: free var at index i in the fix scope
         becomes i+1 in the continuation (one let-binding added). *)
      let captured_shifted =
        Escape.IntSet.map (fun i -> i + 1) fix_captured
      in
      (* Phase 2: shift owned vars and dead-after for the single let binding.
         Remove captured variables from owned set to prevent moves. *)
      let saved_owned = tctx.move_owned_vars in
      let saved_dead_fix = tctx.move_dead_after in
      tctx.move_owned_vars <-
        Escape.IntSet.diff
          (Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars)
          captured_shifted;
      tctx.move_dead_after <-
        Escape.IntSet.map (fun i -> i + 1) tctx.move_dead_after;
      let cont = gen_stmts env_with_fix k b in
      tctx.move_owned_vars <- saved_owned;
      tctx.move_dead_after <- saved_dead_fix;
      (* Check if any fixpoint variable escapes in the continuation.
         If so, use shared_ptr + [=] to prevent dangling references.
         Otherwise, use the simpler [&] capture pattern. *)
      let any_escapes =
        List.exists
          (fun (id, _) -> fixpoint_escapes_in_stmts id cont)
          renamed_ids
      in
      if any_escapes then
        let decls, defs, deref_subst =
          gen_local_fix_ycomb env renamed_ids funs_with_params
        in
        decls @ defs @ deref_subst cont
      else
        let owned_flags_per_fun =
          Array.to_list (Array.map (fun f ->
            let lam_ids, inner_body = Mlutil.collect_lams f in
            let n_params =
              List.length
                (List.filter
                   (fun (_, ty) -> not (ml_type_is_void ty))
                   lam_ids)
            in
            let n_fix = Array.length funs in
            let all_flags =
              Escape.infer_owned_params (n_params + n_fix) inner_body
            in
            List.init n_params (fun i -> List.nth all_flags i)
          ) funs)
        in
        let decls, defs =
          gen_local_fix_by_ref env renamed_ids funs_with_params
            owned_flags_per_fun
        in
        decls @ defs @ cont
  | MLletin (x, t, (MLlam _ as a), b) ->
    (* Check if this is a polymorphic lambda that should be lifted to a
       top-level template function. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    resolve_metas t;
    resolve_metas_in_ast resolve_metas a;
    (* Collect all Tvar indices from the let-binding type *)
    let tvar_indices = collect_tvars [] t in
    (* Also collect Tvars from the lambda body *)
    let body_tvars = collect_tvars_ast [] a in
    let all_body_tvars = List.sort_uniq Int.compare body_tvars in
    let tvar_indices = List.sort Int.compare tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    let has_extra = List.exists (fun i -> i > n_outer) tvar_indices in
    (* Normal MLletin fallback (shared by no-extra-tvars and
       thunk-with-free-vars cases) *)
    let gen_normal_letin () =
      (* Eta-expand a let-bound lambda whose body returns a function value.
         [convert_ml_type_to_cpp_type] maximally uncurries the binding type,
         so a binding of type [unit -> State bool unit] (= [unit -> (bool ->
         pair)]) becomes [std::function<pair(monostate, bool)>] (2 params) and
         the call site emits a 2-arg call.  But if the RHS is [fun u =>
         state_bind ...] — a 1-binder lambda whose body is itself a [State]
         (a unary function) rather than a nested lambda — the emitted lambda
         only takes 1 arg, so it is not convertible to the 2-param type.  Add
         the missing binders (with types drawn from the arrow structure of [t])
         and apply the body to them, so value, type, and call site all agree on
         arity.  Gated on [n_want > n_have] so fully eta-expanded lambdas (the
         common case) are unchanged. *)
      let a =
        match a with
        | MLlam _ ->
          let n_want = count_ml_value_arrows t in
          let binders, body = collect_lams a in
          let n_have =
            List.length
              (List.filter (fun (_, ty) -> not (Mlutil.isTdummy ty)) binders)
          in
          if n_want <= n_have then
            a
          else
            let rec value_arrow_domains = function
              | Miniml.Tarr (t1, t2) when not (Mlutil.isTdummy t1) ->
                t1 :: value_arrow_domains t2
              | Miniml.Tarr (_, t2) -> value_arrow_domains t2
              | Miniml.Tmeta {contents = Some t} -> value_arrow_domains t
              | _ -> []
            in
            (* Domains of the value-arrows not yet abstracted by the lambda,
               in binding order (outermost first). *)
            let new_doms =
              List.filteri (fun i _ -> i >= n_have) (value_arrow_domains t)
            in
            let d = List.length new_doms in
            if d = 0 then
              a
            else
              (* Use the anonymous binder name so these synthesized params are
                 rendered like every other anonymous lambda parameter (the
                 renamer uniquifies them to [_x0], [_x1], ...) instead of a
                 bespoke [_eta] scheme. *)
              let new_binders =
                List.map (fun dom -> (Id anonymous_name, dom)) new_doms
              in
              (* Args applied to the (lifted) body: the innermost new binder is
                 [MLrel 1], the outermost is [MLrel d]. *)
              let args = List.init d (fun i -> MLrel (d - i)) in
              let lifted_body = ast_lift d body in
              let applied =
                match lifted_body with
                | MLapp (f, xs) -> MLapp (f, xs @ args)
                | _ -> MLapp (lifted_body, args)
              in
              let inner = named_lams (List.rev new_binders) applied in
              named_lams binders inner
        | _ -> a
      in
      let x' = remove_prime_id (id_of_mlid x) in
      let renamed_ids, env' = push_vars' [(x', t)] env in
      let x_renamed = fst (List.hd renamed_ids) in
      if x == Dummy then (
        push_env_types [(x_renamed, t)];
        gen_stmts env' k b )
      else if tctx.itree_mode = Reified && is_monadic_ml_type t then begin
        (* Monadic let-binding (reified mode): wrap RHS in an ITree IIFE so
           the variable has type [shared_ptr<ITree<R>>]. *)
        Table.require_itree_header ();
        push_env_types [(x_renamed, t)];
        let tvars = get_current_type_vars () in
        let r_ml = extract_itree_result_ml t in
        let r_cpp = convert_ml_type_to_cpp_type env tvars r_ml in
        (* Voidify unit result type in ITree wrapper *)
        let r_cpp = if ml_type_is_unit r_ml then Tvoid else r_cpp in
        let reified_ty = mk_itree_type r_cpp in
        let ret_k v = Sreturn (Some (mk_itree_ret_for_value r_cpp r_ml v)) in
        let body_stmts = gen_stmts env ret_k a in
        let iife = CPPfun_call (
          CPPlambda ([], Some reified_ty, body_stmts, false), []) in
        (* Shift owned vars and dead-after for the continuation *)
        let saved_owned_lam = tctx.move_owned_vars in
        let saved_dead_lam = tctx.move_dead_after in
        tctx.move_owned_vars <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
        tctx.move_dead_after <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_dead_after;
        let cont = gen_stmts env' k b in
        tctx.move_owned_vars <- saved_owned_lam;
        tctx.move_dead_after <- saved_dead_lam;
        (* Generate the assignment with reified type *)
        [Sasgn (x_renamed, Some reified_ty, iife)] @ cont
      end else
        let afun v = Sasgn (x_renamed, None, v) in
        tctx.last_pair_accessor_any_cast <- false;
        let asgn = gen_stmts env afun a in
        (* When the RHS was a pair accessor on an erased argument (e.g.
           snd vs where vs : std::any), the result is std::any at runtime
           even though the ML type says prod(...).  Override to Tdummy so
           downstream pair accessor calls (fst tail) detect erasure. *)
        let t_for_env =
          if tctx.last_pair_accessor_any_cast then Miniml.Tdummy Ktype else t
        in
        tctx.last_pair_accessor_any_cast <- false;
        (* Push env_types AFTER generating the value expression [a]. *)
        push_env_types [(x_renamed, t_for_env)];
        let tvars = get_current_type_vars () in
        (* Phase 2: shift owned vars and dead-after for lambda let binding.
           The body [b] has one more de Bruijn binder, so all indices must
           be shifted +1. *)
        let saved_owned_lam = tctx.move_owned_vars in
        let saved_dead_lam = tctx.move_dead_after in
        tctx.move_owned_vars <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
        tctx.move_dead_after <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_dead_after;
        let gen_cont () =
          let cont = gen_stmts env' k b in
          tctx.move_owned_vars <- saved_owned_lam;
          tctx.move_dead_after <- saved_dead_lam;
          cont
        in
        match asgn with
        | [Sasgn (_, None, e)] ->
          Sasgn
            ( x_renamed,
              Some (convert_ml_type_to_cpp_type env tvars t),
              e )
          :: gen_cont ()
        | _ ->
          Sdecl
            (x_renamed, convert_ml_type_to_cpp_type env tvars t)
          :: asgn
          @ gen_cont ()
    in
    if not has_extra then
      gen_normal_letin ()
    else (* Lift the polymorphic lambda to a top-level template function. *)
      let params, body = collect_lams a in
      let n_params = List.length params in
      let x' = remove_prime_id (id_of_mlid x) in

      (* 1. Collect free variables in the lambda body *)
      let free_indices = collect_free_rels n_params body in
      let free_vars =
        List.map
          (fun i ->
            let name = get_db_name i env in
            let ty = get_env_type i in
            (name, ty, i) )
          (List.sort Int.compare free_indices)
      in

      (* Check if all parameters are dummy/void - if so, this is likely a thunk
         for monadic ops *)
      let all_params_dummy =
        List.for_all (fun (_, ty) -> isTdummy ty || ml_type_is_void ty) params
      in

      if all_params_dummy then
        (* All lambda params are erased type params — this is a polymorphic
           function alias like `let alias := @id`. Don't lift to a top-level
           template; instead inline the lambda into the continuation and
           beta-reduce, so that call sites like `alias nat 9` become direct
           calls like `id(9)`. *)
        let b' = ast_subst a b in
        let rec beta_red_app args = function
          | MLlam (_, _, body) ->
            ( match args with
            | [] -> MLlam (Dummy, Tdummy Ktype, beta_normalize body)
            | _ :: rest -> beta_red_app rest (ast_pop body) )
          | f ->
            let f = beta_normalize f in
            if args = [] then
              f
            else
              MLapp (f, List.map beta_normalize args)
        and beta_normalize = function
          | MLapp ((MLlam _ as f), args) -> beta_red_app args f
          | t -> ast_map beta_normalize t
        in
        let b' = beta_normalize b' in
        gen_stmts env k b'
      else
        (* 2. Build tvar names: outer tvars keep their names, extra tvars get
           fresh names *)
        let all_tvar_names = build_tvar_names ~outer_tvars tvar_indices in
        let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in

        let extended_tvar_names =
          build_extended_tvar_names tvar_indices all_tvar_names all_body_tvars
        in

        (* 3. Generate the lifted function name *)
        let outer_name =
          match tctx.current_outer_function_name with
          | Some n -> n
          | None -> "anon"
        in
        let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string x' in
        let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in

        (* 4. Substitution helper for call sites: replace CPPfun_call(CPPvar x',
           args) with CPPfun_call(CPPglob(lifted_ref, []), free_var_cpps @
           args) *)
        let rec subst_lifted_call_expr
            (target : Id.t)
            (lifted : GlobRef.t)
            (free_args : cpp_expr list)
            (e : cpp_expr) =
          let sub = subst_lifted_call_expr target lifted free_args in
          match e with
          | CPPfun_call (CPPvar id, args) when Id.equal id target ->
            CPPfun_call (mk_cppglob lifted [], free_args @ List.map sub args)
          | CPPvar id when Id.equal id target ->
            (* Bare reference to lifted function: generate a properly-typed
               wrapper lambda with one parameter per non-erased Rocq lambda
               param. Capture by value ([=]) so that free variables don't
               dangle when the wrapper outlives the current stack frame. *)
            let n_actual_params =
              List.length
                (List.filter
                   (fun (_, ty) ->
                     (not (isTdummy ty)) && not (ml_type_is_void ty))
                   params)
            in
            if free_args = [] && n_actual_params = 0 then
              mk_cppglob lifted []
            else
              let fresh_ids =
                List.init n_actual_params (fun i ->
                  Id.of_string (Printf.sprintf "_xarg%d" i))
              in
              let wrapper_params =
                List.map (fun id -> (Tauto, Some id)) fresh_ids
              in
              let wrapper_call_args =
                free_args @ List.map (fun id -> CPPvar id) fresh_ids
              in
              CPPlambda
                ( wrapper_params,
                  None,
                  [
                    Sreturn
                      (Some
                         (CPPfun_call
                            (mk_cppglob lifted [], wrapper_call_args)));
                  ],
                  true )
          | CPPfun_call (f, args) -> CPPfun_call (sub f, List.map sub args)
          | CPPderef e' -> CPPderef (sub e')
          | CPPmove e' -> CPPmove (sub e')
          | CPPlambda (args, ty, b, cbv) ->
            CPPlambda
              ( args,
                ty,
                List.map (subst_lifted_call_stmt target lifted free_args) b,
                cbv )
          | CPPoverloaded cases -> CPPoverloaded (List.map sub cases)
          | CPPstructmk (id', tys, args) ->
            CPPstructmk (id', tys, List.map sub args)
          | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map sub args)
          | CPPget (e', id') -> CPPget (sub e', id')
          | CPPget' (e', id') -> CPPget' (sub e', id')
          | CPPnamespace (id', e') -> CPPnamespace (id', sub e')
          | CPPparray (args, e') -> CPPparray (Array.map sub args, sub e')
          | CPPmethod_call (obj, meth, args) ->
            CPPmethod_call (sub obj, meth, List.map sub args)
          | CPPmember (e', mid) -> CPPmember (sub e', mid)
          | CPParrow (e', mid) -> CPParrow (sub e', mid)
          | CPPforward (ty, e') -> CPPforward (ty, sub e')
          | CPPnew (ty, args) -> CPPnew (ty, List.map sub args)
          | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ty, sub e')
          | CPPstruct_id (sid, tys, args) ->
            CPPstruct_id (sid, tys, List.map sub args)
          | CPPqualified (e', qid) -> CPPqualified (sub e', qid)
          | CPPany_cast (_, CPPfun_call (CPPvar id, args)) when Id.equal id target ->
            (* The any_cast wraps a direct call to the variable being lifted.
               The lifted template function returns a concrete type (not
               std::any), so drop the cast and replace with the lifted call. *)
            CPPfun_call (mk_cppglob lifted [], free_args @ List.map sub args)
          | CPPany_cast (ty, e') -> CPPany_cast (ty, sub e')
          | _ -> e
        and subst_lifted_call_stmt
            (target : Id.t)
            (lifted : GlobRef.t)
            (free_args : cpp_expr list)
            (s : cpp_stmt) =
          match s with
          | Sreturn (Some e) ->
            Sreturn (Some (subst_lifted_call_expr target lifted free_args e))
          | Sreturn None -> Sreturn None
          | Sasgn (id, ty, e) ->
            Sasgn (id, ty, subst_lifted_call_expr target lifted free_args e)
          | Sexpr e -> Sexpr (subst_lifted_call_expr target lifted free_args e)
          | Scustom_case (ty, e, tys, brs, str) ->
            Scustom_case
              ( ty,
                subst_lifted_call_expr target lifted free_args e,
                tys,
                List.map
                  (fun (args, ty, stmts) ->
                    ( args,
                      ty,
                      List.map
                        (subst_lifted_call_stmt target lifted free_args)
                        stmts ) )
                  brs,
                str )
          | _ -> s
        in

        (* 6. Compile the lambda body with extended type variables *)
        let saved_tvars = get_current_type_vars () in
        set_current_type_vars extended_tvar_names;
        (* Push lambda params into env for body compilation *)
        let param_ids =
          List.map
            (fun (ml_id, ty) -> (remove_prime_id (id_of_mlid ml_id), ty))
            params
        in
        (* For free variables, we need to adjust de Bruijn indices in the body.
           The body references free vars as MLrel (n_params + i) where i is the
           outer index. We compile with an env that has: [free_var_params...;
           lambda_params...] So we push free var names first, then lambda param
           names. *)
        let free_var_params =
          List.map (fun (name, ty, _) -> (name, ty)) free_vars
        in
        let body_params_for_env = free_var_params @ param_ids in
        let body_param_ids, body_env = push_vars' body_params_for_env env in
        let saved_env_types = tctx.env_types in
        push_env_types body_param_ids;

        (* Now compile the body. The body's de Bruijn indices: MLrel 1..n_params
           -> lambda params (at positions n_free+1..n_free+n_params in our env)
           MLrel n_params+i -> free var i (should map to position n_free-i+1 in
           our env, but we actually need to adjust: MLrel (n_params +
           orig_outer_idx) in the body maps to outer env position
           orig_outer_idx. In our extended env, free vars are at positions
           n_params+1..n_params+n_free. So we need to remap. Actually, the body
           already has correct de Bruijn indices: - MLrel 1..n_params are the
           lambda params - MLrel (n_params + i) references outer scope position
           i When we push [free_var_params @ param_ids], the env has: positions
           1..n_params = param_ids (lambda params) positions
           n_params+1..n_params+n_free = free_var_params But the body references
           MLrel(n_params + original_outer_idx), and original_outer_idx may not
           equal the position in free_var_params. We need the body env to map
           MLrel(n_params + i) correctly for each free var. *)

        (* Simpler approach: compile body in a modified env where free vars at
           their original positions are accessible. We push only the lambda
           params on top of the outer env. *)
        let lam_param_ids, lam_env = push_vars' param_ids env in
        tctx.env_types <- saved_env_types;
        push_env_types lam_param_ids;
        (* Lambda bodies have their own return type; clear the enclosing
           function's void flag to avoid bare 'return;' inside the lambda. *)
        let saved_return_type = tctx.current_cpp_return_type in
        ( if tctx.current_cpp_return_type = Some Tvoid then
            tctx.current_cpp_return_type <- None );
        let compiled_body =
          gen_stmts lam_env (fun x -> Sreturn (Some x)) body
        in
        tctx.current_cpp_return_type <- saved_return_type;
        tctx.env_types <- saved_env_types;
        set_current_type_vars saved_tvars;

        (* 7. Now substitute free variable references in compiled body: Free
           vars in the body were compiled as CPPvar(name_from_outer_env). In the
           lifted function, they become parameters. The names are the same, so
           no substitution of the body is needed — the free var params have the
           same names as the outer scope variables. *)

        (* 8. Build the lifted function parameters: free vars first, then lambda
           params *)
        let all_lifted_params =
          free_var_params
          @ List.filter
              (fun (_, ty) -> (not (ml_type_is_void ty)) && not (isTdummy ty))
              lam_param_ids
        in
        let cpp_params, all_temps_with_funs =
          build_lifted_cpp_params
            (convert_ml_type_to_cpp_type
               lam_env
               extended_tvar_names )
            all_temps
            all_lifted_params
        in

        (* Get return type from the let-binding type *)
        let cpp_ty =
          convert_ml_type_to_cpp_type
            lam_env
            extended_tvar_names
            t
        in
        let cod =
          match cpp_ty with
          | Tfun (_, cod) -> cod
          | _ -> cpp_ty
        in

        (* 9. Build and register the lifted declaration *)
        let inner =
          Dfundef ([(lifted_ref, [])], cod, cpp_params, compiled_body, false)
        in
        let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
        add_lifted_decl lifted_decl;

        (* 10. Compile the continuation body b, substituting calls to x' with
           calls to the lifted function *)
        let lifted_ids, env' = push_vars' [(x', t)] env in
        let x_lifted = fst (List.hd lifted_ids) in
        push_env_types [(x_lifted, t)];
        (* Phase 2: shift owned vars for lifted lambda binding *)
        let saved_owned_lifted2 = tctx.move_owned_vars in
        tctx.move_owned_vars <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
        let cont = gen_stmts env' k b in
        tctx.move_owned_vars <- saved_owned_lifted2;
        (* Build the free variable argument expressions *)
        let free_var_cpps =
          List.map (fun (name, _, _) -> CPPvar name) free_vars
        in
        List.map
          (subst_lifted_call_stmt x_lifted lifted_ref free_var_cpps)
          cont
  | MLletin (x, t, a, b) ->
    let x' = remove_prime_id (id_of_mlid x) in
    let ids_renamed, env' = push_vars' [(x', t)] env in
    let x_renamed = fst (List.hd ids_renamed) in
    if x == Dummy then (
      push_env_types [(x_renamed, t)];
      with_shifted_move_tracking 1 (fun () ->
        gen_stmts env' k b) )
    else if ml_type_is_unit t then (
      (* Unit-typed let bindings: the RHS may call a void-ified function,
         so we can't assign its result to a variable.  Execute the RHS for
         side effects, then declare the variable as Unit::e_TT (its only
         possible value) so the body can still reference it. *)
      push_env_types [(x_renamed, t)];
      let rhs = gen_stmts env (fun e -> Sexpr e) a in
      (* Drop trivially pure RHS (e.g. Unit::e_TT from tt, variable refs) *)
      let rhs = List.filter (fun s ->
        match s with
        | Sexpr (CPPenum_val _) -> false
        | Sexpr (CPPvar _) -> false
        | _ -> true) rhs in
      (* Generate the body first (under shifted move tracking for the new
         binder), then check if the variable is actually referenced in the
         generated C++ (not just the ML AST, since optimizations like
         unit-match elimination may drop references). *)
      let body =
        with_shifted_move_tracking 1 (fun () -> gen_stmts env' k b)
      in
      let decl =
        if stmts_reference_var x_renamed body then
          let tvars = get_current_type_vars () in
          let cpp_ty = convert_ml_type_to_cpp_type env tvars t in
          [Sasgn (x_renamed, Some cpp_ty, mk_tt_expr ())]
        else []
      in
      rhs @ decl @ body )
    else
      let depth = tctx.current_letin_depth in
      tctx.current_letin_depth <- depth + 1;
      (* Phase 2: set up dead-after info for move insertion. Compute free vars
         of the continuation [b] (shifted by 1 because [b] is under the let
         binder). A variable at de Bruijn index [i] in [a] is dead-after if
         [i+1] is not free in [b] (since [b] has one extra binder). Only move if
         the variable has exactly 1 occurrence in [a]. *)
      let saved_dead = tctx.move_dead_after in
      let saved_owned = tctx.move_owned_vars in
      let cont_free = Escape.free_rels 1 b in
      (* free in b, shifted past let binder *)
      let dead_in_a =
        Escape.IntSet.filter
          (fun i ->
            (* i is dead after [a] if i is not free in [b] AND occurs exactly
               once in [a] *)
            (not (Escape.IntSet.mem i cont_free))
            && Escape.nb_occur_match i a = 1 )
          tctx.move_owned_vars
      in
      (* Also add any vars from our current dead set that have single occurrence
         in a *)
      let dead_from_above =
        Escape.IntSet.filter
          (fun i ->
            Escape.IntSet.mem i tctx.move_dead_after
            && Escape.nb_occur_match i a = 1 )
          tctx.move_owned_vars
      in
      tctx.move_dead_after <- Escape.IntSet.union dead_in_a dead_from_above;
      let saved_suppress = tctx.move_suppress_tail in
      tctx.move_suppress_tail <- true;
      (* Single-use partial application optimization: when the RHS is a partial
         application and the bound variable is used at most once in the
         continuation without escaping, AND all free variables of the RHS are
         dead in the continuation (so [&] capture references stay valid),
         tell eta_fun to keep CPPmove wrappers and use [&] capture for
         zero-copy closure generation. *)
      let is_single_use_partial_app =
        match a with
        | MLapp (head, ml_args) | MLmagic (MLapp (head, ml_args)) ->
          (match Escape.partial_app_remaining head ml_args with
           | Some remaining ->
             Escape.nb_occur_match 1 b <= 1
             && not (Escape.escapes 1 b)
             && Escape.IntSet.is_empty
                  (Escape.IntSet.inter (Escape.free_rels 0 a) cont_free)
             && Escape.single_use_nargs 1 b >= remaining
           | None -> false)
        | _ -> false
      in
      let saved_eta_keep = tctx.eta_keep_moves in
      if is_single_use_partial_app then tctx.eta_keep_moves <- true;
      let afun v = Sasgn (x_renamed, None, v) in
      (* Thread the let-binding's type annotation as expected_ml_type_for_arg
         so that gen_ctor_call can recover the concrete element type for
         constructors (like nil) whose ML annotation has unresolved metas or
         erased type args.  For example: let sk = [] : list parser_frame — the
         let-binding knows the element type even when the nil's own annotation
         has Tdummy Ktype. *)
      let saved_expected_letin = tctx.expected_ml_type_for_arg in
      (* Look ahead: if t has erased type args, look at the body b to see if the
         bound var (MLrel 1 in b) is used as the i-th arg of a constructor call
         with a non-erased corresponding type arg. If so, use that type instead of t.
         This recovers the correct element type for nils bound before pair constructors:
           let empty_stack : list(Tmeta) = [] in make_pair(fr, empty_stack)
         where the pair type says the second arg is list(parser_frame). *)
      let t_effective =
        let t_has_erased = ml_type_contains_erased t in
        if not t_has_erased then t
        else begin
          (* Try to infer from an MLcons that immediately follows in the body.
             The body b may be directly an MLcons, or wrapped in one more MLletin. *)
          let try_cons_body (b_inner : Miniml.ml_ast) db_offset =
            (* db_offset: how many let-bindings above b_inner, so MLrel (1+db_offset) = x *)
            let target_rel = 1 + db_offset in
            (* Resolve t to get the underlying inductive (through metas) *)
            let t_ind_opt = match resolve_tmeta t with
              | Miniml.Tglob (t_ind, _, _) -> Some t_ind
              | _ -> None
            in
            match b_inner with
            | Miniml.MLcons (ctor_ty, _, ts) ->
              let result = ref None in
              List.iteri (fun i (ti : Miniml.ml_ast) ->
                match ti with
                | Miniml.MLrel r when r = target_rel ->
                  (match resolve_tmeta ctor_ty with
                   | Miniml.Tglob (_, ctor_tys, _) ->
                     (match List.nth_opt ctor_tys i with
                      | Some raw_candidate ->
                        (match resolve_tmeta raw_candidate with
                        | Miniml.Tglob (ind, sub_tys, _) as candidate ->
                          (* Check that candidate's inductive matches t's inductive.
                             When t is fully erased (Tmeta{None}), accept any concrete type. *)
                          let matches_t = match t_ind_opt with
                            | Some t_ind -> GlobRef.CanOrd.equal ind t_ind
                            | None -> true
                          in
                          if matches_t && not (List.exists is_erased_ml_type sub_tys) then
                            result := Some candidate
                        | _ -> ())
                      | _ -> ())
                   | _ -> ())
                | _ -> ()
              ) ts;
              !result
            | _ -> None
          in
          (* Try to infer t from an MLapp body: find the position of target_rel
             in the application args, look up the function's ML type, and extract
             the type of that arg.  This handles the pattern:
               let sk0 : Tmeta = (fr, nil) in multistep(..., sk0, ...)
             where multistep's type tells us sk0 has type parser_frame × list(parser_frame). *)
          let try_app_body (b_inner : Miniml.ml_ast) db_offset =
            let target_rel = 1 + db_offset in
            match b_inner with
            | Miniml.MLapp (Miniml.MLglob (func_ref, _), app_args)
            | Miniml.MLapp (Miniml.MLmagic (Miniml.MLglob (func_ref, _)), app_args) ->
              let rec find_pos args i =
                match args with
                | [] -> None
                | (Miniml.MLrel r) :: _ when r = target_rel -> Some i
                | (Miniml.MLmagic (Miniml.MLrel r)) :: _ when r = target_rel -> Some i
                | _ :: rest -> find_pos rest (i + 1)
              in
              (match find_pos app_args 0 with
              | None -> None
              | Some idx ->
                (match find_type_opt func_ref with
                | None -> None
                | Some func_ty ->
                  let rec nth_arg ty n =
                    match ty with
                    | Miniml.Tarr (Miniml.Tdummy _, cod) -> nth_arg cod n
                    | Miniml.Tarr (dom, _) when n = 0 -> Some dom
                    | Miniml.Tarr (_, cod) -> nth_arg cod (n - 1)
                    | Miniml.Tmeta {contents = Some t2} -> nth_arg t2 n
                    | _ -> None
                  in
                  let try_unfold_typedef resolved =
                    match resolved with
                    | Miniml.Tglob (GlobRef.ConstRef kn, _, _) ->
                      (match Table.lookup_typedef_unchecked kn with
                       | Some expanded -> expanded
                       | None -> resolved)
                    | _ -> resolved
                  in
                  (match nth_arg func_ty idx with
                  | Some arg_ty ->
                    let resolved = resolve_tmeta arg_ty in
                    let resolved = try_unfold_typedef resolved in
                    (match resolve_tmeta t, resolved with
                    | _, Miniml.Tglob (_, r_sub, _)
                      when not (List.exists is_erased_ml_type r_sub) ->
                      Some resolved
                    | _ -> None)
                  | None -> None)))
            | _ -> None
          in
          let inferred = match (b : Miniml.ml_ast) with
            | Miniml.MLcons _ -> try_cons_body b 0
            | Miniml.MLletin (_, _, a', _) ->
              (* In body = MLletin(sk0, pair_expr, ...), nil is at MLrel 1 in pair_expr.
                 db_offset=0 because pair_expr is evaluated before sk0 is bound. *)
              (match try_cons_body a' 0 with
               | Some _ as r -> r
               | None -> try_cons_body b 0)
            | Miniml.MLapp _ ->
              (* Body is a function application — look up the function type to find
                 the type expected for the bound variable at its argument position. *)
              try_app_body b 0
            | _ -> None
          in
          match inferred with Some ty -> ty | None -> t
        end
      in
      tctx.expected_ml_type_for_arg <- Some t_effective;
      tctx.last_pair_accessor_any_cast <- false;
      let asgn = gen_stmts env afun a in
      tctx.expected_ml_type_for_arg <- saved_expected_letin;
      tctx.eta_keep_moves <- saved_eta_keep;
      (* Push env_types AFTER generating the value expression [a] — [a] uses de
         Bruijn indices that don't include the new let binding.  The body [b]
         (generated below) does include it. *)
      let t_for_env =
        if tctx.last_pair_accessor_any_cast then Miniml.Tdummy Ktype else t
      in
      tctx.last_pair_accessor_any_cast <- false;
      push_env_types [(x_renamed, t_for_env)];
      tctx.move_suppress_tail <- saved_suppress;
      (* Shift saved_dead +1 for the body [b]: the new let binding adds one
         de Bruijn level, so all parent-scope indices must be shifted to stay
         in sync with the body's coordinate system. *)
      tctx.move_dead_after <- Escape.IntSet.map (fun i -> i + 1) saved_dead;
      (* The new let binding is owned (it's a local variable). Update
         move_owned_vars for processing [b]: shift all existing indices by 1
         (because [b] has one more binder) and add index 1 if the type is
         shared_ptr. *)
      let shifted_owned =
        Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars
      in
      (* Const-ref binding optimisation: when the RHS [a] is a record-field
         access (single-branch MLcase) on a source variable that is NOT being
         moved at this point, we can bind the result as [const T&] instead of
         [T].  This avoids an unnecessary shared_ptr refcount increment at the
         binding site; any subsequent owned uses still copy from the reference.

         A variable k is moved only when it is in BOTH [move_owned_vars] (owned
         value semantics) AND [move_dead_after] (last use at this point).  When
         the source has further uses in the let body it will not be moved, so
         the const-ref remains valid.  We only apply this when the type is a
         shared_ptr so that primitive types (int, bool) are left unchanged. *)
      let use_const_ref =
        Escape.is_shared_ptr_type t
        &&
        ( match a with
          | MLcase (_, MLrel k, pv)
            when Array.length pv = 1
                 && (match pv.(0) with (_, _, _, MLrel _) -> true | _ -> false)
                 && not (Escape.IntSet.mem k tctx.move_owned_vars
                         && Escape.IntSet.mem k tctx.move_dead_after) ->
            true
          | _ -> false )
      in
      let new_is_tracked =
        (Escape.is_shared_ptr_type t || is_nontrivial_value_ml_type t)
        && not use_const_ref
      in
      let owned_for_b =
        if new_is_tracked then
          Escape.IntSet.add 1 shifted_owned
        else
          shifted_owned
      in
      tctx.move_owned_vars <- owned_for_b;
      let tvars = get_current_type_vars () in
      let result =
        match asgn with
          | [Sasgn (_, None, e)] ->
            let cpp_ty = convert_ml_type_to_cpp_type env tvars t in
            (* When the type contains Tany (from erased carrier projections) but
               the generated expression is a lambda with concrete types, derive
               the std::function type from the lambda's parameter and return
               types. *)
            let cpp_ty =
              match (cpp_ty, e) with
              | Tfun (dom, _), CPPlambda (params, Some ret_ty, _, _)
                when List.exists has_tany_in_type dom ->
                let strip_tmod = function
                  | Tmod (_, t) -> t
                  | t -> t
                in
                let param_tys =
                  List.rev_map (fun (ty, _) -> strip_tmod ty) params
                in
                Tfun (param_tys, ret_ty)
              | _, CPPlambda _ -> cpp_ty
              | _, _ when has_erased_type_in_type cpp_ty ->
                (* Type contains erased positions (Tany or dummy_type marker)
                   but the expression is not a lambda with inferable types.
                   Use [auto] so the C++ compiler deduces the concrete type
                   from the RHS — e.g. for pair-projection bindings like
                   [const auto &prs = tup.first] where the erased type would
                   be [List<pair<String, any>>] but the actual type of
                   [tup.first] is [List<pair<String, JV>>], or for existT nil
                   constructors where the element type is dummy_type. *)
                Tauto
              | _ -> cpp_ty
            in
            (* Apply const-ref binding when safe. *)
            let cpp_ty =
              if use_const_ref then Tref (Tmod (TMconst, cpp_ty))
              else cpp_ty
            in
            begin match extract_block_template e with
            | Some (ref, tmpl, args, tys) ->
              Sblock_custom (ref, tmpl, x_renamed, cpp_ty, args, tys)
              :: gen_stmts env' k b
            | None ->
              Sasgn (x_renamed, Some cpp_ty, e) :: gen_stmts env' k b
            end
          | _ ->
            let cpp_ty = convert_ml_type_to_cpp_type env tvars t in
            (Sdecl (x_renamed, cpp_ty) :: asgn) @ gen_stmts env' k b
      in
      tctx.move_owned_vars <- saved_owned;
      result
  | MLapp (MLfix (x, ids, funs, _), args) ->
    (* Resolve unresolved metas in fix function types to Tvars using mgu.
       Traverse types and assign Tvar 1, 2, ... to each unresolved meta. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    Array.iter (resolve_metas_in_ast resolve_metas) funs;
    List.iter (resolve_metas_in_ast resolve_metas) args;
    (* Collect Tvars from bodies too *)
    let body_tvars = Array.fold_left collect_tvars_ast [] funs in
    let all_body_tvars = List.sort_uniq Int.compare body_tvars in
    (* Collect all Tvar indices from the fixpoint types *)
    let fix_tvar_indices =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
    in
    let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    (* Check if fixpoint introduces Tvars beyond the outer scope *)
    let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function *)
      let all_tvar_names = build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
      let extended_tvar_names =
        build_extended_tvar_names fix_tvar_indices all_tvar_names all_body_tvars
      in
      let fix_name = fst ids.(x) in
      let outer_name =
        match tctx.current_outer_function_name with
        | Some n -> n
        | None -> "anon"
      in
      let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
      let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
      (* Save and set current_type_vars to the extended tvar list for the lifted
         function. extended_tvar_names covers both signature and body Tvar
         indices. *)
      let saved_tvars = get_current_type_vars () in
      set_current_type_vars extended_tvar_names;
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      set_current_type_vars saved_tvars;
      (* Build lifted declarations *)
      let n_fix = Array.length funs in
      List.iteri
        (fun i ((renamed_id, fix_ty), params, body) ->
          let cpp_ty =
            convert_ml_type_to_cpp_type
              env
              extended_tvar_names
              fix_ty
          in
          let _, cod =
            match cpp_ty with
            | Tfun (dom, cod) -> (dom, cod)
            | _ -> ([], cpp_ty)
          in
          let non_fwd_source_indices =
            let lam_params, stripped_body =
              Mlutil.collect_lams funs.(i)
            in
            detect_non_forwarded_params_fix
              (List.length lam_params) n_fix i stripped_body
          in
          let cpp_params, all_temps_with_funs =
            build_lifted_cpp_params
              ~non_fwd_source_indices
              (convert_ml_type_to_cpp_type
                 env
                 extended_tvar_names )
              all_temps
              params
          in
          let rec_call =
            mk_cppglob
              lifted_ref
              (List.map (fun id -> Tvar (0, Some id)) all_tvar_names)
          in
          let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
          let inner = Dfundef ([(lifted_ref, [])], cod, cpp_params, body, false) in
          let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
          add_lifted_decl lifted_decl )
        funs_compiled;
      (* Generate args in outer scope and call the lifted function. Build
         explicit type args: outer tvars stay as Tvar references, extra tvars
         are resolved to concrete types from the enclosing context. Extra tvars
         that appear as the fixpoint's return type are resolved to the enclosing
         function's C++ return type (current_cpp_return_type). *)
      let call_type_args =
        let extra_tvar_names =
          List.filter
            (fun id -> not (List.exists (Id.equal id) outer_tvars))
            all_tvar_names
        in
        if extra_tvar_names = [] then
          (* All tvars are outer — C++ can deduce them *)
          []
        else
          (* Get the fixpoint's template return type to identify which extra
             tvar it uses *)
          let fix_ty = snd ids.(x) in
          let tmpl_cpp_ty =
            convert_ml_type_to_cpp_type
              env
              extended_tvar_names
              fix_ty
          in
          let tmpl_cod =
            match tmpl_cpp_ty with
            | Tfun (_, cod) -> cod
            | t -> t
          in
          let outer_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
          let tvar_map =
            match tctx.current_cpp_return_type with
            | Some conc_ret -> extract_tvar_map tmpl_cod conc_ret
            | None -> []
          in
          let extra_args =
            List.map
              (fun tvar_name ->
                match List.find_opt
                        (fun (id, _) -> Id.equal id tvar_name)
                        tvar_map with
                | Some (_, ty) -> ty
                | None ->
                  match tctx.current_cpp_return_type with
                  | Some ret_ty -> ret_ty
                  | None -> Tvar (0, Some tvar_name) )
              extra_tvar_names
          in
          outer_args @ extra_args
      in
      let cpp_args = List.rev_map (gen_expr env) args in
      [k (CPPfun_call (mk_cppglob lifted_ref call_type_args, cpp_args))] )
    else (* No extra Tvars - proceed with by-ref local fixpoint (immediately applied) *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body) -> (params, body)) funs_compiled
      in
      let args = List.rev_map (gen_expr env) args in
      let _, fix_params, _ = List.nth funs_compiled x in
      let n_provided = List.length args in
      let n_fix_params = List.length fix_params in
      if n_provided < n_fix_params then begin
        (* Partial application: the fixpoint escapes (returned as a lambda).
           Use Y-combinator pattern so the fixpoint body doesn't capture
           a stack-local std::function by reference. *)
        let decls, defs, deref_subst =
          gen_local_fix_ycomb env renamed_ids funs_with_params
        in
        let remaining_params =
          let rec drop n lst =
            if n = 0 then lst
            else match lst with [] -> [] | _ :: t -> drop (n - 1) t
          in
          drop n_provided fix_params
        in
        let tvars = get_current_type_vars () in
        let pa_params =
          List.mapi
            (fun j (_, ml_ty) ->
              let cpp_ty =
                convert_ml_type_to_cpp_type env tvars ml_ty
              in
              (cpp_ty, Some (Id.of_string (Printf.sprintf "_pa%d" j))) )
            remaining_params
        in
        let pa_exprs =
          List.map (fun (_, id_opt) -> CPPvar (Option.get id_opt)) pa_params
        in
        let fix_id = fst (List.nth renamed_ids x) in
        let full_call = CPPfun_call (CPPvar fix_id, List.rev (args @ pa_exprs)) in
        decls @ defs
        @ deref_subst [k (CPPlambda (List.rev pa_params, None, [Sreturn (Some full_call)], true))]
      end else begin
        let owned_flags_per_fun =
          Array.to_list (Array.map (fun f ->
            let lam_ids, inner_body = Mlutil.collect_lams f in
            let n_params =
              List.length
                (List.filter
                   (fun (_, ty) -> not (ml_type_is_void ty))
                   lam_ids)
            in
            let n_fix = Array.length funs in
            let all_flags =
              Escape.infer_owned_params (n_params + n_fix) inner_body
            in
            List.init n_params (fun i -> List.nth all_flags i)
          ) funs)
        in
        let decls, defs =
          gen_local_fix_by_ref env renamed_ids funs_with_params
            owned_flags_per_fun
        in
        decls @ defs
        @ [k (CPPfun_call (CPPvar (fst (List.nth renamed_ids x)), args))]
      end
  | MLfix (x, ids, funs, _) ->
    (* Standalone fixpoint (not immediately applied) — e.g., appearing as the
       RHS of a let-binding.  Since the fixpoint value itself is returned (not
       called in place), it will always escape.  Use the Y-combinator pattern:
       the generated wrapper lambda [fix_name] is already a plain callable. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled =
      Array.to_list
        (Array.mapi
           (fun i f ->
             gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
           funs )
    in
    let renamed_ids =
      List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
    in
    let funs_with_params =
      List.map (fun (_, params, body) -> (params, body)) funs_compiled
    in
    let decls, defs, _deref_subst =
      gen_local_fix_ycomb env renamed_ids funs_with_params
    in
    let fix_id = fst (List.nth renamed_ids x) in
    decls @ defs @ [k (CPPvar fix_id)]
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h -> gen_stmts env k
     (MLapp (a1, a2::[])) *)
  | MLapp (MLglob (r, bind_tys), a1 :: a2 :: l) when is_bind r ->
    (* Reified mode: bind is a real function call, not desugared. *)
    if tctx.itree_mode = Reified then
      let saved_dead = tctx.move_dead_after in
      let e = gen_tail_expr env ast in
      let result = inline_iife k e in
      tctx.move_dead_after <- saved_dead;
      result
    else begin
      (* Sequential mode: desugar bind into sequential statements. *)
      let a_ml, f = Common.last_two (a1 :: a2 :: l) in
      let a = gen_expr env a_ml in
      let ids', f = collect_lams f in
    (* Resolve metas in continuation parameter types using bind's type
       arguments. bind has type forall A B, IO A -> (A -> IO B) -> IO B. The
       first type argument is A, which is the type of the continuation
       parameter. Use mgu to unify them, which mutably resolves metas. Skip
       Tdummy entries in bind_tys — these come from failed type extractions in
       make_tyargs (e.g., HKT type constructors that can't be extracted).
       Unifying a meta with Tdummy would not resolve it usefully. *)
    let non_dummy_bind_tys = filter_value_types bind_tys in
    let () =
      match non_dummy_bind_tys with
      | elem_ty :: _ -> List.iter (fun (_, ty) -> try_mgu ty elem_ty) ids'
      | [] -> ()
    in
    let ids, env =
      push_vars'
        (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids')
        env
    in
    push_env_types ids;
    (* The continuation's lambda parameter adds one de Bruijn level.
       Shift move tracking sets so that parent-scope owned-variable indices
       stay in sync with the body's coordinate system.  Without this shift,
       after N bind continuations the indices drift by N, causing spurious
       collisions that produce incorrect std::move (use-after-move). *)
    let add_owned =
      match ids with
      | (_, ty) :: _ when Escape.is_shared_ptr_type ty
                          || is_nontrivial_value_ml_type ty -> Some 1
      | _ -> None
    in
    with_shifted_move_tracking 1 ?add_owned (fun () ->
    match ids with
    | (x, ml_ty) :: _ ->
      let tvars = get_current_type_vars () in
      let ty = convert_ml_type_to_cpp_type env tvars ml_ty in
      if ty == Tvoid || ty == Tunknown || ml_type_is_unit ml_ty then
        (* Unit/void bind result: execute the action for side effects,
           then declare the variable as Unit::e_TT so the continuation
           can reference it if needed. *)
        let action_is_pure_ret =
          match a_ml with
          | MLapp (MLglob (r, _), _) when is_ret r -> true
          | _ -> false
        in
        let side_effect =
          match a with
          | CPPenum_val _ -> []
          | _ when action_is_pure_ret -> []
          | _ -> [Sexpr a]
        in
        (* Generate the continuation first, then check if the variable is
           actually referenced in the generated C++ (unit-match elimination
           and Ret-in-void optimization may drop ML-level references). *)
        let body = gen_stmts env k f in
        let cpp_ty = convert_ml_type_to_cpp_type env tvars ml_ty in
        let decl =
          if not (stmts_reference_var x body) then []
          else if ml_type_is_unit ml_ty && not (is_cpp_unit_type cpp_ty) then
            []
          else if ml_type_is_unit ml_ty then
            [Sasgn (x, Some cpp_ty, mk_tt_expr ())]
          else
            []
        in
        side_effect @ decl @ body
      else begin
        match extract_block_template a with
        | Some (ref, tmpl, args, tys) ->
          Sblock_custom (ref, tmpl, x, ty, args, tys)
          :: gen_stmts env k f
        | None ->
          Sasgn (x, Some ty, a) :: gen_stmts env k f
      end
    | _ ->
      (* No lambda parameters (eta-reduced continuation like bare Ret).
         Execute the action for side effects, then run the continuation. *)
      let side_effect =
        match a with CPPenum_val _ -> [] | _ -> [Sexpr a]
      in
      ( match f with
      | MLglob (r, _) when is_ret r ->
        (* Eta-reduced Ret: bind action Ret = action (monad right identity).
           In sequential mode, just execute the action and return. *)
        if tctx.current_cpp_return_type = Some Tvoid then
          side_effect @ [Sreturn None]
        else
          [k a]
      | _ ->
        (* Eta-reduced non-Ret continuation: f is a bare function reference.
           Bind action result to a temp var and apply f to it, instead of
           discarding the result and returning f unapplied. *)
        let tvars = get_current_type_vars () in
        let non_void_ty =
          match non_dummy_bind_tys with
          | ty :: _ ->
            let cpp_ty =
              convert_ml_type_to_cpp_type env tvars ty
            in
            if cpp_ty = Tvoid || cpp_ty = Tunknown || ml_type_is_unit ty then
              None
            else
              Some cpp_ty
          | [] -> None
        in
        ( match non_void_ty with
        | Some cpp_ty ->
          let temp_id = Id.of_string "_bind_result" in
          let f_expr = gen_expr env f in
          let app = CPPfun_call (f_expr, [CPPvar temp_id]) in
          [Sasgn (temp_id, Some cpp_ty, a); k app]
        | None ->
          side_effect @ gen_stmts env k f ) ) )
    end
  | MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
    if tctx.itree_mode = Reified then begin
      (* Reified mode: Ret is a constructor call, not desugared. *)
      let saved_dead = tctx.move_dead_after in
      let e = gen_tail_expr env ast in
      let result = inline_iife k e in
      tctx.move_dead_after <- saved_dead;
      result
    end
    else begin
      (* Sequential mode: eliminate Ret, just use the value. *)
      let t = Common.last (a1 :: l) in
      if tctx.current_cpp_return_type = Some Tvoid then
        (* Void-returning function: discard the value and return. *)
        [Sreturn None]
      else
        [k (gen_expr ?expected_ty:tctx.current_cpp_return_type env t)]
    end
  | MLcase (typ, t, pv) when is_custom_match pv ->
    (* Set up dead-after for owned variables at their last use, same as the
       default tail-position case below. Without this, owned variables
       passed as function arguments in the scrutinee would not get std::move.
       Suppress when processing a let-binding RHS to avoid use-after-move. *)
    let saved_dead = tctx.move_dead_after in
    ( if not tctx.move_suppress_tail then
        let tail_dead =
          Escape.IntSet.filter
            (fun i -> Escape.nb_occur_match i ast = 1)
            tctx.move_owned_vars
        in
        tctx.move_dead_after <-
          Escape.IntSet.union tctx.move_dead_after tail_dead );
    let result = gen_custom_cpp_case env k typ t pv in
    tctx.move_dead_after <- saved_dead;
    result
  | MLcons (_, r, []) when Table.is_tt_constructor r
      && tctx.current_cpp_return_type = Some Tvoid ->
    (* tt (unit constructor) in tail position of a void-returning function *)
    if tctx.itree_mode = Reified then begin
      Table.require_itree_header ();
      [k (mk_itree_ret Tvoid [])]
    end
    else
      [Sreturn None]
  | MLglob (r, _) when is_ghost r ->
    if tctx.itree_mode = Reified then begin
      (* Reified mode: ghost (void value) at tail position must produce
         ITree<void>::ret() rather than bare return, since the function
         returns shared_ptr<ITree<void>>. *)
      Table.require_itree_header ();
      [k (mk_itree_ret Tvoid [])]
    end
    else
      [Sreturn None]
  | MLexn msg ->
    (* Generate throw statement for unreachable/absurd cases (e.g., empty
       match) *)
    [Sthrow msg]
  | MLmagic (MLexn msg) ->
    (* Handle MLexn wrapped in MLmagic *)
    [Sthrow msg]
  | MLcase (typ, t, pv)
    when (not (record_fields_of_type typ == [])) && Array.length pv == 1 ->
    let ids, _r, _pat, body = pv.(0) in
    let n = List.length ids in
    let body' = match body with MLmagic b -> b | b -> b in
    let is_simple =
      match body' with
      | MLrel i when i <= n -> true
      | MLapp (MLrel i, _) when i <= n -> true
      | MLapp (MLmagic (MLrel i), _) when i <= n -> true
      | _ -> false
    in
    if is_simple then
      (* Simple body: gen_expr handles these as direct field access (no IIFE),
         so delegate to the default path. *)
      let saved_dead = tctx.move_dead_after in
      ( if not tctx.move_suppress_tail then
          let tail_dead =
            Escape.IntSet.filter
              (fun i -> Escape.nb_occur_match i ast = 1)
              tctx.move_owned_vars
          in
          tctx.move_dead_after <-
            Escape.IntSet.union tctx.move_dead_after tail_dead );
      let result = inline_iife k (gen_expr ?expected_ty:tctx.current_cpp_return_type env ast) in
      tctx.move_dead_after <- saved_dead;
      result
    else
      (* Complex body: emit field extraction assignments as flat statements
         instead of wrapping in an IIFE. This produces clean code for all
         continuations (return, assignment, etc.). *)
      let is_typeclass = Table.is_typeclass_type typ in
      let all_fields = record_fields_of_type typ in
      let non_erased_fields = List.filter_map Fun.id all_fields in
      let make_field_access base_expr fld =
        if is_typeclass then
          let fld_name = Id.of_string (Common.pp_global_name Term fld) in
          CPPqualified (base_expr, fld_name)
        else
          CPPget' (base_expr, fld)
      in
      let renamed_ids, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      let renamed_ids_fwd = List.rev renamed_ids in
      let tvars = get_current_type_vars () in
      let asgns =
        List.concat_map
          (fun (i, ((renamed_name, _), (_, ty))) ->
            let fld =
              try Some (List.nth non_erased_fields i) with _ -> None
            in
            let e =
              match fld with
              | Some fld -> make_field_access (gen_expr env t) fld
              | _ ->
                CErrors.anomaly (Pp.str "record field index out of bounds")
            in
            let e =
              match typ with
              | Tglob (record_ref, _, _) ->
                let storage_ty =
                  convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton record_ref)
                    tvars
                    ty
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env tvars ty
                in
                wrap_api_expr ~storage_ty ~api_ty e
              | _ -> e
            in
            let api_ty_for_decl =
              convert_ml_type_to_cpp_type env tvars ty
            in
            let decl_ty =
              if has_tany_in_type api_ty_for_decl then
                Tref (Tmod (TMconst, Tauto))
              else
                api_ty_for_decl
            in
            match lift_iife_assignment renamed_name decl_ty e with
            | Some stmts -> stmts
            | None -> [Sasgn (renamed_name, Some decl_ty, e)])
          (List.mapi (fun i x -> (i, x)) (List.combine renamed_ids_fwd ids))
      in
      let env_ids =
        List.map
          (fun ((n, _), (_, ty)) -> (n, ty))
          (List.combine renamed_ids_fwd ids)
        |> retype_dependent_params typ
      in
      push_env_types env_ids;
      asgns @ gen_stmts env' k body
  | t ->
    (* Tail position: generate expression with dead-after tracking.
       No deref_reified needed: in sequential mode, monadic variables are
       direct values (bind desugars to let-binding); in reified mode,
       they are trees returned as-is. *)
    let saved_dead = tctx.move_dead_after in
    let is_void_tail = match t with
      | MLapp (f, args) | MLmagic (MLapp (f, args)) ->
        ml_callee_is_void f
        (* Only treat as void if fully applied — partial applications
           return a function value, not void. *)
        && ( match f with
           | MLglob (r, _) ->
             ( match find_type_opt r with
             | Some ty ->
               let rec count_arrows = function
                 | Miniml.Tarr (t1, rest) ->
                   if isTdummy t1 then count_arrows rest
                   else 1 + count_arrows rest
                 | _ -> 0
               in
               let n_non_dummy_args =
                 List.length (List.filter (fun a ->
                   match a with MLdummy _ -> false | _ -> true) args)
               in
               n_non_dummy_args >= count_arrows ty
             | None -> true )
           | _ -> true )
      | _ -> false
    in
    if is_void_tail then begin
      let e = gen_tail_expr ?expected_ty:tctx.current_cpp_return_type env t in
      tctx.move_dead_after <- saved_dead;
      if tctx.current_cpp_return_type = Some Tvoid then
        [Sexpr e; Sreturn None]
      else
        match k (CPPint 0) with
        | Sexpr _ ->
          (* Side-effect-only continuation (e.g. from unit let handler).
             The void call provides the side effect; the caller handles
             the variable declaration separately.  No value needed. *)
          [Sexpr e]
        | _ ->
          [Sexpr e] @ inline_iife k (mk_tt_expr ())
    end
    else begin
      let e = gen_tail_expr ?expected_ty:tctx.current_cpp_return_type env t in
      let result = inline_iife k e in
      tctx.move_dead_after <- saved_dead;
      result
    end

(** Generate a C++ expression for [t] in tail position.
    Marks owned variables that occur exactly once as dead-after (for
    last-use move semantics).  Callers are responsible for saving and
    restoring [move_dead_after].

    Used by the default tail case and by reified-mode bind/ret handlers
    (which bypass monadic desugaring and treat bind/Ret as plain calls). *)
and gen_tail_expr ?expected_ty env t =
  ( if not tctx.move_suppress_tail then
      let tail_dead =
        Escape.IntSet.filter
          (fun i -> Escape.nb_occur_match i t = 1)
          tctx.move_owned_vars
      in
      tctx.move_dead_after <-
        Escape.IntSet.union tctx.move_dead_after tail_dead );
  gen_expr ?expected_ty env t

(** Generate a fixpoint (recursive function) definition. Handles both single and
    mutually recursive functions. [all_fix_ids] contains names of all mutual
    fixpoints; [fix_idx] is the index of this fixpoint in the mutual group. *)
and gen_fix env ?(all_fix_ids = []) ~fix_idx (n, ty) f =
  let ids, f = collect_lams f in
  let ids, _ =
    push_vars'
      (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids)
      env
  in
  (* Push all mutual fixpoint names (or just (n,ty) for single fixpoints). For
     mutual fixpoints, all_fix_ids contains all fixpoint names in array order.
     For single fixpoints, all_fix_ids is empty and we use [(n,ty)].

     IMPORTANT: Rocq's extraction pushes fix bindings so that the LAST function
     is at db 1 and the FIRST is at db n (standard de Bruijn convention with
     fold_left over the array). We must reverse fix_names to match. *)
  let fix_names = if all_fix_ids = [] then [(n, ty)] else all_fix_ids in
  let n_fix_funs = List.length fix_names in
  let fix_names_db_order = List.rev fix_names in
  let renamed_fix_ids, env = push_vars' (ids @ fix_names_db_order) env in
  let saved_env_types = tctx.env_types in
  push_env_types (ids @ fix_names_db_order);
  (* Extract the renamed name for THIS fixpoint function. fix_names_db_order
     is reversed from the array order, so fix array index i corresponds to
     position (n_fix_funs - 1 - i) in the reversed list. *)
  let n_lam_params = List.length ids in
  let renamed_n =
    fst (List.nth renamed_fix_ids
           (n_lam_params + (n_fix_funs - 1 - fix_idx))) in
  let ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) ids in
  (* Phase 2: set up move state for fixpoint body. Fix params are owned (passed
     by value in the generated std::function lambda). After push_vars'(ids @
     fix_names), de Bruijn indices in f are: ids[0] → db 1, ..., ids[k-1] → db
     k, fix_names[0] → db k+1, ..., fix_names[m-1] → db k+m. We only mark lambda
     params as owned (not the fix self-references). *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let n_fix_params = List.length ids in
  let n_total = n_fix_params + n_fix_funs in
  let fix_owned_base = Escape.infer_owned_params n_total f in
  let fix_sub_esc = Escape.infer_sub_bindings_escape_params n_total f in
  tctx.move_owned_vars <-
    List.fold_left
      (fun acc i ->
        let db = i + 1 in
        let base_owned =
          match List.nth_opt fix_owned_base i with
          | Some b -> b
          | None -> false
        in
        let sub_esc =
          match List.nth_opt fix_sub_esc i with
          | Some b -> b
          | None -> false
        in
        let ml_ty = snd (List.nth ids i) in
        let owned = base_owned
          || (sub_esc && is_prod_ml_type ml_ty) in
        if owned && (Escape.is_shared_ptr_type ml_ty
                     || is_nontrivial_value_ml_type ml_ty) then
          Escape.IntSet.add db acc
        else
          acc )
      Escape.IntSet.empty
      (List.init n_fix_params (fun i -> i));
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_n_params <- n_fix_params + n_fix_funs;
  let result =
    ((renamed_n, ty), ids, gen_stmts env (fun x -> Sreturn (Some x)) f)
  in
  tctx.env_types <- saved_env_types;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  result

(** Whether [expr] is a numeral-converter application (e.g.
    [Nat.of_num_uint (Number.UIntDecimal ...)]) that {!gen_expr} folds into a
    literal via [Table.get_numeral_info].  When true, the whole subtree is
    replaced by a raw integer literal at translation time, so the converter and
    its digit-chain argument (and everything they transitively reference) are
    never emitted.  Dependency collection uses this to avoid pulling in the
    vestigial [of_num_uint]/[of_uint]/[Uint] machinery. *)
let is_foldable_numeral_converter_app = function
  | MLapp (MLglob (r, _), [arg]) when Table.is_numeral_converter r ->
    ( match try_fold_num_uint arg with
    | Some _ -> true
    | None -> Option.has_some (try_fold_num_int arg) )
  | _ -> false

(** Set method_self_ns from local_inductives for standalone functions.
    Functions inside wrapper modules (e.g. Cotree.tree_of_cotree) construct
    containers whose type parameters must use shared_ptr for recursive
    value-type inductives, matching struct field types.  Returns the saved
    previous value for restoration. *)
let set_method_ns_for_locals () =
  let saved = tctx.method_self_ns in
  let full_ns =
    List.fold_left
      (fun acc g ->
        if Table.has_recursive_fields g && not (is_enum_inductive g)
        then Refset'.add g acc
        else acc)
      tctx.method_self_ns
      (get_local_inductives ())
  in
  tctx.method_self_ns <- full_ns;
  saved

(** Restore method_self_ns to a previously saved value. *)
let restore_method_self_ns saved =
  tctx.method_self_ns <- saved

