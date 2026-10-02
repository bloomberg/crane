(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What translation shares below its type conversion: constructor field
    naming, monad and void-call handling, type-variable collection and meta
    resolution, the parameters of lifted fixpoints, ownership and escape
    analysis, and the conversions between storage and API representations. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Util
open Translation_state
open Ml_type_util


(** Compute the factory method name for a constructor.
    Factory names are the lowercase of the constructor struct name
    (e.g. [Cons] -> ["cons"]). If the lowercased name collides with a C++
    keyword, one of {!Common.inductive_generated_members}, or the enclosing
    type's own name (which
    C++ treats as a constructor declaration), the original PascalCase is kept
    with a trailing underscore
    (e.g. [Char] -> ["Char_"]).

    @param type_name  the enclosing inductive type's C++ name, for same-name
                      collision detection (default [""]) *)
let factory_name_of_ctor ?(type_name = "") ctor_struct_name =
  let lc = String.lowercase_ascii ctor_struct_name in
  let collides =
    Common.is_reserved_cpp_name lc
    || lc = String.lowercase_ascii type_name
    || Id.Set.mem (Id.of_string lc) Common.inductive_generated_members
  in
  if collides then ctor_struct_name ^ "_"
  else lc

(** The type a never-returning expression is spelled with, given whatever type
    the slot it sits in called for.  {!Tany} is what an erased slot asks for,
    and the only thing left to say when the slot named no type; nothing here
    guesses past that. *)
let abort_ty : cpp_type option -> cpp_type = function
  | Some ty -> ty
  | None -> Tany

(** The C++ name of the inductive that [cref] constructs, or [""] when [cref]
    is not a constructor reference.  {!factory_name_of_ctor} needs it, and a
    caller holding only the constructor should not have to take the inductive
    apart to supply it. *)
let owning_type_name cref =
  match cref with
  | GlobRef.ConstructRef ((kn, i), _) ->
    Common.pp_global_name Type (GlobRef.IndRef (kn, i))
  | _ -> ""

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
      if Common.is_reserved_cpp_name sanitized then
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
let compute_field_name ~owner ctor_struct_name field_consarg_names
    bind_consarg_names _n_fields j =
  let base_str = field_name_str_of_idx field_consarg_names j in
  (* A field shares its scope with the earlier fields, with the factory method,
     with the members the struct generates for itself, and with the type names
     visible there -- its own struct and the inductive that struct belongs to,
     either of which a same-named member would hide.  All are resolved the same
     way, by falling back to the indexed form. *)
  let type_name = owning_type_name owner in
  let reserved =
    Id.Set.union Common.inductive_generated_members
      (Id.Set.of_list
         (List.map Id.of_string
            ( ctor_struct_name :: type_name
              :: factory_name_of_ctor ~type_name ctor_struct_name
              :: List.init j (field_name_str_of_idx field_consarg_names) ) ))
  in
  let needs_index = Id.Set.mem (Id.of_string base_str) reserved in
  let field_str =
    if needs_index then base_str ^ "_" ^ string_of_int j else base_str
  in
  let field_id = Id.of_string field_str in
  register_ctor_field_name ~owner ctor_struct_name j field_id;
  (* Binding variable name: use indexed fallback for anonymous kernel binders
     to prevent shadowing when nested matches on the same type reuse [a0]/[l0]. *)
  let bind_id =
    match List.nth_opt bind_consarg_names j with
    | Some (Some _) -> field_id  (* kernel-named: same as field for readability *)
    | _ -> field_param_id j      (* anonymous kernel binder: safe indexed fallback *)
  in
  register_ctor_bind_name ~owner ctor_struct_name j bind_id;
  field_id

(** Compute and register field names for all [n_fields] fields of a
    constructor struct.  [field_consarg_names] supplies the pretty names used
    for struct field declarations (may include [Arguments_renaming] overrides);
    [bind_consarg_names] supplies the kernel-only names used for structured-
    binding variable generation. *)
let compute_and_register_field_names ~owner ctor_struct_name
    field_consarg_names bind_consarg_names n_fields =
  List.init n_fields (fun j ->
    compute_field_name ~owner ctor_struct_name field_consarg_names
      bind_consarg_names n_fields j)

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
    (i.e. its monad template string contains ["ITree"]).

    Lives in {!Table} because {!Ml_type_util} asks it too, to recognise an
    event family. *)
let is_monad_reified = Table.is_monad_reified

(** If the codomain of [ty] is a registered monad, return its reference. *)
let extract_monad_from_codomain ty =
  match ml_codomain ty with
  | Miniml.Tglob (monad_ref, _, _) when Table.is_monad monad_ref ->
    Some monad_ref
  | _ -> None

(* [ref_is_skipped] and [ml_ret_is_skipped] live in {!Ml_type_util}, which
   {!Method_registry} also asks. *)

(* {!Ml_type_util.ml_type_is_instance} works the answer out; a caller with a
   global asks {!ref_is_instance} and one with a binder asks
   {!binder_is_instance}. *)

(** Collect [Id.t]s for typeclass-typed parameters in an ML arrow type.

    Only a parameter whose class Crane kept: each becomes a concept-constrained
    template parameter, and one whose class was skipped has nothing to be
    constrained by.  A skipped instance still has to be recognised as one where
    it is {e used} -- see {!binder_is_instance}. *)
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

(** A type variable that really denotes an associated type of a type-class
    instance parameter: [htp_tvar] stands for [typename <htp_instance>::<htp_field>]. *)
type hkt_tvar_position = {
  htp_tvar : int;
  htp_instance : Minicpp.cpp_type;  (** always a {!Minicpp.Tinstance} *)
  htp_field : Id.t;
}

(** The type variables of an ML arrow type that stand for a higher-kinded
    class parameter: [mret : forall M, Mon M -> forall A, A -> M A] passes the
    variable for [M A] as the type-constructor argument of its [Mon]
    parameter.  Such a variable is not a C++ template parameter but the
    instance's associated type — see {!Table.get_ind_hkt_params}.

    Instance parameters are numbered as [Gen_decls.gen_dfun] numbers them --
    it walks the binders innermost first, so the source-{e last} instance is
    [_tcI0].  With one instance the two orders coincide; with two they do not,
    and a signature numbered the other way swaps the functors. *)
let hkt_tvar_positions_of_type ty =
  let last = List.length (collect_typeclass_param_ids ty) - 1 in
  let rec go i acc = function
    | Miniml.Tarr (Miniml.Tglob (class_ref, type_args, _), rest)
      when Table.is_typeclass class_ref ->
      let ip_vars = Table.get_ind_ip_vars class_ref in
      let acc =
        List.fold_left
          (fun acc pos ->
            match (List.nth_opt type_args pos, List.nth_opt ip_vars pos) with
            | ( Some (Miniml.Tvar (_, j) | Miniml.Tapp (j, _)),
                Some var_name ) ->
              { htp_tvar = j;
                htp_instance =
                  Minicpp.Tinstance (tc_instance_id (last - i), class_ref);
                htp_field = var_name }
              :: acc
            | _ -> acc )
          acc
          (Table.get_ind_hkt_params class_ref)
      in
      go (i + 1) acc rest
    | Miniml.Tarr (_, rest) -> go i acc rest
    | _ -> acc
  in
  go 0 [] ty

(** Apply unit-to-void conversion on a C++ type.  [unit_void] comes from
    {!ml_type_is_void_call}, which already declines for a reified monad, so
    there is one outcome left: the whole type is [void]. *)
let apply_unit_void unit_void ty = if unit_void then Tvoid else ty

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

(** Whether [ty]'s codomain is a monad extracted as a reified tree. *)
let codomain_is_reified_monad (ty : Miniml.ml_type) : bool =
  match ml_codomain ty with
  | Miniml.Tglob (r, _, _) -> Table.is_monad r && is_monad_reified r
  | _ -> false

(** Whether [ty] is the type of something whose C++ call returns [void]: a
    function (or monad) whose result type is [unit].  Such a call cannot be
    used as a value — it must be wrapped in an IIFE that executes it for its
    side effect and returns [std::monostate{}].

    A monad counts only in sequential mode, where a monadic value {e is} the
    running of its effects and a [unit] result is therefore nothing.  Under the
    reified backend it is data: [itree E unit] is a tree that has to be
    returned, built, and bound into, and void-ifying it does not merely mistype
    the call -- it drops the tree, and with it the sequencing the program was
    expressed in. *)
let ml_type_is_void_call (ty : Miniml.ml_type) : bool =
  (match Ml_type_util.resolve_tmeta ty with
  | Miniml.Tarr _ -> true
  | Miniml.Tglob (r, _, _) -> Table.is_monad r
  | _ -> false)
  && ml_type_is_unit (ml_result_type ty)
  && not (codomain_is_reified_monad ty)

(** Whether a global reference [r] has been void-ified.

    An inline custom is void-ified in reified mode as well.  Its replacement
    text is written once, in the sequential spelling -- [std::cout << s] is a
    statement, not a tree -- so its Rocq type saying [itree E unit] does not
    make its C++ a tree.  The lift into [ITree<R>::ret()] at the call site is
    what makes it one, and that lift is keyed on this. *)
let is_void_ified_ref (r : GlobRef.t) : bool =
  match find_type_opt r with
  | Some ty ->
    ml_type_is_void_call ty
    || Table.is_inline_custom r
       && ml_type_is_unit (ml_result_type ty)
       && codomain_is_reified_monad ty
  | None -> false

(** Wrap a void-returning function call expression in an IIFE so it can
    be used in value context.  Produces:
      [&]() { void_call(); return std::monostate{}; }()
    The call is executed for side effects; the IIFE returns the unit value. *)
let wrap_void_call_as_value (call_expr : cpp_expr) : cpp_expr =
  mk_iife None [Sexpr call_expr; Sreturn (Some (mk_tt_expr ()))]

(** Check whether an ML function expression [f] in [MLapp(f, args)] would
    produce a void-returning call in C++.  Handles:
    - [MLglob(r, _)]  — named function, look up type in extraction table
    - [MLrel(i)]       — variable (e.g. callback), look up type in env
    - [MLmagic] — transparent wrapper, recurse *)
let rec ml_callee_is_void = function
  (* A record field of a [unit]-returning function type is stored as a
     [std::function<void(...)>]: [globals_object.(globals_set) gs]. *)
  | MLglob (r, _) when Table.is_projection r -> (
    try ml_type_is_void_call (Table.find_type r) with Not_found -> false )
  | MLglob (r, _) -> is_void_ified_ref r
  | MLmagic (_, inner) -> ml_callee_is_void inner
  | MLrel i -> ( try ml_type_is_void_call (get_env_type i) with _ -> false )
  | _ -> false

(** Whether the C++ for an ML expression is a statement rather than a value:
    a call to something void-ified, applied or not. *)
let ml_expr_is_void_call = function
  | MLapp (f, _) -> ml_callee_is_void f
  | e -> ml_callee_is_void e

(** Whether an ML expression in a value position may compile to a [void] call,
    and so has to be wrapped by {!wrap_void_call_as_value}: a call to something
    void-ified, or a match whose every branch is one -- the projection
    extraction writes [r.(f) x] as, applying a field binder of a
    [unit]-returning function type, stored as [std::function<void(...)>]. *)
let rec ml_value_is_void_call = function
  | MLapp (f, _) -> ml_callee_is_void f
  | MLmagic (_, e) -> ml_value_is_void_call e
  | MLcase (_, _, pv) ->
    Array.length pv > 0
    && Array.for_all
         (fun (binds, _, _, body) ->
           let applies_void_binder = function
             | MLapp (MLrel k, _) when k >= 1 && k <= List.length binds -> (
               match List.nth_opt binds (List.length binds - k) with
               | Some (_, ty) -> ml_type_is_void_call ty
               | None -> false )
             | e -> ml_value_is_void_call e
           in
           match body with
           | MLmagic (_, b) -> applies_void_binder b
           | b -> applies_void_binder b )
         pv
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
  Tshared_ptr (Tid_external ("ITree", [r_cpp]))

(** Recursively wrap [Tglob] inductive references with [Tnamespace] so that
    the type printer produces fully-qualified names.  The [~skip]
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
  | Tref (k, t) -> Tref (k, qualify_inductives ~skip t)
  | Tconst t -> Tconst (qualify_inductives ~skip t)
  | Tptr t -> Tptr (qualify_inductives ~skip t)
  | Tfun (args, ret) ->
    Tfun (List.map (qualify_inductives ~skip) args,
          qualify_inductives ~skip ret)
  | Tid (id, ts) -> Tid (id, List.map (qualify_inductives ~skip) ts)
  | Tid_external (id, ts) ->
    Tid_external (id, List.map (qualify_inductives ~skip) ts)
  | Tnondeduced t -> Tnondeduced (qualify_inductives ~skip t)
  | Trebind (h, x) ->
    Trebind (qualify_inductives ~skip h, qualify_inductives ~skip x)
  | Tqualified (base, id) ->
    Tqualified (qualify_inductives ~skip base, id)
  | t -> t

(** The real type printer ([Cpp_print.pp_cpp_type]), installed by {!Cpp_print}
    at load time because this module cannot depend on it.

    There used to be a second, string-level renderer here for callers that ran
    before the printer was installed.  Nothing runs before a module's own
    top-level initialiser, so it never did -- what it did do was spell a
    handful of types differently from the printer (in Coq form, patched back
    with three [Str.global_replace] passes), which is the whole of what a raw
    template string embedded in printer output must not do. *)

(** Whether a reference was methodified: spelled [x.f(...)] rather than
    [f(x, ...)]. *)
let is_methodified r = Cpp_names.lookup_method_this_pos r <> None


let build_guard_compare_stmts n ids =
  match Table.find_guard_compare n with
  | None -> []
  | Some ctor_ref ->
    let strip_wrappers t =
      let rec go = function
        | Tref (_, t) | Tconst t | Tnamespace (_, t) -> go t
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
        | GlobRef.ConstructRef ((kn, i), _cidx) ->
          (* Parametric constructor (e.g. [OrderedType.EQ : eq x y -> Compare
             lt eq x y]): render as [Type<temps>::factory()], mirroring the
             ordinary [MLcons] constructor-call codegen. The template args
             ([temps]) come from the enclosing function's own return type
             ([cod]), since the guard only fires when the function returns
             this same inductive. *)
          let ind = GlobRef.IndRef (kn, i) in
          let ctor_struct = ctor_struct_name_of_ref ctor_ref in
          let ind_type_name = Common.pp_global_name Type ind in
          let fname = factory_name_of_ctor ~type_name:ind_type_name ctor_struct in
          (* The qualifier is a type and is spelled as one, so the type printer
             supplies both halves this used to render by hand: the enclosing
             module of the inductive (e.g. "OrderedType::Compare", see
             [OrderedTypeEx.h]/[FSetInterface.h]), and any enclosing-functor
             "D::Defs::" prefix on the compared value's own type.  That prefix
             is why the argument comes from [ids] rather than from [cod]'s
             converted return type, which loses it during ml_type -> cpp_type
             conversion (a pre-existing asymmetry with parameter-type
             conversion: the same underlying type converts to a bare
             unqualified name from [cod] but to "typename
             D::Defs::sll_subparser" from the parameter list). *)
          let p1_ty = strip_wrappers (snd (List.find (fun (i, _) -> i = p1) ids)) in
          mk_call
            (CPPqualified_t (Tglob (ind, [p1_ty], []), Id.of_string fname))
            []
        | _ -> mk_cppglob ctor_ref []
      in
      [ Sif
          ( CPPbinop (Beq, CPPunop (Uaddr, CPPvar p1), CPPunop (Uaddr, CPPvar p2)),
            [Sreturn (Some ctor_expr)], [] ) ]
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
  let strip_const = function Tconst t -> t | t -> t in
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
      | Some t -> Common.contains_substring t.it_text "make_pair"
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
        CPPmove (CPPaccess (Adot, CPPvar scrut_id, first_id))
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
        ~on_expr:(fun acc child -> acc + count_state_uses subst child)
        ~on_stmts:(fun acc stmts ->
          List.fold_left
            (fun acc s -> acc + count_state_uses_stmt subst s) acc stmts)
        0 e
  and count_state_uses_stmt subst s =
    fold_stmt_children
      ~on_expr:(fun acc e -> acc + count_state_uses subst e)
      ~on_stmts:(fun acc stmts ->
        List.fold_left
          (fun acc s -> acc + count_state_uses_stmt subst s) acc stmts)
      0 s
  in
  let rec rewrite_expr subst e =
    match e with
    | CPPfun_call (res, (CPPglob (g, tys, ci) as fn), args)
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
      CPPfun_call (res, fn, map_args move_states args)
    | CPPfun_call (res, fn, {rev = [r_arg; s_arg]}) when is_make_pair_fn fn ->
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
      CPPfun_call (res, fn, of_reversed [rewrite_expr subst r_arg; s_arg'])
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

(** [is_access_path e] -- [e] is a chain of variable reads, dereferences,
    field selections and nullary accessors, so naming it twice in one
    expression duplicates no work and no side effect. *)
let rec is_access_path = function
  | CPPvar _ | CPPthis | CPPnullptr -> true
  | CPPderef e | CPPget (e, _) | CPPget' (e, _, _) | CPPaccess (_, e, _) ->
    is_access_path e
  | CPPaccess_call (_, e, _, []) -> is_access_path e
  | _ -> false

(** When [expr] is a single-argument IIFE
    [CPPfun_call(CPPlambda
      { cl_params = [(ty, id)];
        cl_ret = ret;
        cl_body = body;
        cl_capture = Immediate }, [arg])], lift the
    lambda body into assignment statements targeting [target_var]:
    {[
      Type target_var{};
      const auto& param = arg;
      <body with "return X;" rewritten to "target_var = X;">
    ]}
    Returns [Some stmts] on success, [None] if [expr] is not a liftable IIFE.
    [target_ty] is [None] where the declaration has no type of its own to
    impose, and the lambda's return type is used instead. *)
let lift_iife_assignment target_var (target_ty : cpp_type option) expr =
  match expr with
  | CPPfun_call (_, 
      CPPlambda
        { cl_params = {rev = [(param_ty, Some param_id)]};
          cl_ret = Some ret_ty;
          cl_body = body;
          cl_capture = Immediate },
      {rev = [arg]}) ->
    let actual_ty = match target_ty with Some t -> t | None -> ret_ty in
    let lifted_body = List.map (function
      | Sreturn (Some e) -> Sasgn (target_var, Existing, e)
      | s -> s
    ) body in
    Some (Sdecl_init (target_var, actual_ty)
          :: Sasgn (param_id, Declare param_ty, arg)
          :: lifted_body)
  | _ -> None

(** For inductives with dependent parameters (e.g. [sigT]), unresolved
    rigid type variables correspond to fields whose C++ type
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
      match ml_ty with Miniml.Tvar (Rigid, _) -> (n, Tdummy Ktype) | _ -> (n, ml_ty)) ids
  else ids

(** The declared ML types of constructor [ctor]'s value fields, instantiated at
    scrutinee type [typ]'s type arguments — the types a branch's pattern
    variables have by construction, in field order.

    [None] when the answer would not be trustworthy: either the inductive has
    no recorded [ip_types] (custom-extracted ones such as [prod] do not; for
    those the scrutinee's own type arguments {i are} the field types), or a
    field mentions a parameter the scrutinee does not instantiate, in which
    case substitution would leave a stray [Tvar] behind and a stray [Tvar] is
    worse than the [std::any] it would replace. *)
let ctor_field_types_at ctor (typ : ml_type) =
  let tyargs = match typ with Tglob (_, args, _) -> args | _ -> [] in
  let nargs = List.length tyargs in
  let rec within_scope : ml_type -> bool = function
    | Tvar (_, i) -> i <= nargs
    | Tapp (i, args) -> i <= nargs && List.for_all within_scope args
    | Tarr (a, b) -> within_scope a && within_scope b
    | Tglob (_, l, _) -> List.for_all within_scope l
    | Tmeta {contents = Some t} -> within_scope t
    | _ -> true
  in
  match Table.get_ctor_ip_types_opt ctor with
  | Some tys ->
    let tys = List.filter (fun t -> not (Mlutil.isTdummy t)) tys in
    if List.for_all within_scope tys then
      Some (List.map (Mlutil.type_subst_list tyargs) tys)
    else None
  | None -> (
    match typ with
    | Tglob (g, _, _) when is_prod_global g -> Some tyargs
    | _ -> None )

(** Recover a pattern variable's type from the scrutinee's own type structure
    when extraction left it as an unresolved meta-variable ([Tmeta
    {contents=None}]).

    For a [prod A B] scrutinee destructured as [(x, y)], [x]'s and [y]'s ML
    types are exactly [A] and [B] — but when [A]/[B] come from a
    non-reducible dependent computation (e.g. projecting an element out of
    [tuple (List.map symbol_semty gamma)] for a nonterminal/production
    grammar), Rocq's extraction can fail to unify the pattern variable's own
    type with the (perfectly concrete, if opaque) component type visible in
    the scrutinee's [Tglob(prod, [A; B])] annotation, leaving the pattern
    variable's type as a dangling meta.  A dangling meta erases to
    [std::any] with no further structure, discarding container information
    (e.g. "this is a [list]") that the scrutinee type still carries — so a
    "cons" production destructuring such a pattern var loses track of the
    fact that it's building a [list], while the "nil" production (whose
    return type is directly, concretely annotated, with no destructuring
    involved) keeps it — the reason nil and cons productions of the very
    same Coq-level [list] type diverge in their erased C++ representation.

    The pair is only the clearest case; the same recovery applies to any
    inductive, which is why the field types come from
    {!ctor_field_types_at} rather than from the scrutinee's type arguments
    directly.

    [ids] here is in reverse-bound order relative to the constructor's fields
    (the last pattern variable in the list is the first field), matching the
    convention already used elsewhere in this file. *)
let recover_pattern_var_types_from_scrutinee ~ctor (typ : ml_type) ids =
  match ctor_field_types_at ctor typ with
  | Some ftys when List.length ftys = List.length ids ->
    let n = List.length ftys in
    List.mapi
      (fun i (x, ml_ty) ->
        let fty = List.nth ftys (n - 1 - i) in
        (* The field at the scrutinee's instantiation is the binder's type
           wherever the pattern's own annotation says less: an open meta, or
           an erased component the scrutinee states ([md] of a pattern over
           [(nat * phi T) * list (metadata T)]). *)
        match ml_ty with
        | Tmeta {contents = None} -> (x, fty)
        | _
          when Ml_type_util.is_ml_erased_ty ml_ty
               && not (Ml_type_util.is_ml_erased_ty fty) ->
          (x, fty)
        | _ -> (x, ml_ty))
      ids
  | _ -> ids

(** Generate an inline C++ expression that converts [expr] from [src_ty] to
    [dst_ty].  Used at every boundary between the storage representation
    (where recursive fields are [shared_ptr]-wrapped) and the API
    representation (where they are bare values).

    Conversion cases:
    - [shared_ptr<S> -> shared_ptr<T>]: null-check, dereference, make_shared
    - [shared_ptr<T> -> T]: dereference (converting ctor if inner ≠ dst)
    - [T -> shared_ptr<T>]: wrap in make_shared
    - [Tglob(g, ts1) -> Tglob(g, ts2)]: same container, different elements
    - Everything else (type variables, scalars): converting constructor

    @param skip    predicate for GlobRefs to skip during qualification
    @param src_ty  the source C++ type
    @param dst_ty  the destination C++ type
    @param expr    the C++ expression to convert
    @return a [cpp_expr] that produces a value of type [dst_ty] *)

let gen_type_conversion_expr ?(skip = fun _ -> false) ~src_ty ~dst_ty expr =
  (* Every type rendered here lands in a raw string inside a template body
     (a converting constructor, a [make_shared<...>] argument), so it must be
     spelled exactly as the printer spells the same type in the surrounding
     generated code -- hence the real printer rather than the eager
     approximation. *)
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
  (* Build an expression that names [expr] twice.  An access path can simply
     be repeated; anything else is bound once as the parameter of an
     immediately-applied lambda, so that its effects happen once.
     [lambda_ty] is that lambda's return type. *)
  let naming_expr ~lambda_ty ~body =
    if is_access_path expr then body expr
    else
      let x = Id.of_string "__x" in
      mk_call
        (mk_lambda
           [(rval_ref Tauto, Some x)]
           (Some lambda_ty)
           [Sreturn (Some (body (CPPvar x)))]
           ~capture:Immediate )
        [expr]
  in
  if src_ty = dst_ty then expr
  else
    (* ---- Different types: dispatch on wrapper structure ---- *)
    match (src_ty, dst_ty) with
    | Tshared_ptr src_inner, Tshared_ptr dst_inner
      when strip_ns src_inner = strip_ns dst_inner ->
      (* shared_ptr<S> → shared_ptr<T> where the pointee types are identical
         (they differ only in a [Tnamespace] rendering wrapper).  The pointer is
         already the right type, and the pointee is immutable, so forward the
         existing pointer (a refcount bump / move) instead of dereferencing and
         re-[make_shared]ing a fresh, independent copy of the whole node. *)
      expr
    | Tshared_ptr _src_inner, Tshared_ptr dst_inner ->
      (* shared_ptr<S> → shared_ptr<T>: null-check, then allocate the pointee
         read at [T].  Handing the pointee straight to [make_shared] would ask
         [T] to be constructible from [S], which is only one of the ways a
         value crosses instantiations -- a [std::pair] is read component by
         component instead -- so ask the helper for the pointee and allocate
         what it gives back. *)
      require_header "memory";
      naming_expr ~lambda_ty:dst_ty ~body:(fun x ->
        CPPcond
          ( x,
            mk_call
              (CPPalloc (Alloc_heap, dst_inner))
              [CPPconvert (dst_inner, CPPderef x)],
            CPPnullptr ))
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
      else Cpp_erasure.converting_ctor orig_dst_ty [derefed]
    | _, Tshared_ptr inner ->
      mk_call (CPPalloc (Alloc_heap, inner)) [expr]
    | Tglob (g1, _src_ts, _), Tglob (g2, _dst_ts, _)
      when GlobRef.CanOrd.equal g1 g2 && _src_ts <> _dst_ts
           && not (Table.is_inline_custom g1) ->
      (* Same type at different arguments.  A converting constructor is the
         usual way across, but not every type has one -- [std::pair]'s asks
         each component to be constructible from the other's, and an erased
         component has to be cast rather than constructed -- so ask the helper,
         which uses the constructor where there is one and takes the value
         apart where there is not. *)
      CPPconvert (orig_dst_ty, expr)
    (* A function at another result type: [crane_convert] reads what it
       returns. *)
    | Tfun (src_dom, _), Tfun (dst_dom, _)
      when List.length src_dom = List.length dst_dom ->
      CPPconvert (orig_dst_ty, expr)
    | ( (Tvar (Tv_index (_, Some _) | Tv_named _) | Tapply (Tvar (Tv_index (_, Some _) | Tv_named _), _)),
        (Tvar (Tv_index (_, Some _) | Tv_named _) | Tapply (Tvar (Tv_index (_, Some _) | Tv_named _), _)) ) ->
      (* Type-variable-to-type-variable conversion in converting constructors
         -- a family's field [E X] is one too, written [E] once the family is
         a plain parameter.
         A plain converting constructor [A(field)] is wrong here: at runtime
         [U] may be [std::any], and [pair<K,V>] has no constructor from one --
         nor from [pair<any,any>], which is how a pair's components are boxed
         one at a time.  Dispatch at compile time instead. *)
      require_header "any";
      if not (is_access_path expr) then
        Cpp_erasure.converting_ctor orig_dst_ty [expr]
      else begin
        (* Which way [U] is read at [A] -- unboxed, converted, or taken apart
           component by component -- cannot be decided until C++ substitutes
           [U], and [crane_convert] is exactly that decision, so ask it rather
           than restate a part of it here.  The one question left is whether
           there is any route at all: where there is none the field belongs to
           a constructor this instantiation never holds. *)
        let dst = qualify_inductives ~skip orig_dst_ty in
        mk_iife (Some dst)
          [ Sif_constexpr
              ( Tt_convertible (dst, Tref (Lvalue, Tconst src_ty)),
                [Sreturn (Some (CPPconvert (dst, expr)))],
                (* [U] is neither a box nor anything else [A] can be read
                   from.  A converting constructor converts every field of
                   every constructor, but only the constructor the source
                   actually holds is reached; the rest are converted only
                   because C++ compiles both sides of an [if].  Two
                   instantiations that agree on the field being carried can
                   disagree completely on one that is not, so the unreachable
                   side gets the throw rather than a conversion no one asked
                   for. *)
                [Sthrow inactive_field_message] ) ]
      end
    | (_, dst) when (let strip_ns = function Tnamespace (_, t) -> t | t -> t in
                     match strip_ns dst with
                     | Tglob (g, [elem_ty], _) ->
                       Ml_type_util.is_custom_list_global g
                       && elem_ty <> Tany && elem_ty <> Tauto
                     | _ -> false) ->
      let strip_ns = function Tnamespace (_, t) -> t | t -> t in
      (match strip_ns dst with
       | Tglob (g, [_], _) ->
         (match src_ty with
           | Tany -> Cpp_erasure.unbox (Tglob (g, [Tany], [])) expr
           | _ -> expr)
       | _ -> expr)
    | _ ->
      (* Type variables or fully concrete different types: converting
         constructor.  Type variables are always bare (never shared_ptr)
         because nested self-references are wrapped at the field level. *)
      Cpp_erasure.converting_ctor orig_dst_ty [expr]

(** Build a [CPPfun_call] for [ITree<R>::ret(...)].
    When [r_cpp] is [Tvoid], generates [ITree<void>::ret()]. *)
let mk_itree_ret (r_cpp : cpp_type) (args : cpp_expr list) : cpp_expr =
  let itree_ty = Tid_external ("ITree", [r_cpp]) in
  mk_call (CPPqualified_t (itree_ty, Id.of_string "ret")) args

(** Build [ITree<R>::ret(v)], or [ITree<void>::ret()] where there is no value
    to carry.  [r_cpp] is the C++ result type, [r_ml] the ML one, [v] the value.

    Only a type extracted as C++ [void] is valueless.  Rocq's [unit] is not: it
    has an inhabitant, spelled [std::monostate], and a tree carrying it is a
    tree like any other.  Spelling it [ITree<void>] instead loses the
    distinction between a computation that yields nothing and one that yields
    the trivial thing, and the two then meet in one match. *)
let mk_itree_ret_for_value r_cpp r_ml v =
  if r_cpp = Tvoid || ml_type_is_void r_ml then mk_itree_ret Tvoid []
  else mk_itree_ret r_cpp [v]

(** Reify a monadic parameter type for ITree extraction.

    In reified mode, the C++ type for a monadic parameter [itree E R] after
    monad erasure is just [R].  This function wraps it back into
    [shared_ptr<ITree<R>>] so the tree can be passed as a first-class value.
    Does nothing in sequential mode or when [ml_ty] is not monadic. *)
let reify_monadic_param_type ml_ty cpp_ty =
  if is_monadic_ml_type ml_ty && (!tctx).itree_mode = Reified then begin
    Table.require_itree_header ();
    let r_ty =
      match cpp_ty with
      | Tglob (_, _ :: r :: _, _) -> r
      | t -> t
    in
    mk_itree_type r_ty
  end
  else cpp_ty

(** Check whether an ML expression already produces a reified monadic value
    (a [shared_ptr<ITree<R>>]).  Extends {!is_reified_monadic_var} to also
    cover [MLapp(MLrel f, args)] where [f] is a local function whose return
    type is monadic.  Such calls already return a tree, so wrapping in
    [ITree::ret()] would incorrectly double-wrap.

    Also covers a constructor of the monad type itself: [ITree]'s own node
    constructors are extracted to expressions that build a tree, so a term
    like [go (RetF x)] is already the tree and must not be wrapped again.

    A call to a global counts too, but only where Crane itself wrote the
    callee: a global with a mapping (e.g. [print_endline]) stands for a direct
    C++ expression, which genuinely needs the wrap, and a void-ified one
    returns nothing at all in C++ however monadic its Rocq type reads.  The
    exception is a mapping whose result is a {e reified} monad: that monad's
    values are trees, so its mappings -- [itree_trigger], [itree_ret] -- are
    spelled as expressions that build one, and wrapping would double it. *)
let rec is_reified_monadic_expr ml_expr =
  (* The result of applying [n] arguments to something of ML type [ty].  A
     dummy domain is an erased type parameter, which the term does not pass, so
     it is stepped over without spending an argument. *)
  let rec ml_result_after n ty =
    match Ml_type_util.resolve_tmeta ty with
    | Miniml.Tarr (dom, res) when (match Ml_type_util.resolve_tmeta dom with
            | Miniml.Tdummy _ -> true
            | _ -> false) ->
      ml_result_after n res
    | Miniml.Tarr (_, res) when n > 0 -> ml_result_after (n - 1) res
    | t -> t
  in
  (* A callee generic over a monad class returns [m (list B)]: a [Tapp] headed
     by the class's carrier variable, which no test against a concrete monad
     glob can recognise.  The monad is nonetheless known {e here} -- the call
     supplies the dictionary, and the instance the emitter writes for it is
     [Monad_itree<std::any>] -- so the question is put to the call site rather
     than to the callee's type, which is the only side that does not know the
     answer.

     The dictionary is identified by the domain it fills: a class applied to
     the very carrier the result is headed by.  An instance passed for another
     class, or for another carrier, says nothing about this result. *)
  let instance_carrier_is_reified g =
    match Option.map ml_codomain (find_type_opt g) with
    | Some t -> (
      match Ml_type_util.resolve_tmeta t with
      | Miniml.Tglob (_, targs, _) ->
        List.exists
          (fun t ->
            match Ml_type_util.resolve_tmeta t with
            | Miniml.Tglob (m, _, _) -> Table.is_monad m && is_monad_reified m
            | _ -> false )
          targs
      | _ -> false )
    | None -> false
  in
  let reified_via_dictionary ty args head =
    (* A carrier of arrow kind stands in its class's argument list as the
       [Tapp] it would be if applied, with nothing applied to it yet. *)
    let names_carrier t =
      match Ml_type_util.resolve_tmeta t with
      | Miniml.Tvar (_, i) | Miniml.Tapp (i, _) -> Int.equal i head
      | _ -> false
    in
    let rec go doms args =
      match (doms, args) with
      | dom :: doms', _ when Mlutil.isTdummy dom -> go doms' args
      | dom :: doms', a :: args' ->
        let fills_this_carrier =
          match Ml_type_util.resolve_tmeta dom with
          | Miniml.Tglob (_, targs, _) -> List.exists names_carrier targs
          | _ -> false
        in
        ( match a with
        | Miniml.MLglob (g, _) when fills_this_carrier ->
          instance_carrier_is_reified g
        | _ -> go doms' args' )
      | _ -> false
    in
    go (Ml_type_util.ml_domains ty) args
  in
  (* A local's type may say nothing -- a rank-2 [D ~> itree E] parameter is
     erased, so what it returns is a type variable -- and then the Rocq
     typing of the position is the only statement there is: an argument at a
     monadic parameter has that monadic type, and every value of a reified
     monad is a tree.  Only a type that says something else is evidence of a
     plain value. *)
  let says_monadic ty =
    is_monadic_ml_type ty
    ||
    match Ml_type_util.resolve_tmeta ty with
    | Miniml.Tvar _ | Miniml.Tunknown | Miniml.Tmeta {contents = None} -> true
    | _ -> false
  in
  match ml_expr with
  (* A coercion changes the type a value is read at, not whether it is a
     tree: the question is asked of what is under it. *)
  | MLmagic (_, e) -> is_reified_monadic_expr e
  | MLapp (MLmagic (_, f), args) -> is_reified_monadic_expr (MLapp (f, args))
  | MLrel i ->
    (match get_env_type_opt i with Some ty -> says_monadic ty | None -> false)
  | MLapp (MLrel i, args) ->
    (match get_env_type_opt i with
     | Some ty -> says_monadic (ml_result_after (List.length args) ty)
     | None -> false)
  (* A global of monadic type is already a tree whether or not it is applied:
     a zero-arity constant like [get : itree E nat] is the same value that its
     applied form would be, and wrapping it in [ret] builds a tree of trees. *)
  | MLglob (r, _) | MLapp (MLglob (r, _), _) ->
    let nargs = match ml_expr with MLapp (_, args) -> List.length args | _ -> 0 in
    (not (is_void_ified_ref r))
    && ( match find_type_opt r with
       | Some ty ->
         let res = ml_result_after nargs ty in
         ( match Ml_type_util.resolve_tmeta res with
         | Miniml.Tapp (head, _) ->
           let args = match ml_expr with MLapp (_, args) -> args | _ -> [] in
           reified_via_dictionary ty args head
         | _ ->
           is_monadic_ml_type res
           && ( (not (Table.is_inline_custom r))
              || match Ml_type_util.resolve_tmeta res with
                 | Miniml.Tglob (m, _, _) -> is_monad_reified m
                 | _ -> false ) )
       | None -> false )
  | MLcons (ty, _, _) -> is_monadic_ml_type ty
  | _ -> false

(** Make the lambdas a function returns closures.  A returned lambda
    outlives the frame it was written in, so it must hold copies ([\[=\]])
    rather than references into that frame.

    A lambda invoked where it is written is not returned, whatever its result
    is: it stays [Immediate], and only what {e it} returns is made a
    closure. *)
let return_captures_by_value stmts =
  let rec by_value l =
    {(map_lambda stmt Fun.id l) with cl_capture = Closure}
  and expr = function
    | CPPlambda l -> CPPlambda (by_value l)
    | CPPfun_call (res, CPPlambda l, args) ->
      CPPfun_call (res, CPPlambda (map_lambda stmt Fun.id l), map_args expr args)
    | CPPfun_call (res, f, args) ->
      CPPfun_call (res, expr f, map_args expr args)
    | CPPderef e -> CPPderef (expr e)
    | CPPmove e -> CPPmove (expr e)
    | CPPforward (ty, e) -> CPPforward (ty, expr e)
    | CPPstruct (id, tys, es) -> CPPstruct (id, tys, List.map expr es)
    | CPPstruct_id (id, tys, es) -> CPPstruct_id (id, tys, List.map expr es)
    | CPPstructmk (id, tys, es) -> CPPstructmk (id, tys, List.map expr es)
    | CPPshared_ptr_ctor (ty, e) -> CPPshared_ptr_ctor (ty, expr e)
    | CPPbinop (op, a, b) -> CPPbinop (op, expr a, expr b)
    | CPPunop (op, e) -> CPPunop (op, expr e)
    | CPPaccess (Adot, e, id) -> CPPaccess (Adot, expr e, id)
    | CPPscope (e, id, []) -> CPPscope (expr e, id, [])
    | CPPget (e, id) -> CPPget (expr e, id)
    | CPPget' (e, id, ty) -> CPPget' (expr e, id, ty)
    | CPPaccess_call (Aarrow, e, id, args) ->
      CPPaccess_call (Aarrow, expr e, id, List.map expr args)
    | CPPany_cast (ty, e) -> Cpp_erasure.unbox ty (expr e)
    | e -> e
  and stmt = function
    | Sreturn (Some e) -> Sreturn (Some (expr e))
    | Sexpr e -> Sexpr (expr e)
    | Sasgn (_, _, _) as s -> s
    | Sassign_expr (_, _) as s -> s
    | Sif (c, t, f) -> Sif (expr c, List.map stmt t, List.map stmt f)
    | Sswitch (scrut, ind, branches, default) ->
      Sswitch
        ( expr scrut,
          ind,
          List.map (fun (id, body) -> (id, List.map stmt body)) branches,
          Option.map (List.map stmt) default )
    | Smatch (scrut, branches, default) ->
      Smatch
        ( { scrut with sc_expr = expr scrut.sc_expr },
          List.map
            (fun br -> { br with smb_body = List.map stmt br.smb_body })
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
      | Sreturn (Some (CPPlambda ({ cl_capture = Immediate; _ } as l))) ->
        Sreturn (Some (CPPlambda { l with cl_capture = Closure }))
      | Sreturn (Some e) -> Sreturn (Some (expr e))
      | s -> s )
    stmts

(** Whether evaluating [e] is only building a value: no call is made, so it
    cannot fail to terminate.  A lambda is a value; so is a constructor of
    values.  A global is a value unless naming it calls it -- a cofixpoint
    or a monadic definition is emitted as a nullary function. *)
let rec ml_is_value = function
  | MLrel _ | MLlam _ | MLdummy _ | MLuint _ | MLfloat _ | MLstring _ -> true
  | MLglob (r, _) ->
    not
      ( Table.is_cofixpoint r || Table.is_throwing_value r
      || match find_type_opt r with
         | Some t -> is_monadic_ml_type t
         | None -> false )
  | MLcons (_, _, args) | MLtuple args -> List.for_all ml_is_value args
  | MLmagic (_, e) -> ml_is_value e
  | _ -> false

(** Whether [body] calls [r] somewhere a suspension does not reach: outside
    every lambda and every coinductive constructor.  Rocq's guard condition
    rules this out syntactically, but it checks guardedness up to unfolding
    definitions, so a corecursive call may sit under a function that only
    builds the constructor once unfolded.  A body like that is suspended
    whole, as every coinductive-returning body used to be. *)
let calls_eagerly r body =
  let exception Found in
  let rec walk e =
    match e with
    | MLglob (r', _) when globref_equal r r' -> raise Found
    | MLlam _ -> ()
    | MLcons (ty, _, _) when Table.is_coinductive_type ty -> ()
    | _ -> Mlutil.ast_iter walk e
  in
  try walk body; false with Found -> true

(** [suspend_ctor ty call] is the coinductive constructor application [call]
    of type [ty], suspended: [ty::lazy_([=]() -> ty { return call; })].

    The only suspension point a coinductive value has, as in OCaml's
    extraction: everything else in a body runs where it is written.  It is
    taken only where the constructor's arguments compute.  Rocq's guard
    condition puts every corecursive call under a constructor, so a
    constructor whose arguments are values holds no call to delay, and is
    built directly. *)
let suspend_ctor ty call =
  CPPfun_call
    ( Minicpp.call_sig ~yields:ty ~nargs:1 (),
      CPPqualified_t (ty, Id.of_string "lazy_"),
      of_reversed
        [mk_lambda [] (Some ty) [Sreturn (Some call)] ~capture:Closure] )

(** Run [f] in a fresh escape-analysis scope, restoring the enclosing one
    afterwards.  Escape analysis runs at several nesting levels (lambdas,
    let-in expressions, top-level functions) and each level has its own set of
    safe bindings. *)
let with_escape_analysis f =
  (* Prevent void optimization from leaking into IIFE/lambda bodies: when the
     outer function returns void, gen_stmts generates bare 'return;' for tt,
     but IIFE bodies return their own type (e.g. monostate), not void. *)
  let inner_return_type =
    match (!tctx).current_cpp_return_type with
    | Some Tvoid -> None
    | rt -> rt
  in
  (* A lambda body is not part of the constructor expression that encloses it.
     Both flags make an unresolvable type variable erase to [std::any], which
     is right for a constructor's own arguments and wrong for the body of a
     lambda that merely happens to be one -- the lambda has its own binders
     and its own slots. *)
  with_scope @@ fun () ->
  tctx :=
    { !tctx with
      current_letin_depth = 0;
      move_dead_after = Escape.IntSet.empty;
      move_owned_vars = Escape.IntSet.empty;
      move_n_params = 0;
      match_param_counter = 0;
      cs_counter = 0;
      in_constructor_expr = false;
      current_cpp_return_type = inner_return_type };
  f ()

(** Bracket for an IIFE that stands in for a SUB-expression (a let-in, a
    fixpoint, or a record destructure in argument position).  The lambda
    returns THIS expression's value, not the enclosing function's, so the
    ambient return type must be re-based on the expression's own expected type
    ([None] wherever the context imposes none).  Without this the enclosing
    function's return type leaks into the IIFE body and its tail expression is
    cast to it — e.g. [any_cast<uint64_t>] on an erased record field that the
    caller then projects with [.first.first]. *)
let with_iife_return_type expected_ty f = with_cpp_return_type expected_ty f

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
    @param exclude_owned_set  Indices to REMOVE from the owned set after
      shifting.  Used for the variables a local fixpoint captures: the
      continuation still reads them through the fixpoint's closure, so moving
      out of them would leave the closure holding a moved-from value.
    @param exclude_owned  Optional de Bruijn index to REMOVE from the owned set
      after shifting.  Used for match scrutinees: after shifting by [n], the
      scrutinee's outer index [db] becomes [db + n].  Excluding it prevents
      [std::move(scrutinee)] from being emitted inside the branch while
      pattern-variable structured bindings ([const auto& [d_a0, d_a1] = ...])
      still hold const references into it — which would cause use-after-move. *)
let with_shifted_move_tracking n ?(clear_dead = false) ?add_owned
    ?(add_owned_set = Escape.IntSet.empty)
    ?(exclude_owned_set = Escape.IntSet.empty) ?exclude_owned f =
  let saved_owned = (!tctx).move_owned_vars in
  let saved_dead = (!tctx).move_dead_after in
  tctx :=
    { !tctx with
      move_owned_vars =
          Escape.IntSet.diff
            (Escape.IntSet.map (fun i -> i + n) (!tctx).move_owned_vars)
            exclude_owned_set };
  ( match add_owned with
  | Some idx ->
    tctx :=
      { !tctx with
        move_owned_vars = Escape.IntSet.add idx (!tctx).move_owned_vars }
  | None -> () );
  tctx :=
    { !tctx with
      move_owned_vars =
          Escape.IntSet.union (!tctx).move_owned_vars add_owned_set };
  ( match exclude_owned with
  | Some idx ->
    tctx :=
      { !tctx with
        move_owned_vars = Escape.IntSet.remove idx (!tctx).move_owned_vars }
  | None -> () );
  tctx :=
    { !tctx with
      move_dead_after =
          ( if clear_dead then Escape.IntSet.empty
            else Escape.IntSet.map (fun i -> i + n) (!tctx).move_dead_after ) };
  Fun.protect
    ~finally:(fun () ->
      tctx := { !tctx with move_owned_vars = saved_owned };
      tctx := { !tctx with move_dead_after = saved_dead } )
    f

(* ============================================================================
   Shared helpers for method generation (used by gen_ind_header_v2 and
   gen_record_methods)
   ============================================================================ *)

(** Re-export [IntSet] from [Escape] for local use in type variable collection. *)
module IntSet = Escape.IntSet

(** Collect all Tvar indices from an ml_type. Used to find type variables beyond
    those of the containing inductive/record. *)
let collect_tvars_set acc ty = IntSet.union acc (Mlutil.ml_tvars ty)

(** Convert an IntSet of type variable indices back to a list, wrapping
    [collect_tvars_set]. Used to collect all Tvar indices from an ml_type. *)
let collect_tvars acc ty =
  IntSet.elements (collect_tvars_set (IntSet.of_list acc) ty)

(** Whether [r] declares a C++ template parameter for the type argument at
    (1-based) position [i].

    A type argument standing for a higher-kinded class parameter is not one:
    it is the instance's associated type, and it is always erased, which would
    otherwise make [filter_erased_type_args] drop the real type arguments
    alongside it.  Neither is a variable that does not occur in [r]'s type at
    all ([mbind]'s [B] only ever appears under the carrier [M B]).

    Asked both of a call's type arguments and of an instance's, which are the
    same list read at the same positions. *)
let keeps_type_arg_position r =
  match find_type_opt r with
  | None -> fun _ -> true
  | Some ty -> (
    match List.map (fun p -> p.htp_tvar) (hkt_tvar_positions_of_type ty) with
    | [] -> fun _ -> true
    | hkt ->
      let occurring = collect_tvars_set IntSet.empty ty in
      fun i ->
        (not (List.mem i hkt))
        && (IntSet.is_empty occurring || IntSet.mem i occurring) )

(** [ty] with every family variable written applied taken back to the bare
    variable: a plain family is declared without its index. *)
let deapply_families =
  map_cpp_type (function Tapply ((Tvar _ as v), _) -> v | t -> t)

(** The 1-based positions among [1..n] that {!keeps_type_arg_position} keeps
    for [r]: the written type arguments of a call to [r]. *)
let kept_type_arg_positions r n =
  List.filter (keeps_type_arg_position r) (List.init n (fun i -> i + 1))

(** [r]'s type arguments, less those {!keeps_type_arg_position} rules out. *)
let kept_type_args r ts =
  let keep = keeps_type_arg_position r in
  List.filteri (fun i _ -> keep (i + 1)) ts

(** The number of type parameters [g] is written with in C++: the promoted
    variables it leads with ({!ind_promoted_type_args}), then an inductive's
    parameters or the variables of a type alias's body.  A family alias under
    a [Params] section is [BotE<ptr, X>], and [BotE<ptr>] is one short. *)
let written_arity g =
  let promoted = List.length (Table.promoted_type_params g) in
  match g with
  | GlobRef.IndRef (kn, _) ->
    Option.map (( + ) promoted) (Table.get_ind_num_param_vars_opt kn)
  | GlobRef.ConstRef kn ->
    Option.map
      (fun body -> promoted + Mlutil.type_maxvar body)
      (Table.lookup_typedef_unchecked kn)
  | _ -> None

(** Whether [t] is a type written with fewer arguments than it has
    parameters -- all a type-level lambda leaves once extraction writes it as
    its head ([fun T => list (box T)] as a bare [list]), or an alias carrier
    ([texp]) passed as its name.  At a plain position that is no type at
    all. *)
let under_applied_ind t =
  match t with
  | Tglob (g, args, _) | Tnamespace (_, Tglob (g, args, _)) -> (
    match written_arity g with
    | Some n -> List.length args < n
    | None -> false )
  | _ -> false

(** [t], a type {!under_applied_ind} says is short of arguments, applied at
    [std::any] for each one missing: a family at an erased index. *)
let saturate_at_any t =
  let pad g args =
    match written_arity g with
    | Some n -> args @ List.init (n - List.length args) (fun _ -> Tany)
    | None -> args
  in
  match t with
  | Tglob (g, args, es) -> Tglob (g, pad g args, es)
  | Tnamespace (ns, Tglob (g, args, es)) -> Tnamespace (ns, Tglob (g, pad g args, es))
  | t -> t

(** [ts], an explicit argument list for [r] read from the front, with a
    plain position given a type: a family recovered as its bare head --
    [box] for [TFunctor_list'], whose [F] the declaration writes plain -- is
    that family at its erased index, [box<std::any>]. *)
let types_at_plain_positions r ts =
  match find_type_opt r with
  | None -> ts
  | Some ml_ty ->
    let hk = Ml_type_util.higher_kinded_ml_tvars [ml_ty] in
    let n = IntSet.fold max (collect_tvars_set IntSet.empty ml_ty) 0 in
    let kept = kept_type_arg_positions r n in
    List.mapi
      (fun k t ->
        match List.nth_opt kept k with
        | Some i when not (IntSet.mem i hk) -> (
          (* A carrier abstraction is applied at the erased index; a bare
             head has its missing arguments erased. *)
          let t =
            match t with
            | Ttyctor body -> (
              match Minicpp.tapply t [Tany] with Tapply _ -> body | applied -> applied )
            | t -> t
          in
          if under_applied_ind t then saturate_at_any t else t )
        | _ -> t )
      ts

(** [r]'s type arguments, with those standing for a parameter of kind
    [Type -> Type] spelled as the bare template names they are.

    Such a parameter is declared [template <typename> class], so an explicit
    argument for it is a template, not a type: [iter<_tcI0::template F, R>].
    Written as a type it reads [typename _tcI0::F], which names the alias's
    result rather than the alias, and C++ rejects it outright.  Which
    positions those are is read off [r]'s own type -- the same question its
    declaration asked of it.

    [ts] is the list {!kept_type_args} produced, so it is indexed by kept
    position, not by de Bruijn index: the variables a class resolved away are
    no longer in it.  The correspondence is rebuilt from the same predicate
    that dropped them, and a list of some other length -- one a later pass
    filtered or padded -- is left alone rather than guessed at. *)
let hkt_spelled_type_args r ts =
  match find_type_opt r with
  | None -> ts
  | Some ml_ty ->
    (* Higher-kinded as the declaration has it: an event family is applied
       everywhere it occurs, and is still declared a plain [typename] --
       whose argument is the family's own type, promoted arguments and all,
       and not its bare template name. *)
    let hk = Ml_type_util.higher_kinded_ml_tvars [ml_ty] in
    (* Only a higher-kinded variable is relaxed out of a head: a family is a
       plain parameter the declaration keeps. *)
    let relaxed = IntSet.inter (Ml_type_util.relaxed_applied_ml_tvars ml_ty) hk in
    let ts = types_at_plain_positions r ts in
    if IntSet.is_empty hk && IntSet.is_empty relaxed then ts
    else
      let n = IntSet.fold max (collect_tvars_set IntSet.empty ml_ty) 0 in
      let keep = keeps_type_arg_position r in
      let kept = List.filter keep (List.init n (fun i -> i + 1)) in
      if List.length kept <> List.length ts then ts
      else
        List.map2
          (fun i t ->
            (* The declaration relaxed this one out of its head: what is left
               at the position is a phantom defaulted to [void], and the
               application it stood for is deduced from the argument. *)
            if IntSet.mem i relaxed then Minicpp.Tvoid
            else
              match t with
              | Minicpp.Ttyctor _ -> t
              | _ when IntSet.mem i hk -> Minicpp.Ttyctor t
              | _ -> t )
          kept ts

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
  | MLmagic (_, a) -> collect_tvars_ast acc a
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
  | MLglob (r, _) -> Table.is_throwing_value r
  | MLlam (_, _, body) -> ast_may_throw body
  | MLletin (_, _, a, b) -> ast_may_throw a || ast_may_throw b
  | MLcons (_, _, args) -> List.exists ast_may_throw args
  | MLcase (_, e, brs) ->
    ast_may_throw e
    || Array.exists (fun (_, _, _, body) -> ast_may_throw body) brs
  | MLfix (_, _, funs, _) -> Array.exists ast_may_throw funs
  | MLapp (f, args) -> ast_may_throw f || List.exists ast_may_throw args
  | MLmagic (_, a) -> ast_may_throw a
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
    | (Miniml.Tvar (_, i)), _ when not (has_tvar t2) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t2)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | _, (Miniml.Tvar (_, i)) when not (has_tvar t1) ->
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
    try_mgu (Miniml.Tmeta m) (Miniml.Tvar (Schematic, idx))
  | Miniml.Tmeta {contents = Some t} -> resolve_type_metas ~next_tvar t
  | Miniml.Tarr (t1, t2) ->
    resolve_type_metas ~next_tvar t1;
    resolve_type_metas ~next_tvar t2
  | Miniml.Tglob (_, args, _) -> List.iter (resolve_type_metas ~next_tvar) args
  | _ -> ()

(** The type a term builds in tail position, where its own annotations say so.

    Only a constructor application answers.  [MLcons] carries the inductive it
    builds (see the typing note on {!Miniml.ml_ast}), so it is the one node
    that knows its type without reconstruction; a recursive call, by
    definition, says nothing the fixpoint's own type does not already. *)
let rec tail_result_type ~app_result = function
  | MLlam (_, _, b) | MLletin (_, _, _, b) | MLmagic (_, b) ->
    tail_result_type ~app_result b
  | MLcons (ty, _, _) -> Some ty
  | MLapp (f, args) -> app_result f args
  | MLcase (_, _, brs) ->
    Array.fold_left
      (fun acc (_, _, _, b) ->
        match acc with Some _ -> acc | None -> tail_result_type ~app_result b )
      None brs
  | _ -> None

(** Recover a fixpoint's return type from its body.

    An eliminator's motive is erased, so the fixpoint MiniML builds for
    [nat_rect] carries a type variable where its result type belongs -- one no
    parameter mentions and no caller supplies.  Lifted to a C++ template that
    becomes a template parameter nothing deduces, leaving the call site to
    guess: [_shifted_F<std::any>] against a body returning [Positive].

    The body knows.  Where the variable is undeducible -- absent from every
    parameter type -- and a tail position builds a constructor, that
    constructor's inductive is what the function returns, and substituting it
    makes the signature say so.

    A variable some parameter mentions is genuine polymorphism and is left
    alone.  So is one whose body builds nothing:
    [tests/regression/anon_lift_name_collision]'s [_count_F] returns [T1] from
    integer literals, and its call site supplies the argument. *)
let recover_fix_codomain ~app_result ((id, ty) : Id.t * ml_type)
    (body : ml_ast) : (Id.t * ml_type) * ml_ast =
  let dom, cod = Mlutil.type_decomp ty in
  match cod with
  | Miniml.Tmeta ({contents = None} as cell) -> (
    (* A hole, not a variable: the cell is shared with every annotation the
       body writes it into, so filling it {e is} the substitution. *)
    match tail_result_type ~app_result body with
    | Some t -> cell.Miniml.contents <- Some t; ((id, ty), body)
    | None -> ((id, ty), body) )
  | Miniml.Tvar (_, i)
    when (not (List.exists (fun t -> collect_tvars [] t |> List.mem i) dom))
         && tail_result_type ~app_result body <> None ->
    let subst = [(i, Option.get (tail_result_type ~app_result body))] in
    ( (id, subst_tvars_type subst ty),
      map_types_in_ast (subst_tvars_type subst) body )
  | _ -> ((id, ty), body)

(** Settle the types of a fixpoint's functions: recover each codomain from its
    body where erasure lost it, then mint [Tvar]s for the metas that remain.
    The order is the point -- a variable already standing for the result type
    is no longer asking what the body builds. *)
let resolve_fix_types ~app_result ~next_tvar ids funs =
  Array.iteri
    (fun i idty ->
      let idty, body = recover_fix_codomain ~app_result idty funs.(i) in
      ids.(i) <- idty;
      funs.(i) <- body )
    ids;
  Array.iter (fun (_, ty) -> resolve_type_metas ~next_tvar ty) ids

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
  | MLmagic (_, a) -> resolve_metas_in_ast resolve_metas a
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
    generic AST visitors for structural recursion.

    With [~keep_cast:true], an occurrence that already sits directly under an
    [any_cast] keeps that cast: only the variable underneath is substituted,
    and a top-level [any_cast] on [repl] is dropped.  Callers whose [repl] is
    an [any_cast] of [target] use this -- the cast already there was chosen by
    the code that built that use site and knows its runtime encoding, so
    nesting the two casts would throw [std::bad_any_cast].

    With [~extra_args], an occurrence in callee position also gains those
    arguments.  Lifting a local binding to a top-level function turns its free
    variables into trailing parameters, and every call has to grow to match;
    the list is given already reversed, as {!CPPfun_call} stores its
    arguments. *)
let rec local_var_subst_expr ?(keep_cast = false) ?(extra_args = [])
    (target : Id.t) (repl : cpp_expr) (e : cpp_expr) =
  let sub = local_var_subst_expr ~keep_cast ~extra_args target repl in
  match e with
  | CPPany_cast (ty, CPPvar id) when keep_cast && Id.equal id target ->
    Cpp_erasure.unbox ty
      (match repl with CPPany_cast (_, inner) -> inner | r -> r)
  | CPPfun_call (o, CPPvar id, args) when extra_args <> [] && Id.equal id target
    ->
    CPPfun_call
      (o, repl, of_reversed (extra_args @ List.map sub (to_reversed args)))
  | CPPvar id when Id.equal id target -> repl
  | _ ->
    map_expr
      sub
      (local_var_subst_stmt ~keep_cast ~extra_args target repl)
      Fun.id
      e

(** Statement-level counterpart of [local_var_subst_expr]: substitute
    [CPPvar target] with [repl] inside a single C++ statement. *)
and local_var_subst_stmt ?(keep_cast = false) ?(extra_args = [])
    (target : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt
    (local_var_subst_expr ~keep_cast ~extra_args target repl)
    (local_var_subst_stmt ~keep_cast ~extra_args target repl)
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

(** The reference under which an inner fixpoint named [fix_name], lifted out of
    the declaration currently being generated, is emitted.

    The identity is minted by {!Lifted.make} rather than assembled here, so that
    two helpers cannot become one by agreeing on a spelling; see [lifted.mli]. *)
let lifted_fix_ref (fix_name : Id.t) : GlobRef.t =
  Lifted.ref_of (Lifted.make ~origin:!Table.current_decl_ref ~binder:fix_name)

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
    | MLmagic (_, MLrel db) | MLrel db -> db = expected_db
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
    | MLmagic (_, e) -> walk depth e
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

(** The source-order indices of the parameters that a closure may hold on
    to: those named under a lambda the body does not apply on the spot, or
    anywhere when [suspended] -- the whole body is a thunk, as a function
    returning a coinductive is.

    A callable parameter that escapes this way is taken as a [crane::fn]
    rather than generalised to [F &&].  A deduced callable is the caller's
    closure type itself, and every closure that captures it copies it and all
    it captured; a [crane::fn] is converted once, at the call, and shared by
    every capture after that. *)
let escaping_params ~suspended n_params body =
  let escaping = Hashtbl.create 4 in
  let rec walk under depth e =
    match e with
    | MLrel db ->
      let i = n_params - db + depth in
      if under && db > depth && i >= 0 && i < n_params then
        Hashtbl.replace escaping i ()
    | MLapp ((MLlam _ as f), args) ->
      (* Applied where it is written: the binders the arguments fill run
         here, not later.  Any left over make a closure. *)
      let rec spine n depth = function
        | MLlam (_, _, b) when n > 0 -> spine (n - 1) (depth + 1) b
        | b -> walk under depth b
      in
      spine (List.length args) depth f;
      List.iter (walk under depth) args
    | MLlam (_, _, b) -> walk true (depth + 1) b
    | MLapp (f, args) ->
      walk under depth f;
      List.iter (walk under depth) args
    | MLletin (_, _, e1, e2) ->
      walk under depth e1;
      walk under (depth + 1) e2
    | MLcase (_, scrut, branches) ->
      walk under depth scrut;
      Array.iter
        (fun (ids, _, _, b) -> walk under (depth + List.length ids) b)
        branches
    | MLcons (_, _, args) | MLtuple args -> List.iter (walk under depth) args
    | MLfix (_, _, bodies, _) ->
      (* A local fixpoint is a closure over its free variables. *)
      let n = Array.length bodies in
      Array.iter (walk true (depth + n)) bodies
    | MLmagic (_, e) -> walk under depth e
    | MLparray (elts, def) ->
      Array.iter (walk under depth) elts;
      walk under depth def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _
     |MLstring _ -> ()
  in
  walk suspended 0 body;
  Hashtbl.fold (fun k () acc -> k :: acc) escaping []

(* Detect non-forwarded params in a local fixpoint body.  Self-references
   use MLrel: after collect_lams strips [n_params] lambda params, the fix
   binding for [fix_idx] in [n_fix] mutual funs is at
   db = [n_params + n_fix - fix_idx], shifted by binder depth. *)
let detect_non_forwarded_params_fix n_params n_fix fix_idx body =
  let base_self_db = n_params + n_fix - fix_idx in
  detect_non_forwarded_params_generic
    ~is_self_call:(fun depth f ->
      (* A coercion around the self-reference (extraction inserts one when the
         fixpoint's type was generalised) must not hide the recursive call. *)
      let rec strip = function MLmagic (_, e) -> strip e | e -> e in
      match strip f with
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
        | Tshared_ptr _ -> (id, Tref (Lvalue, Tconst cpp_ty))
        | _ -> (id, Tconst cpp_ty) )
      params
  in
  let unwrap_fun_ty = function
    | Tconst ((Tfun _ as f)) -> Some f
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
          (x, Tref (Forwarding, named_tvar (fun_tparam_id (n_params - j - 1))))
        | _ -> (x, ty) )
      cpp_params
  in
  let extra_temps = List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let all_temps_with_funs = base_temps @ extra_temps in
  (cpp_params, all_temps_with_funs)

(** [generalize_lambda_only_tparams temps params ret body] moves a lifted
    helper's undeducible type parameters into the lambda that is their only
    occurrence, returning the shortened head and the rewritten body.

    A parameter the helper's own signature does not mention cannot be deduced
    from a call.  When every occurrence it does have is the binder of a lambda
    the helper returns, the polymorphism belongs to that lambda rather than to
    the helper -- C++ spells that [auto], and the head is shorter by one.  A
    parameter occurring anywhere else is left where it is: [auto] is not a
    type one may write as a template argument.

    Sound only where call sites name no type argument of their own beyond a
    leading prefix they always name, since a positional explicit argument list
    would be renumbered by the drop. *)
let generalize_lambda_only_tparams temps params ret body =
  let candidates =
    List.filter
      (fun (tt, id) ->
        tt = TTtypename
        && (not (tvar_named id ret))
        && not (List.exists (fun (_, ty) -> tvar_named id ty) params) )
      temps
  in
  if candidates = [] then (temps, body)
  else
    (* Occurrences that are not a lambda binder, and so pin the variable
       down where it stands. *)
    let pinned = ref [] in
    let note ty =
      List.iter
        (fun (_, id) ->
          if tvar_named id ty && not (List.exists (Id.equal id) !pinned) then
            pinned := id :: !pinned )
        candidates;
      ty
    in
    let rec scan_e e =
      match e with
      | CPPlambda l ->
        CPPlambda
          { l with
            cl_ret = Option.map note l.cl_ret;
            cl_body = List.map scan_s l.cl_body }
      | _ -> map_expr scan_e scan_s note e
    and scan_s s = map_stmt scan_e scan_s note s in
    List.iter (fun s -> ignore (scan_s s)) body;
    let movable =
      List.filter (fun (_, id) -> not (List.exists (Id.equal id) !pinned)) candidates
    in
    if movable = [] then (temps, body)
    else
      let to_auto ty =
        match tvar_name ty with
        | Some n when List.exists (fun (_, id) -> Id.equal id n) movable -> Tauto
        | _ -> ty
      in
      let rec rw_e e =
        match e with
        | CPPlambda l ->
          CPPlambda
            { l with
              cl_params =
                of_reversed
                  (List.map
                     (fun (ty, id) -> (to_auto ty, id))
                     (to_reversed l.cl_params) );
              cl_body = List.map rw_s l.cl_body }
        | _ -> map_expr rw_e rw_s Fun.id e
      and rw_s s = map_stmt rw_e rw_s Fun.id s in
      ( List.filter
          (fun (_, id) -> not (List.exists (fun (_, m) -> Id.equal id m) movable))
          temps,
        List.map rw_s body )

(** The type variables a type spells out in a deducible position.  A
    function-typed parameter reaches C++ as an opaque template parameter [F0]
    rather than as a written-out signature, so a variable occurring only
    inside one -- the callback's own codomain, say -- is in no deducible
    context; every other parameter spells its type out. *)
let rec spelled_tvars_of ?(plain = fun _ -> false) acc = function
  | Miniml.Tvar (_, j) -> IntSet.add j acc
  (* A higher-kinded variable is written applied, and is spelled all the same:
     as a template name, or -- a family -- as the plain type it is.  A plain
     head's arguments are not written at all ([E A] is [T1]), so where
     [plain] says so they spell nothing. *)
  | Miniml.Tapp (j, l) ->
    let acc = IntSet.add j acc in
    if plain j then acc else List.fold_left (spelled_tvars_of ~plain) acc l
  | Miniml.Tarr (a, b) ->
    spelled_tvars_of ~plain (spelled_tvars_of ~plain acc a) b
  (* An inductive's indices are not written ([Tglob] conversion keeps its
     parameters only): [getE T] is the enum [GetE]. *)
  | Miniml.Tglob (r, l, _) ->
    let l =
      match r with
      | GlobRef.IndRef (kn, _) -> (
        match Table.get_ind_num_param_vars_opt kn with
        | Some n -> safe_firstn n l
        | None -> l )
      | _ -> l
    in
    (* Nor are the arguments a mapping's text does not place: [itree E R] is
       [std::shared_ptr<ITree<R>>], and [E] cannot be read off it. *)
    let l = List.filteri (fun i _ -> Ml_type_util.type_arg_is_written r i) l in
    List.fold_left (spelled_tvars_of ~plain) acc l
  | Miniml.Tmeta {contents = Some t} -> spelled_tvars_of ~plain acc t
  | _ -> acc

(** The variables [ml_ty]'s declaration takes as template names.

    {!Ml_type_util.higher_kinded_ml_tvars} less those the declaration only
    ever applies, in its parameters and nowhere else: each such application is
    relaxed there to a fresh deduced parameter
    ({!Gen_decls.relax_applied_param}), and the variable left a plain
    [typename] -- [fused_trigger]'s [e : F T] is declared [_P0 e], and [F]
    [typename T1 = void].  So its arguments are no more spelled than a plain
    family's, and its position takes a box like any other. *)
let declared_higher_kinded_tvars ml_ty =
  let relaxed j =
    let bare = ref false and applied = ref false in
    let rec scan t =
      match resolve_tmeta t with
      | Miniml.Tvar (_, j') when j' = j -> bare := true
      | Miniml.Tapp (j', l) ->
        if j' = j then applied := true;
        List.iter scan l
      | Miniml.Tarr (a, b) -> scan a; scan b
      | Miniml.Tglob (_, l, _) -> List.iter scan l
      | _ -> ()
    in
    List.iter
      (fun d ->
        match expand_ml_fun_alias d with Miniml.Tarr _ -> () | d -> scan d )
      (ml_domains ml_ty);
    !applied && (not !bare)
    && not (IntSet.mem j (collect_tvars_set IntSet.empty (ml_return_type ml_ty)))
  in
  IntSet.filter (fun j -> not (relaxed j))
    (Ml_type_util.higher_kinded_ml_tvars [ml_ty])

(** The type variables of [id] a C++ compiler could read off the call's value
    arguments. *)
let deducible_tvars_of_glob id =
  match find_type_opt id with
  | None -> None
  | Some ml_ty_orig ->
    let hk = declared_higher_kinded_tvars ml_ty_orig in
    let plain j = not (IntSet.mem j hk) in
    Some
      (List.fold_left
         (fun acc d ->
           (* A definitional class is an alias for a function type -- [Id_ C
              obj] -- and an argument there is a callable just the same. *)
           match expand_ml_fun_alias d with
           | Miniml.Tarr _ -> acc
           | _ -> spelled_tvars_of ~plain acc d )
         IntSet.empty
         (List.map resolve_tmeta (ml_domains ml_ty_orig)) )

(** Infer the ML type of a body expression from its structure, or [None] where
    the structure does not say.

    This reads a type off a typed AST -- [MLcons] and [MLcase] carry theirs,
    and a global's is in the table -- rather than guessing one back out of an
    untyped C++ expression, which is what {!Loopify.infer_saved_type} used to
    do.  Its answer annotates a [CPPlambda]'s return type, so the frame a
    loopified call builds is typed instead of falling back on
    [decltype(lambda)].

    Instantiation goes through {!Mlutil.type_subst_list}, the one substituter:
    a second one here would be a second oracle, free to disagree. *)
let rec infer_ml_body_type (a : ml_ast) : ml_type option =
  match a with
  | MLapp (MLglob (r, tys), args) ->
    ( match find_type_opt r with
    | Some ty ->
      (* Instantiate type schema variables with actual type arguments -- the
         ones the call site carries, or, where it carries none, the ones its
         arguments imply. *)
      let tys =
        if tys <> [] then tys
        else
          tvar_instantiation ty
            (List.filter (function MLdummy _ -> false | _ -> true) args)
      in
      let ty = match tys with
        | [] -> ty
        | _ -> Mlutil.type_subst_list tys ty
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
  | MLmagic (_, e) -> infer_ml_body_type e
  | _ -> None

(** [tvar_instantiation callee_ty args] is the callee's type-variable
    instantiation, read off the arguments' own ML types.

    A call site does not always carry its type arguments: when they were
    erased, the [MLglob]'s list is empty and the callee's schema stays
    uninstantiated, so a codomain like [projT2]'s reads as a bare [Tvar] and
    nothing downstream can tell whether it erases.  The arguments still pin
    the variables down -- matching the declared domain against the type each
    argument actually has recovers them.

    The result is indexed the way {!Mlutil.type_subst_list} expects: position
    [i] instantiates [Tvar (_, i + 1)].  A variable no argument mentions keeps
    itself, so substituting leaves it alone. *)
and tvar_instantiation_found
    ?(in_scope = false)
    ?(constructors = false)
    ?result
    callee_ty
    args =
  (* A binder's type is not on the [MLrel] that names it; it was written down
     where it was bound, which is what {!Translation_state.env_types} keeps.
     Only a caller generating code {e inside} that scope may read it, which is
     why it is asked for rather than assumed. *)
  let arg_ml_ty a =
    match infer_ml_body_type a with
    | Some _ as t -> t
    | None -> (
      match a with
      | MLrel i when in_scope ->
        Option.map snd (List.nth_opt (!tctx).env_types (i - 1))
      | _ -> None )
  in
  let found = Hashtbl.create 7 in
  (* The first binding stands, unless a later one is free of variables where
     it was not: a dictionary's own type binds a carrier at its instance's
     variables ([itree (E (sum _ _))]), and the handler argument that follows
     says [itree TopE]. *)
  let bind k t =
    let open_ t = not (IntSet.is_empty (collect_tvars_set IntSet.empty t)) in
    match Hashtbl.find_opt found k with
    | None -> Hashtbl.replace found k t
    | Some old when open_ old && not (open_ t) -> Hashtbl.replace found k t
    | Some _ -> ()
  in
  let rec unify formal actual =
    match (resolve_tmeta formal, resolve_tmeta actual) with
    | Miniml.Tvar (_, i), a -> bind i a
    (* A definitional class is the function type it abbreviates: [Case obj C]
       met by the eta-expanded dictionary lambda that fills it. *)
    | (Miniml.Tglob (GlobRef.ConstRef _, _, _) as f), (Miniml.Tarr _ as a)
      when (match expand_ml_fun_alias f with Miniml.Tarr _ -> true | _ -> false) ->
      unify (expand_ml_fun_alias f) a
    | Miniml.Tglob (g1, a1, _), Miniml.Tglob (g2, a2, _)
      when GlobRef.CanOrd.equal g1 g2 && List.length a1 = List.length a2 ->
      List.iter2 unify a1 a2
    (* Where both sides open with type abstractions, they may abstract
       different numbers of them -- [E ~> M]'s one against a handler written
       [fun T => intr], itself abstracting its own [T] -- and the value
       arguments align only past all of them.  Only where both do: a formal
       value domain against an erased binder is a category's object, kept on
       one side and erased on the other. *)
    | Miniml.Tarr (Miniml.Tdummy _, c1), Miniml.Tarr (Miniml.Tdummy _, c2) ->
      let rec past_abstractions t =
        match resolve_tmeta t with
        | Miniml.Tarr (Miniml.Tdummy _, c) -> past_abstractions c
        | t -> t
      in
      unify (past_abstractions c1) (past_abstractions c2)
    | Miniml.Tarr (d1, c1), Miniml.Tarr (d2, c2) ->
      unify d1 d2 ;
      unify c1 c2
    (* A carrier applied to arguments -- [m A] -- is the shape a class method
       is written in, and its element is exactly the variable a call site
       cannot deduce.  The heads are variables themselves, so they pin nothing
       down against each other; the arguments do. *)
    | Miniml.Tapp (_, a1), Miniml.Tapp (_, a2)
      when List.length a1 = List.length a2 -> List.iter2 unify a1 a2
    (* An applied variable against a concrete application of the same arity: the
       variable stands for the head, which the actual type names, and the
       arguments are what both are applied to. This is the only place a [Type ->
       Type] argument can still be read off -- MiniML erases the argument
       itself, and what is left is the constraint that mentions it.

       Asked for, not assumed: where a class's carrier is what the variable
       stands for, the head alone is the wrong answer. A composed carrier [fun t
       => option (Exp t)] meets an [option (Exp any)] here and the head is
       [option], which is the arity deduction would have guessed and precisely
       what a composition is not. The dictionary routes recover those, and they
       must be left to reach them. *)
    | Miniml.Tapp (k, a1), Miniml.Tglob (g, a2, l)
      when constructors && List.length a1 = List.length a2 ->
      bind k (Miniml.Tglob (g, [], l));
      List.iter2 unify a1 a2
    (* A carrier is a head partially applied: [M T] against [itree TopE T]
       binds [M] to [itree TopE], the arguments the application writes ahead
       of the ones the variable is applied to.  Only where those are families
       -- a head, or one at its erased index: [modul nat (cfg nat)] is as
       much [fun T => modul T (cfg T)] at [nat] as [modul nat] at
       [cfg nat], and a prefix of plain types cannot say which. *)
    | Miniml.Tapp (k, a1), Miniml.Tglob (g, a2, l)
      when constructors && List.length a1 < List.length a2
           && List.for_all
                (fun t ->
                  match resolve_tmeta t with
                  | Miniml.Tglob (_, [], _) -> true
                  | Miniml.Tglob (_, args, _) ->
                    Ml_type_util.is_ml_erased_ty (List.nth args (List.length args - 1))
                  | _ -> false )
                (List.filteri (fun i _ -> i < List.length a2 - List.length a1) a2) ->
      let n_fixed = List.length a2 - List.length a1 in
      bind k (Miniml.Tglob (g, List.filteri (fun i _ -> i < n_fixed) a2, l));
      List.iter2 unify a1 (List.filteri (fun i _ -> i >= n_fixed) a2)
    (* A type alias meets an actual type already written as what it expands to:
       a class with a single field is inlined to that field, so a constraint
       spelled [Sub UBE E] meets an [UBE X -> UBE X]. Expanding puts both in the
       same form, and the alias's arguments are what its own parameters stand
       for. *)
    | Miniml.Tglob (GlobRef.ConstRef kn, cargs, _), actual when constructors ->
      ( match Table.lookup_typedef_unchecked kn with
      | Some body -> unify (Mlutil.type_subst_list cargs body) actual
      | None -> () )
    | _ -> ()
  in
  (* [args] holds the value arguments only, so a [Tdummy] formal -- an erased
     type or proof parameter -- consumes none of them.  What is left once they
     run out is the type of the application -- the codomain, or for a partial
     application the callable still to be applied -- and [result], where the
     position states one, says what it is. *)
  let rec walk ty args =
    match (resolve_tmeta ty, args) with
    | Miniml.Tarr (Miniml.Tdummy _, cod), _ -> walk cod args
    | Miniml.Tarr (dom, cod), a :: rest ->
      ( match arg_ml_ty a with
      | Some t -> unify dom t
      | None -> () ) ;
      walk cod rest
    | ty, [] -> Option.iter (unify ty) result
    | _ -> ()
  in
  walk callee_ty args ;
  Hashtbl.fold (fun i t acc -> (i, t) :: acc) found []

(** {!tvar_instantiation_found} padded into the positional list
    {!Mlutil.type_subst_list} expects: position [i] instantiates
    [Tvar (_, i + 1)], and a variable no argument mentions keeps itself, so
    substituting leaves it alone. *)
and tvar_instantiation callee_ty args =
  match tvar_instantiation_found callee_ty args with
  | [] -> []
  | found ->
    let n = List.fold_left (fun m (i, _) -> max i m) 0 found in
    List.init n (fun k ->
        match List.assoc_opt (k + 1) found with
        | Some t -> t
        | None -> Miniml.Tvar (Miniml.Schematic, k + 1) )

(** [complete_short_tys id tys args] extends a call's type-argument list to the
    length the callee's schema needs, where the arguments determine the
    missing entries and C++ could not have deduced them.

    All or nothing: C++ takes a prefix of the parameter list, so a position
    that cannot be named leaves every later one unnameable too, and writing a
    shorter prefix than the undeducible variable's position achieves nothing.
    Positions the compiler can deduce are left to it -- naming a type twice is
    an opportunity to spell it differently, not a safeguard. *)
and complete_short_tys id tys args =
  match find_type_opt id with
  | None -> tys
  | Some callee_ty ->
    let n = IntSet.fold max (collect_tvars_set IntSet.empty callee_ty) 0 in
    let have = List.length tys in
    if have >= n then tys
    else
      let deducible =
        match deducible_tvars_of_glob id with
        | Some d -> d
        | None -> IntSet.empty
      in
      let missing = List.init (n - have) (fun k -> have + k + 1) in
      if List.for_all (fun i -> IntSet.mem i deducible) missing then tys
      else
        let found = tvar_instantiation_found ~in_scope:true callee_ty args in
        let recovered = List.map (fun i -> List.assoc_opt i found) missing in
        if List.for_all Option.has_some recovered then
          tys @ List.map Option.get recovered
        else tys

(** [fill_erased_tys id tys args] replaces an erased entry of a call's
    type-argument list with what the value arguments say it stands for.

    MiniML erases a [Type -> Type] argument, but the callee still declares a
    template parameter for it -- and the erasure is contagious: template
    arguments are positional, so the all-or-nothing rule in
    {!Ml_type_util.filter_erased_type_args} drops the concrete entries beside
    it. One lost family therefore costs every type argument the call could have
    written, including the ones nothing can deduce.

    The family survives in the type of whatever argument is constrained in it --
    [Sub UBE E] against a [Sub UBE UBE] -- which is what
    {!tvar_instantiation_found} reads.

    Unlike {!complete_short_tys} this fills interior positions, which is sound
    for the same reason: the entry it replaces stands for a variable the callee
    quantifies at exactly that position. *)
and fill_erased_tys ?(only_alias_args = false) id tys args =
  let erased = function
    | Miniml.Tdummy Miniml.Ktype -> true
    | _ -> false
  in
  if not (List.exists erased tys) then
    tys
  else
    match
      find_type_opt id
    with
    | None -> tys
    | Some callee_ty ->
      (* Only a variable the callee applies: this pass exists because MiniML
         erases a [Type -> Type] argument, and a plain type argument that came
         out erased is erased for a reason a value argument cannot undo. *)
      let applied = Ml_type_util.applied_ml_tvar_arities [callee_ty] in
      (* Nor one a type alias in a domain is applied to: [ReSum_id : Id_ obj C
         -> ...] takes the category's morphism constructor [C], a type-level
         function erased for that reason alone, and the definitional class
         [Id_] -- an alias -- states it through the argument passed at it.
         A class, not any alias: [halist K V], a plain one, is applied to a
         value-indexed family whose argument's type is one instance of it.
         The erasure the rule above protects is a dependent inductive's
         ([sigT]), never an alias's. *)
      let in_dictionary =
        let rec alias_arg v = function
          | Miniml.Tglob ((GlobRef.ConstRef _ as g), l, _)
            when Typeclasses.is_class g ->
            List.exists
              (fun a ->
                (match resolve_tmeta a with
                 | Miniml.Tvar (_, j) -> j = v
                 | _ -> false)
                || alias_arg v a )
              l
          | Miniml.Tglob (_, l, _) -> List.exists (alias_arg v) l
          | Miniml.Tmeta {contents = Some t} -> alias_arg v t
          | _ -> false
        in
        fun v ->
          List.exists (alias_arg v)
            (List.map resolve_tmeta (ml_domains callee_ty))
      in
      let found =
        tvar_instantiation_found
          ~in_scope:true
          ~constructors:true
          callee_ty
          args
      in
      List.mapi
        (fun k t ->
          if
            erased t
            && ((not only_alias_args) && Hashtbl.mem applied (k + 1)
               || in_dictionary (k + 1))
          then
            match
              List.assoc_opt (k + 1) found
            with
            | Some t' when not (erased t') -> t'
            | _ -> t
          else
            t )
        tys

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
  match find_type_opt r with Some ty -> ml_ret_is_skipped ty | None -> false

(** Whether a global denotes a typeclass instance. *)
let ref_is_instance r =
  match find_type_opt r with
  | Some ty -> ml_type_is_instance ty
  | None -> false


(* Use Common.extract_at_pos for extracting elements at a position *)

(** Create a substitution function for extra type variables in C++ types.
    num_ind_vars: number of type vars from the containing inductive/record
    extra_tvar_map: mapping from Tvar index to Id for extra type vars *)
let make_subst_extra_tvars num_ind_vars extra_tvar_map =
  let rec subst = function
    | Tvar (Tv_index (i, None)) when List.mem_assoc i extra_tvar_map ->
      named_tvar ((List.assoc i extra_tvar_map))
    | Tvar (Tv_index (i, None)) when i >= 1 && i <= num_ind_vars ->
      (* Inductive's type var - keep as-is for tvar_subst_stmt *)
      Tvar (Tv_index (i, None))
    | Tfun (dom, cod) -> Tfun (List.map subst dom, subst cod)
    | Tshared_ptr t -> Tshared_ptr (subst t)
    | Tglob (r, args, e) -> Tglob (r, List.map subst args, e)
    | Tref (k, t) -> Tref (k, subst t)
    | Tconst t -> Tconst (subst t)
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
  | MLmagic (_, a) -> collect_free_rels_set n_bound acc a
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

(** Which free variables of a body being lifted become trailing parameters.

    Lifting moves a body out of the scope that bound its free variables, so
    each one has to arrive as an argument instead -- but not every free rel is
    a value there is anything to pass.

    - A class instance is already carried by {!current_class_temps} as a
      template parameter, explicit at every reference because nothing deduces
      one.  Passing it again emits [const Params _tcI0], which is ill-formed
      (a concept is not a type) and shadows the template parameter it is named
      after, so every use in the body then resolves to the value.
    - An erased or void binder has no value at all.

    Both lift paths ask this, and they ask it of the same [env]: the names are
    the enclosing scope's, so a compiled body needs no substitution and only
    the head and the call sites grow. *)
let lifted_free_vars ~class_temps env free_indices =
  List.filter_map
    (fun i ->
      let name = Common.get_db_name i env in
      let ty = get_env_type i in
      if
        List.exists (fun (_, id) -> Id.equal id name) class_temps
        || isTdummy ty
        || ml_type_is_void ty
      then
        None
      else
        Some (name, ty, i) )
    free_indices

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
  | Tshared_ptr _ -> Tref (Lvalue, Tconst cpp_ty)
  | _ when is_inductive_value_type cpp_ty ->
    if is_owned then cpp_ty  (* pass by value, caller moves *)
    else Tref (Lvalue, Tconst cpp_ty)  (* const T& for borrowing *)
  | Tvar _ | Tqualified _ ->
    (* Template type parameters and dependent types (e.g. typename C::t) have
       unknown concrete size; always pass by const-ref to avoid deep copies.
       When owned (caller moves in), pass by value to enable move semantics. *)
    if is_owned then cpp_ty
    else Tref (Lvalue, Tconst cpp_ty)
  | _ -> cpp_ty

(** Check if the return type of an ML function type is erased — i.e., it
    becomes [std::any] in C++.  This covers three cases:
    - Promoted type vars (erased carrier projections like [Obj C]).
    - [Tunresolved] arising from dependent type families.
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

(** [ml_projection_field_type a] -- the type of the field a single-branch
    record projection reads, applied to whatever the projection applies it to.

    A projection is an [MLcase] over the instance whose one branch returns a
    destructured field, and the class declares that field's type.  The
    branch's own return annotation does not: it is written where the class's
    carrier is erased, so it says [Tunknown] in the position the field names.
    This is therefore the only place a projection's result type is written
    down. *)
let ml_projection_field_type = function
  | Miniml.MLcase (Tglob (r, _, _), _, pv) when Array.length pv = 1 ->
    let ids, _, _, proj_body = pv.(0) in
    let n = List.length ids in
    let projected = function
      | Miniml.MLrel i | MLmagic (_, MLrel i) when i >= 1 && i <= n ->
        Some (n - i, 0)
      | MLapp ((MLrel i | MLmagic (_, MLrel i)), args) when i >= 1 && i <= n ->
        Some (n - i, count_real_ml_args args)
      | _ -> None
    in
    ( match projected proj_body with
    | Some (idx, nargs) ->
      ( match
          List.nth_opt (filter_value_types (Table.record_field_types r)) idx
        with
      | Some field_ty -> if nargs = 0 then Some field_ty
                         else strip_tarr_n nargs field_ty
      | None -> None )
    | None -> None )
  | _ -> None

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
  | Miniml.MLapp ((MLglob (r, tys) | MLmagic (_, MLglob (r, tys))), args) as full ->
    let direct =
      match find_type_opt r with
      | Some ty ->
        let ty = match tys with [] -> ty | _ -> Mlutil.type_subst_list tys ty in
        ( match strip_tarr_n (count_real_ml_args args) ty with
        | Some ret_ty -> ml_return_type_is_erased ret_ty
        | None -> false )
      | None -> false
    in
    direct ||
    (match full with Miniml.MLapp (f, _) -> ml_body_returns_erased_field f | _ -> false)
  | Miniml.MLapp (f, _) -> ml_body_returns_erased_field f
  | MLmagic (_, f) -> ml_body_returns_erased_field f
  | MLcase _ as c ->
    ( match ml_projection_field_type c with
    | Some field_ty -> ml_return_type_is_erased field_ty
    | None -> false )
  | _ -> false

(** Check if the head of an ML application has an [MLmagic] wrapper.

    The [simpl] optimization in {!Mlutil} transforms
    [MLmagic (_, MLapp(f, args))] into [MLapp(MLmagic (_, f), args)], pushing magic
    inside application heads.  A top-level [MLmagic] check therefore misses
    these cases.  This function follows application heads recursively.

    Used in {!gen_spec} to detect when a function call's result needs a C++
    cast to match the expected return type. *)
let rec ml_head_has_magic = function
  | Miniml.MLmagic (_, _) -> true
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

(** Strip a single [Tnamespace] wrapper off a namespaced [Tglob], leaving any
    other type untouched. Used to see through the namespace qualifier when
    classifying list-like globals. *)
let strip_ns_tglob = function
  | Tnamespace (_, (Tglob _ as inner)) -> inner
  | t -> t

(** Binder-type state: {!Translation_state.cpp_binder_types}, every binder's
    C++ type tagged with what decided it. *)
type binder_env = (cpp_type * binder_origin) IntMap.t

(** Strip self-referential [Tnamespace] wrappers, at every depth.

    Flat single-file extraction sometimes wraps a module-local inductive in
    [Tnamespace (g, Tglob (g, ...))], which renders as the bogus
    [typename G::G<...>].  Unwrapping those leaves a well-formed type; every
    other namespace qualifier is preserved. *)
let rec clean_self_ns t =
  match t with
  | Tnamespace (ns_r, Tglob (g_r, args, gns)) when GlobRef.CanOrd.equal ns_r g_r
    ->
    clean_self_ns (Tglob (g_r, args, gns))
  | Tnamespace (ns_r, inner) -> Tnamespace (ns_r, clean_self_ns inner)
  | Tglob (gr, args, ns) -> Tglob (gr, List.map clean_self_ns args, ns)
  | Tref (k, t) -> Tref (k, clean_self_ns t)
  | Tshared_ptr t -> Tshared_ptr (clean_self_ns t)
  | t -> t

(** Rewrite a local fixpoint's recursive calls to pass the self-parameters.

    Both lowerings of a local fixpoint -- the by-reference one and the
    Y-combinator one -- generate an [f_impl] lambda that takes [_self_f]
    ahead of its own arguments, so both need every call to [f] inside the
    body to grow that argument.  The rewrite is the same one, so it lives
    here rather than in each.

    A recursive call reaches its arguments through however many applications
    MiniML curried it into: [f a b] can arrive as one call of two arguments
    or as two calls of one.  The lambda takes them all at once, so the
    application spine is flattened before [_self_f] is prefixed -- rewriting
    only the innermost call yields [_self_f(_self_f, a)(b)], which asks a
    three-argument lambda for two.  A unary fixpoint cannot show the
    difference, which is why this went unnoticed.

    [renamed_ids] and [self_ids] are positionally paired.
    @return the expression and statement rewriters, which are mutually
      recursive and must be taken together. *)
let self_call_rewriter (renamed_ids : (Id.t * 'a) list) (self_ids : Id.t list)
    : (cpp_expr -> cpp_expr) * (cpp_stmt -> cpp_stmt) =
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
  (* The self id this application spine calls, with every argument along it
     in one reversed list -- an outer application's arguments come after an
     inner one's, so they go first once reversed. *)
  let rec self_call_spine = function
    | CPPfun_call (_, CPPvar id, args) ->
      Option.map (fun self_id -> (self_id, to_reversed args)) (find_self_id id)
    | CPPfun_call (_, callee, args) ->
      Option.map
        (fun (self_id, inner) -> (self_id, to_reversed args @ inner))
        (self_call_spine callee)
    | _ -> None
  in
  let rec rewrite_expr e =
    match self_call_spine e with
    | Some (self_id, args_rev) ->
      CPPfun_call
        ( call_opaque, CPPvar self_id,
          of_reversed (List.map rewrite_expr args_rev @ self_vars_rev) )
    | None -> map_expr rewrite_expr rewrite_stmt Fun.id e
  and rewrite_stmt s = map_stmt rewrite_expr rewrite_stmt Fun.id s in
  (rewrite_expr, rewrite_stmt)

(** [ml_ast_type_hint e] is the ML type [e] carries, when it carries one: a
    constructor's own annotation, or the source type of a coercion extraction
    inserted around it.  Used to recover a type argument left [Tunresolved] by
    extraction. *)
let rec ml_ast_type_hint = function
  | Miniml.MLcons (t, _, _) -> Some t
  | Miniml.MLmagic (Miniml.Mcoerce (from, _), inner) ->
    ( match Ml_type_util.resolve_tmeta from with
    | Miniml.Tunknown | Miniml.Tdummy _ -> ml_ast_type_hint inner
    (* A function value's representation at a slot it is coerced into is the
       boxed one [crane_erase_fn] produces, never its own arrow type: grounding
       it would defeat the boxing and the consumer's fixed [any_cast]. *)
    | Miniml.Tarr _ -> None
    | t -> Some t )
  | Miniml.MLmagic (_, inner) -> ml_ast_type_hint inner
  | _ -> None

(** Convert ML type to C++ type. Handles custom types, inductives, type
    variables, and erased parameters. env: variable environment; ns: set of
    local references; tvars: type variable names *)

(** What the position a subterm occupies tells the generator about how to
    build it.  These properties travel together down every position whose
    value ends up in the same slot -- an argument, a coercion's operand, a
    branch result, a tail expression, the body of a lambda that is itself the
    stored value.  A position that opens a new slot (a let-bound right-hand
    side, a non-tail statement) starts again from {!empty_slot}. *)
type slot = {
  deep_erase : bool;
      (** The slot is really [std::any], so a constructor built for it has to
          use the canonical erased shape: every producer of the same Coq type
          must agree with the fixed [any_cast] that reads it back.  A "cons"
          production keeping [deque<Prod<Nat, Nat>>] where the matching "nil"
          erased to [deque<Prod<any, any>>] is what [std::bad_any_cast] at the
          consumer looks like. *)
  expected_ml_ty : ml_type option;
      (** The ML type of the slot, when the caller knows it more precisely than
          the expression's own annotation does.  It lets a constructor whose
          annotation carries unresolved metas (a [nil] whose element type
          extraction left open, say) recover the concrete type arguments from
          the position it occupies. *)
  in_ctor_arg : bool;
      (** The slot is an argument of a constructor, so a nested constructor
          filling it cannot name a template parameter of its own: an
          out-of-range [Tvar] here is an erased field, which is [std::any]. *)
  eta_keep_moves : bool;
      (** The slot holds a single-use partial application whose closure may
          capture by reference and keep its [CPPmove] wrappers.  Read once, by
          the {!eta_fun} that builds that closure. *)
  call_result : cpp_type option;
      (** The type the call this slot is an argument of is expected to
          produce.  An instance passed as a value -- [MonadIter_itree] as
          [interp]'s dictionary, whose own slot erases with the class's
          carrier -- has its carrier head that type, and so is where an
          argument extraction erased from it is read back
          ({!instance_family_binding}). *)
  stated_ml_ty : ml_type option;
      (** The ML type the position states, erased parts and all -- the
          parameter an argument is passed at, [stateT nat (itree BotE) T] with
          [BotE] applied at its erased index.  {!expected_ml_ty} withholds a
          type with erasures in it, which is right for what it is used for;
          this is read only where an erased part is expected, to recover an
          event family nothing deduces. *)
}

(** What a call to a global is, before its arguments are generated; see
    {!plan_call}. *)
type call_plan = {
  cp_excess_args : ml_ast list;
  cp_primary_args : ml_ast list;
  cp_instance_args : ml_ast list;
  cp_regular_args : ml_ast list;
  cp_leading_params : int;
  cp_expected_result : cpp_type option;
  cp_instance_type_args : cpp_type option list;
  cp_instance_families : (cpp_type * Id.t list * (Id.t * cpp_type) list) list;
  cp_fn_ml_ty : ml_type;
  cp_tys : ml_type list;
  cp_dictionary_filled : bool;
  cp_fn_ml_ty_subst : ml_type;
  cp_params : Param_pos.subst Param_pos.params;
  cp_params_orig : Param_pos.orig Param_pos.params;
  cp_subst_index_of_orig : Param_pos.orig Param_pos.pos -> Param_pos.subst Param_pos.pos option;
  cp_tvars : Id.t list;
  cp_concrete_tvar_type : cpp_type option;
  cp_instance_promoted : (Id.t * cpp_type) list;
  cp_result_tvar_map : (Id.t list * (Id.t * cpp_type) list) Lazy.t;
}

(** The slot properties of a position that constrains nothing. *)
let empty_slot =
  { deep_erase = false;
    expected_ml_ty = None;
    in_ctor_arg = false;
    eta_keep_moves = false;
    call_result = None;
    stated_ml_ty = None }

(** Mark the template arguments of [g] that its declaration spells
    [template <typename> class].  Such a position takes a bare template name
    ([wrapped<List, uint64_t>]), never an instantiation, so every site that
    spells an instantiation of [g] -- its type, its factory calls, and the
    constructor structs a match qualifies -- has to agree on this. *)
let apply_hkt_tyctors g temps =
  (* A template-template position takes a {e unary} constructor, and what
     reaches it may be an application of more than one argument: Rocq's
     [TFunctor (fun T => two T (FnBody T))] normalises to [two] applied to
     both, with the binder gone.  Naming that head alone spells a constructor
     of the wrong arity, and the declaration it appears in does not compile.

     Putting the binder back is what the position wants, and the printer
     already mints an alias template for a body carrying the sentinel
     ({!Minicpp.abstract_cpp_type}).  The argument the position varies in is
     the leading one -- the class applies its carrier to the traversed type,
     and this idiom writes that type first.

     The unary case goes through the same rule and comes out unchanged:
     [box<_CraneTcArg>] is a head plus the sentinel, which the printer
     recognises and prints as the bare name. *)
  let rec abstract_leading_arg t =
    match t with
    (* A qualification is spelling: an external carrier ([ITree]'s [itree])
       arrives wrapped, and is abstracted inside the wrapper. *)
    | Tnamespace (ns, inner) -> Tnamespace (ns, abstract_leading_arg inner)
    | t ->
    let args =
      match t with
      (* A custom mapping is excluded: its replacement text says for itself
         which argument the C++ template varies in, and that is not in general
         the leading one -- [itree]'s is its last.  The printer substitutes the
         sentinel through the mapping rather than into the argument list. *)
      | Tglob (g, args, _) when not (Table.is_custom g) -> args
      | Tid (_, args) | Tid_external (_, args) | Tapply (_, args) -> args
      | _ -> []
    in
    (* A partial application -- [stateT S (itree E)], the carrier [itree E]
       -- varies in the argument eta-expansion appended, an unknown type
       ([Topaque], or [std::any]): the last such, by position, since an
       erased argument elsewhere may be spelled the same.  Where there is
       none, the leading one. *)
    let hole =
      List.fold_left
        (fun (i, found) a ->
          (i + 1, if a = Topaque || a = Tany then Some i else found) )
        (0, None) args
      |> snd
    in
    let with_sentinel_at k =
      let args =
        List.mapi
          (fun i a -> if i = k then Thole else a)
          args
      in
      match t with
      | Tglob (g, _, es) -> Tglob (g, args, es)
      | Tid (id, _) -> Tid (id, args)
      | Tid_external (id, _) -> Tid_external (id, args)
      | Tapply (h, _) -> Tapply (h, args)
      | t -> t
    in
    match args with
    | over :: _ :: _ -> (
      (* Only a constructor of arity above one needs abstracting.  A unary one
         is already a head plus its argument, which the printer cuts to the
         bare name; substituting the sentinel there would hand it a body it
         reads as an abstraction rather than an application, and it would mint
         an alias for a template that can simply be named. *)
      match hole with
      | Some k when k > 0 -> with_sentinel_at k
      | _ -> (
        match Minicpp.abstract_cpp_type ~over t with Some b -> b | None -> t ) )
    | _ -> t
  in
  List.mapi
    (fun i t ->
      if Table.is_hkt_ind_param g i then Ttyctor (abstract_leading_arg t)
      else
        match t with
        | Tapply ((Tvar tv as head), _)
          when Table.is_phantom_type_param g i
               || Option.cata is_current_typename_var false (tvar_hint tv) ->
          (* The application cannot be written, so the head alone stands for
             it -- which is all a phantom position reads anyway, and all an
             erased family has left to say.

             The deciding fact is the {e variable's} kind in the head this
             declaration is being given, not the position's: the first branch
             already took every position [g] made a template, so what is left
             is a plain [typename], and a plain [typename] is where an applied
             template-template parameter belongs ([List::list<T1<std::any>>]).
             Stripping there is what breaks it.  A parameter the declaration
             spells [typename] is the opposite case: it is neither phantom nor
             higher-kinded, and writing the application is what made two
             readings disagree about its kind. *)
          head
        | _ -> t )
    temps

(** The name a type variable carries in [tvars], where it has one.  MiniML
    numbers them from one, and a scope shorter than the type -- a declaration
    read before its own quantifiers are in hand -- simply leaves the variable
    unnamed rather than being an error. *)
let tvar_name_at tvars i =
  if i >= 1 then List.nth_opt tvars (pred i) else None
