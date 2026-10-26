(** Erasure decisions over the MiniCpp IR.

    A value that crosses into a [std::any] has to be read back out at the shape
    it was written in, and how to do that is not always knowable when the cast
    is built: a pair whose components were boxed one at a time is physically a
    [pair<any, any>] however concrete its type says it is, and a cast whose
    target is an associated type of a type-class instance cannot be resolved
    until C++ instantiates the instance.  [crane_any_cast] in
    [theories/cpp/crane_fn.h] handles both by deferring to [if constexpr].

    Deciding {e which} caster to use used to happen in {!Cpp_print}, which meant
    {!Translation} chose the target type and the printer independently chose the
    caster — two halves of one decision, made in two passes, neither able to see
    the other.  {!resolve_casts} makes the choice once and records it in the IR,
    so the printer only has to spell out what the IR already says.

    This module is also the single home for the question "is this type spelled
    [std::any]", which previously had a third answer here in the printer
    alongside {!Ml_type_util.prints_as_any} and {!Ml_type_util.is_boxed_type}.

    See [docs/nanopass-plan.md]. *)

open Names
open Minicpp

(** {2 Axiom types}

    A Rocq axiom has no computational content, so its type extracts to
    [std::any].  The classification is global to a session — the registry is
    populated from each unit's declarations before anything about the unit
    is planned ({!Cpp.prepare_structure}) and read here: a function whose
    type mentions one is never [constexpr], since it may call a throwing
    axiom stub ({!decide_constexpr}). *)

let axiom_type_refs : unit Ref.User.Tbl.t = Ref.User.Tbl.create 16

(** Register a GlobRef as an axiom type. *)
let register_axiom_type (r : GlobRef.t) = Ref.User.Tbl.replace axiom_type_refs r ()

(** Whether a GlobRef has been registered as an axiom type. *)
let is_axiom_type_ref (r : GlobRef.t) = Ref.User.Tbl.mem axiom_type_refs r

(** {2 The boxedness oracle} *)

(** Names introduced by [using X = std::any;].  Populated as declarations are
    walked, in the order they are emitted, so an alias is visible exactly where
    C++ would see it. *)
let any_type_aliases : Id.Set.t ref = Cpp_state.owned_ref Id.Set.empty

(** The member aliases the struct being walked declares.  A type-level
    declaration whose body erased -- a higher-kinded class field [memM] among
    them -- is spelled through its file-scope alias, [using memM = std::any];
    inside an instance struct the same name is that struct's own alias
    ([natMMP::memM<A> = A]) and says nothing about a box. *)
let member_aliases : Id.Set.t ref = ref Id.Set.empty

let alias_name = function
  | GlobRef.ConstRef c -> Some (Label.to_id (Constant.label c))
  | _ -> None

(** [is_any_shaped ty] — [ty] is spelled [std::any] in the generated code,
    whether directly, through a type modifier, through an alias introduced by a
    [using] declaration, or because it is an axiom type. *)
let rec is_any_shaped = function
  | Tany | Topaque -> true
  | Tconst inner | Tref (_, inner) | Tnamespace (_, inner) ->
    is_any_shaped inner
  | Tid (id, []) -> Id.Set.mem id !any_type_aliases
  | Tglob (g, _, _) as t
    when Ml_type_util.names_erased_alias t
         && ( match alias_name g with
            | Some id -> not (Id.Set.mem id !member_aliases)
            | None -> false ) ->
    true
  | Tglob (GlobRef.ConstRef c, _, _) ->
    is_axiom_type_ref (GlobRef.ConstRef c)
    || ( try
           let t = Table.find_type (GlobRef.ConstRef c) in
           t = Miniml.Tunknown || t = Miniml.Taxiom
         with Not_found -> false )
  | t -> Ml_type_util.is_cpp_dummy_type t

(** [erased_list_shape ty] is the shape a value of list type [ty] physically
    has once it has been through a [std::any]: its elements were boxed one at a
    time, so the container holds [std::any] however concrete [ty]'s element
    type is.  Returns the list's global alongside the shape, because whether
    the concrete-element container can be recovered from it depends on whether
    the list is custom-extracted -- a generated list has the converting
    constructor [List<A>(const List<_U>&)] that unboxes each element, a custom
    one does not and stays flat until a consumer converts it.

    [None] for anything that is not a list, and for a list whose elements are
    erased already: there is nothing to restore. *)
let erased_list_shape ty =
  let rec go = function
    | Tnamespace (ns_g, t) -> (
      match go t with
      | Some (g, t') -> Some (g, Tnamespace (ns_g, t'))
      | None -> None )
    | Tglob (g, [elem], _)
      when Ml_type_util.is_list_global g
           && not (Ml_type_util.prints_as_any elem) ->
      Some (g, Tglob (g, [Tany], []))
    | _ -> None
  in
  go ty

(** [needs_deep_recovery ty] — recovering a [ty] from a box needs the tolerant
    caster rather than a plain [std::any_cast].  A pair with a concrete
    component may have had its components boxed one at a time, so the box holds
    [pair<any, any>] and each component has to be recovered in turn.  An
    all-erased pair is stored as itself and needs no such walk. *)
let needs_deep_recovery = function
  | Tglob (g, ([_; _] as args), _) ->
    Ml_type_util.is_prod_global g
    && List.exists (fun a -> not (is_any_shaped a)) args
  | _ -> false

(** [tolerant ty] — a cast to [ty] cannot be resolved now and must defer to
    [crane_any_cast].  A bare type variable is one: instantiated at
    [std::any] -- [trigger]'s answer type under an erased interpretation --
    a plain [std::any_cast<std::any>] looks for a box inside the box. *)
let tolerant ty =
  instance_dependent ty <> None || needs_deep_recovery ty
  || match ty with Tvar _ -> true | _ -> false

(** [is_method n] -- [n] is rendered as a member function: one the registry
    found in its up-front scan, which every candidate a render collects is
    ({!Method_registry.planned_candidate}).  Mirrors
    [Cpp_names.lookup_method_this_pos], which answers the same question and
    additionally says where [this] sits. *)
let is_method (n : GlobRef.t) : bool = Cpp_state.is_registered_method n <> None

(** [returns_a_box e] -- [e] is a call whose result is declared [std::any], so
    reading it at a concrete type needs a cast.  Method results are the only
    boxed-return positions the registry tracks; an application through the
    erased convention counts too, since that convention hands back a box. *)
let returns_a_box = function
  | CPPaccess_call (Aarrow, CPPglob (n, _, _), _, _) ->
    Cpp_state.method_returns_any n
  | CPPfun_call (_, CPPglob (n, _, _), _) when is_method n ->
    Cpp_state.method_returns_any n
  | CPPfun_call (_, CPPget' (_, n, _), _) -> Cpp_state.method_returns_any n
  | CPPerased_call _ -> true
  | _ -> false

(** [castable_to ty] -- [ty] names something [any_cast] can ask for.  A type
    variable or an unresolved type does not. *)
let rec castable_to = function
  | Tvar _ -> false
  | Tunresolved | Tany | Topaque | Tauto -> false
  | Tconst inner -> castable_to inner
  | Tglob (GlobRef.ConstRef _, _, _) -> false
  | _ -> true

(** {2 The pass} *)

(** Record any [std::any] alias a declaration introduces, so that later casts
    in the same emission order can see it. *)
let note_alias id ty =
  if is_any_shaped ty then any_type_aliases := Id.Set.add id !any_type_aliases

(** [applies_erased_callee e] -- [e] applies a callable that was recovered
    from a box, so its result is a box too however concrete the position it
    lands in is.  Unlike a call to a named function, whose declared result
    type is already right, this one cannot be: the erased convention hands
    back [std::any]. *)
let applies_erased_callee = function CPPerased_call _ -> true | _ -> false

(** [boxed_var boxed e] -- [e] reads a binder that is declared [std::any]. *)
let rec boxed_var boxed = function
  | CPPvar id -> Id.Set.mem id boxed
  | CPPmove e -> boxed_var boxed e
  | _ -> false

(* [boxed] is the set of binders in scope whose declared type is [std::any].
   It is threaded through the walk rather than kept in a ref so that a binder
   is boxed exactly where C++ would see its declaration -- the printer used to
   keep the same set in an ambient ref and save/restore it around every
   construct that introduced one.  [ret] is the enclosing lambda's declared
   return type, or [None] outside one. *)
let rec resolve_expr boxed e =
  match e with
  | CPPany_cast (ty, inner) ->
    let inner = resolve_expr boxed inner in
    if is_any_shaped ty then
      (* Casting a box to [std::any] is the identity, not a cast: [any_cast]
         would look for a further [std::any] stored inside and throw. *)
      inner
    else if tolerant ty then begin
      CPPany_cast_tolerant (ty, inner)
    end
    else
      CPPany_cast (ty, inner)
  | CPPlambda ({cl_params = params; cl_ret = ret_ty; _} as l) ->
    let boxed =
      List.fold_left
        (fun acc (ty, id_opt) ->
          match id_opt with
          | Some id when is_any_shaped ty -> Id.Set.add id acc
          | _ -> acc)
        boxed (to_reversed params)
    in
    CPPlambda (map_lambda (resolve_stmt ~ret:ret_ty boxed) Fun.id l)
  | _ ->
    map_expr (resolve_expr boxed) (resolve_stmt ~ret:None boxed) (fun t -> t) e

and resolve_stmt ?(ret = None) boxed s =
  ( match s with
  | Susing (id, ty) -> note_alias id ty
  | _ -> () );
  match s with
  (* A lambda that returns one of its own boxed parameters has to unbox it to
     reach the declared return type -- [std::function<uint64_t(std::any)>]
     does not compile otherwise.  Only a bare parameter: an any-returning call
     in the same position is already correctly typed in loopified bodies, and
     casting it would silently change the value (regression:
     tests/regression/loopify_variant_self_assign and friends). *)
  | Sreturn (Some e)
    when (match ret with Some t -> castable_to t | None -> false)
         && (boxed_var boxed e || applies_erased_callee e) ->
    let t = Ml_type_util.resolve_tvars_to_any (Option.get ret) in
    Sreturn (Some (resolve_expr boxed (CPPany_cast (t, e))))
  | Scustom_case (rty, scrut, targs, branches, custom) ->
    Scustom_case (rty, resolve_expr boxed scrut, targs,
      List.map
        (fun (ps, bty, body) ->
          let boxed =
            List.fold_left
              (fun acc p ->
                if is_any_shaped p.cp_type then Id.Set.add p.cp_name acc else acc)
              boxed ps
          in
          (ps, bty, List.map (resolve_stmt ~ret boxed) body))
        branches,
      custom)
  | _ ->
    map_stmt (resolve_expr boxed) (resolve_stmt ~ret boxed) (fun t -> t) s

let resolve_expr = resolve_expr Id.Set.empty
let resolve_stmt = resolve_stmt ~ret:None Id.Set.empty

let rec resolve_field ((f, vis, tag) as field) =
  match f with
  | Fnested_using ([], id, ty) ->
    note_alias id ty;
    field
  | Fnested_struct (id, fields) ->
    (Fnested_struct (id, List.map resolve_field fields), vis, tag)
  | _ -> map_field resolve_expr resolve_stmt (fun t -> t) field

(** [converting_ctor ty args] -- see [cpp_erasure.mli]. *)
let converting_ctor ty args =
  match args with
  | [inner] when Ml_type_util.prints_as_any ty ->
    (* Boxing a box is two sites each believing they owned the boundary; the
       inner value would then be unreachable, because the consumer casts once.
       Re-box what was inside instead. *)
    let inner = match inner with CPPbox (_, x) -> x | x -> x in
    CPPbox (ty, inner)
  | _ -> CPPconverting_ctor (ty, args)

(** [empty_box] -- see [cpp_erasure.mli]. *)
let empty_box = converting_ctor Tany []

(** [unbox ty e] -- see [cpp_erasure.mli]. *)
let unbox ty e =
  match e with
  (* [any_cast] to an erased type does not unwrap the box: it asks whether the
     box holds a *further* box, and throws when it does not. *)
  | _ when Ml_type_util.prints_as_any ty -> e
  (* A cast applied straight to a box built here is dead work. *)
  | CPPbox (_, inner) -> inner
  (* Nor is a closure built here a box: [std::any_cast] would wrap it in a
     [std::any] holding the closure type and throw -- a definitional
     instance [:= @id lit], eta-expanded, read back at [Endo<lit>]. *)
  | CPPlambda _ -> e
  | _ -> CPPany_cast (ty, e)

(** [unbox_tolerant ty e] -- see [cpp_erasure.mli]. *)
let unbox_tolerant ty e =
  match e with
  | CPPbox (_, inner) -> inner
  | CPPlambda _ -> e
  | _ -> CPPany_cast_tolerant (ty, e)

(** [resolve_casts decl] rewrites every [CPPany_cast] in [decl] to say which
    caster the printer should emit: dropped where the cast is the identity,
    {!Minicpp.CPPany_cast_tolerant} where the shape is only knowable at
    instantiation time, and left alone otherwise.

    Call it on declarations in emission order: [using] aliases are recorded as
    they are met, mirroring where C++ would have them in scope. *)
type settled = cpp_decl

let rec resolve_casts (d : settled) : settled =
  match d with
  (* Spelled out rather than left to [map_decl] only where the alias registry
     has to see a field, or where the recursion must be into [resolve_casts]
     itself so that it does. *)
  | Dtemplate (tps, constr, inner) ->
    Dtemplate (tps, Option.map resolve_expr constr, resolve_casts inner)
  | Dnspace (r, decls) -> Dnspace (r, List.map resolve_casts decls)
  | Dstruct s ->
    let declared =
      List.fold_left
        (fun acc (f, _, _) ->
          match f with Fnested_using (_, id, _) -> Id.Set.add id acc | _ -> acc )
        Id.Set.empty s.ds_fields
    in
    let saved = !member_aliases in
    member_aliases := Id.Set.union declared saved;
    let fields =
      Fun.protect
        ~finally:(fun () -> member_aliases := saved)
        (fun () -> List.map resolve_field s.ds_fields)
    in
    Dstruct {s with ds_fields = fields}
  (* A constant initialised from a boxed call has to unbox to reach its own
     declared type.  The printer used to decide this while rendering; saying it
     in the IR means the cast goes through the normalisation above like every
     other one. *)
  | Dasgn ({da_type = ty; da_init = e; _} as a) when returns_a_box e && castable_to ty ->
    Dasgn {a with da_init = resolve_expr (unbox (Ml_type_util.resolve_tvars_to_any ty) e)}
  | _ -> map_decl resolve_expr resolve_stmt (fun t -> t) d

(** {2 Reading boxed values}

    A value in a [std::any] is read back at a known type by an explicit
    {!Minicpp.CPPunbox}.  Which binders hold boxes is read off their declared
    types -- a parameter, lambda parameter, match binding or custom-match
    branch parameter typed [std::any] -- and a custom pair match on a boxed
    scrutinee says that its branch parameters are boxed too, holding values of
    their declared types.  Reads are then made explicit where the context
    expects a concrete type: a custom template's argument or scrutinee, and
    every use of a branch parameter that holds a known type in a box. *)

type reads = {
  boxed : Id.Set.t;  (** binders holding a [std::any] *)
  stored : cpp_type Id.Map.t;
      (** binders holding a value of this type in a box: read at it on every
          use *)
}

let no_reads = {boxed = Id.Set.empty; stored = Id.Map.empty}

let with_boxed_params r params =
  { r with
    boxed =
      List.fold_left
        (fun acc (id, ty) -> if is_any_shaped ty then Id.Set.add id acc else acc)
        r.boxed params }

(* A type a value can be cast to: not a variable, not unknown, not a constant
   whose definition may itself be [std::any]. *)
let rec is_concrete = function
  | Tvar _ | Tunresolved | Tany | Topaque | Tauto -> false
  | Tconst inner -> is_concrete inner
  | Tglob (GlobRef.ConstRef _, _, _) -> false
  | _ -> true

(* A call that hands back a box: a method registered as returning
   [std::any], or an erased call. *)
let returns_box = function
  | CPPaccess_call (Aarrow, CPPglob (n, _, _), _, _) -> Cpp_state.method_returns_any n
  | CPPfun_call (_, CPPglob (n, _, _), _) when Cpp_names.lookup_method_this_pos n <> None ->
    Cpp_state.method_returns_any n
  | CPPfun_call (_, CPPget' (_, n, _), _) -> Cpp_state.method_returns_any n
  | CPPerased_call _ -> true
  | _ -> false

let rec is_boxed_binder r = function
  | CPPvar id -> Id.Set.mem id r.boxed && not (Id.Map.mem id r.stored)
  | CPPmove e -> is_boxed_binder r e
  | _ -> false

(* [read_as r original e expected] -- [e], the rewritten [original], read at
   [expected] where [original] is a box and [expected] is concrete. *)
let read_as r original e expected =
  if (returns_box original || is_boxed_binder r original) && is_concrete expected then
    CPPunbox (Unbox_to (Ml_type_util.resolve_tvars_to_any expected), e)
  else e

(* A use of a binder holding a value of type [ty] in a box. *)
let read_stored id ty =
  let resolved = Ml_type_util.resolve_tvars_to_any ty in
  match erased_list_shape resolved with
  | Some (g, flat) ->
    (* A custom list's erased shape is a deque of bare boxes; a converting
       read would re-box it.  Another list converts from its flat form. *)
    if Table.is_custom g then CPPunbox (Unbox_to flat, CPPvar id)
    else CPPunbox (Unbox_list (resolved, flat), CPPvar id)
  | None -> (
    match ty with
    | Tqualified _ | Tglob (GlobRef.ConstRef _, _, _) -> CPPunbox (Unbox_or_keep ty, CPPvar id)
    | _ -> CPPunbox (Unbox_to resolved, CPPvar id) )

let rec reads_expr r e =
  let ex = reads_expr r and st = reads_stmt r in
  match e with
  | CPPvar id when Id.Map.mem id r.stored -> read_stored id (Id.Map.find id r.stored)
  (* The cast already names the type; the binder is read bare inside it. *)
  | CPPany_cast (_, CPPvar id) when Id.Map.mem id r.stored -> e
  | CPPlambda l ->
    let r' =
      with_boxed_params r
        (List.filter_map
           (fun (ty, id) -> Option.map (fun id -> (id, ty)) id)
           (to_reversed l.cl_params))
    in
    map_expr (reads_expr r') (reads_stmt r') Fun.id e
  | CPPfun_call (res, (CPPglob (_, _, Some {ci_inline = Some {it_form = Templated; _}; _}) as f), ts) ->
    let expected = match res.cs_params with Ptypes ts -> ts | Punknown -> [] in
    let arg i a =
      match List.nth_opt expected i with
      | Some exp -> read_as r a (ex a) exp
      | None -> ex a
    in
    CPPfun_call (res, ex f, of_reversed (List.rev (List.mapi arg (call_args ts))))
  | _ -> map_expr ex st Fun.id e

and reads_stmt r s =
  let ex = reads_expr r and st = reads_stmt r in
  match s with
  | Smatch (scrut, branches, default) ->
    let branch b =
      let r' =
        with_boxed_params r (List.map (fun fb -> (fb.fb_name, fb.fb_type)) b.smb_field_bindings)
      in
      {b with smb_body = List.map (reads_stmt r') b.smb_body}
    in
    Smatch
      ( {scrut with sc_expr = ex scrut.sc_expr},
        List.map branch branches,
        Option.map (List.map st) default )
  | Scustom_case (typ, scrut, tyargs, branches, cmatch) ->
    reads_custom_case r typ scrut tyargs branches cmatch
  | _ -> map_stmt ex st Fun.id s

(* A custom match.  A pair match on a boxed scrutinee reads the pair at
   [pair<any, any>] -- what a boxed pair holds -- so its type arguments are
   [std::any] and its branch parameters are boxes. *)
and reads_custom_case r typ scrut tyargs branches cmatch =
  let tokens = Foreign_template.match_template cmatch.cm_template in
  let prod_of = function Tglob (g, _, _) when Ml_type_util.is_prod_global g -> Some g | _ -> None in
  let scrut_boxed = match scrut with CPPvar id -> Id.Set.mem id r.boxed | _ -> false in
  let known_prod =
    match scrut with
    | CPPany_cast (ty, _) when prod_of ty <> None -> prod_of ty
    | _ -> ( match typ with Tglob (g, _ :: _, _) when Ml_type_util.is_prod_global g -> Some g | _ -> prod_of typ )
  in
  let preset =
    match scrut with
    | CPPany_cast (ty, _) -> prod_of ty <> None
    | CPPvar _ when scrut_boxed -> (
      match typ with Tglob (g, _ :: _, _) -> Ml_type_util.is_prod_global g | _ -> false )
    | _ -> false
  in
  let has_scrut = List.mem Foreign_template.CCscrut tokens in
  let effective, at_scrut =
    match (scrut, typ) with
    | CPPvar _, Tglob (g, _ :: _, _) when scrut_boxed && Ml_type_util.is_prod_global g ->
      (Tglob (g, [Tany; Tany], []), true)
    | CPPvar _, _ when scrut_boxed ->
      if Ml_type_util.is_prod_global cmatch.cm_inductive then
        ((match known_prod with Some g -> Tglob (g, [Tany; Tany], []) | None -> typ), true)
      else (typ, false)
    | CPPany_cast (ty, _), _ when prod_of ty <> None ->
      (Tglob (Option.get (prod_of ty), [Tany; Tany], []), true)
    | _ -> (typ, false)
  in
  let overridden = preset || (has_scrut && at_scrut) in
  (* The type arguments a template spells before its scrutinee are read
     before the override is known, unless it was known from the start. *)
  let ty_arg_before_scrut =
    let rec go = function
      | [] -> false
      | Foreign_template.CCscrut :: _ -> false
      | (Foreign_template.CCty_arg _ | Foreign_template.CCelem _) :: _ -> true
      | _ :: rest -> go rest
    in
    go tokens
  in
  let tyargs =
    if overridden && (preset || not ty_arg_before_scrut) then List.map (fun _ -> Tany) tyargs
    else tyargs
  in
  let scrut' = if has_scrut then read_as r scrut (reads_expr r scrut) effective else scrut in
  let scrut_is_cast_pair =
    match scrut with CPPany_cast (Tglob (g, _, _), _) -> Ml_type_util.is_prod_global g | _ -> false
  in
  let branch (params, rty, body) =
    let r' = with_boxed_params r (List.map (fun p -> (p.cp_name, p.cp_type)) params) in
    let r' =
      if overridden || scrut_is_cast_pair then
        List.fold_left
          (fun r' {cp_name = id; cp_type = ty; _} ->
            let is_pair = match ty with Tglob (g, _ :: _, _) -> Ml_type_util.is_prod_global g | _ -> false in
            if is_any_shaped ty || is_pair then {r' with boxed = Id.Set.add id r'.boxed}
            else
              let erased =
                match ty with
                | Tglob (g, args, ns) when args <> [] ->
                  Tglob (g, List.map Ml_type_util.erase_type_to_any args, ns)
                | Tnamespace (g, inner) -> Tnamespace (g, Ml_type_util.erase_type_to_any inner)
                | t -> t
              in
              {r' with stored = Id.Map.add id erased r'.stored} )
          r' params
      else r'
    in
    (params, rty, List.map (reads_stmt r') body)
  in
  Scustom_case (typ, scrut', tyargs, List.map branch branches, cmatch)

let reads_method r (m : method_field) =
  let r' = with_boxed_params {r with boxed = Id.Set.empty} m.mf_params in
  {m with mf_body = List.map (reads_stmt r') m.mf_body}

let rec reads_decl (d : settled) : settled =
  match d with
  | Dtemplate (tps, c, inner) -> Dtemplate (tps, c, reads_decl inner)
  | Dnspace (r, ds) -> Dnspace (r, List.map reads_decl ds)
  | Dfun ({df_shape = Ddef (params, body); _} as f) ->
    let r = with_boxed_params no_reads params in
    Dfun {f with df_shape = Ddef (params, List.map (reads_stmt r) body)}
  | _ ->
    let rec field (f, vis, tag) =
      let f =
        match f with
        | Fmethod m -> Fmethod (reads_method no_reads m)
        | Fmember_decl (OLmethod m) -> Fmember_decl (OLmethod (reads_method no_reads m))
        | Fnested_struct (id, fs) -> Fnested_struct (id, List.map field fs)
        | f -> f
      in
      (f, vis, tag)
    in
    ( match d with
    | Dstruct ds -> Dstruct {ds with ds_fields = List.map field ds.ds_fields}
    | Dfields ds -> Dfields {ds with ds_fields = List.map field ds.ds_fields}
    | Dmember_def ({dm_field = OLmethod m; _} as md) ->
      Dmember_def {md with dm_field = OLmethod (reads_method no_reads m)}
    | d -> map_decl (reads_expr no_reads) (reads_stmt no_reads) Fun.id d )

let lower_boxed_reads (d : settled) : settled = reads_decl d

(* [tys] extended with [std::any] for each argument past its end that a
   template parsed into [tokens] names. *)
let supplied tokens tys =
  let missing = Foreign_template.type_arity tokens - List.length tys in
  if missing > 0 then tys @ List.init missing (fun _ -> Tany) else tys

(* A mapped type takes its arguments as the printer reads them: a mapping
   that does not say where they go takes those it is given
   ({!Foreign_template.custom_template_with_args}).  A type constructor named
   unapplied ({!Minicpp.Ttyctor}) is left as it is: the printer names it by
   the arguments it has, positionally. *)
let rec supply_type_args t =
  rewrite_cpp_type
    (function
      | Ttyctor _ as t -> Some t
      | Tglob (r, tys, args) when Table.to_inline r -> (
        match Table.find_custom_opt r with
        | Some s ->
          let tokens =
            Foreign_template.term_template
              (Foreign_template.custom_template_with_args s (List.length tys))
          in
          Some (Tglob (r, supplied tokens (List.map supply_type_args tys), args))
        | None -> None )
      | _ -> None)
    t

let supply_template_args (d : settled) : settled =
  let rec fe e =
    match e with
    | CPPglob (r, tys, (Some {ci_inline = Some tmpl; _} as ci)) ->
      CPPglob (r, supplied (Foreign_template.term_template tmpl.it_text) (List.map supply_type_args tys), ci)
    | e -> map_expr fe fs supply_type_args e
  and fs s =
    match map_stmt fe fs supply_type_args s with
    | Sblock_custom (r, tmpl, result, ty, args, tyargs, b) ->
      Sblock_custom (r, tmpl, result, ty, args, supplied (Foreign_template.term_template tmpl) tyargs, b)
    | Scustom_case (ty, scrut, tyargs, branches, cm) ->
      let tokens = Foreign_template.match_template (custom_match_text cm) in
      Scustom_case (ty, scrut, supplied tokens tyargs, branches, cm)
    | s -> s
  in
  map_decl fe fs supply_type_args d

(* The lambda a methodified function [n] is written as where it is a value,
   its receiver at [pos].  It takes the function's parameters at the types the
   method was declared at, not [const auto &]: a generic lambda has no
   deducible signature, so whatever inspects one -- [crane_erase_fn] probing
   whether it accepts [std::any], [std::function] CTAD -- must instantiate its
   body to find out, and an instantiation that does not type-check is a hard
   error rather than a substitution failure.  A type mentioning a template
   parameter can only be spelled where that parameter is in scope, which a
   lambda in a static data member's initialiser is not, so such a type is left
   generic; a method planned nowhere leaves only the generic form. *)
let method_value n tys pos =
  let spellable ty = if Ml_type_util.contains_tvar ty then None else Some ty in
  let receiver = Option.bind (Cpp_state.method_receiver_cpp_type n tys) spellable in
  let params, receiver_pos =
    match Cpp_state.lookup_method_arity n with
    | arity when arity <= 1 -> ([receiver], 0)
    | arity ->
      (* The plan records the declared parameters in order, without the
         receiver's slot; each carries however many qualifiers the
         declaration gave it, and the lambda spells its own. *)
      let declared = Option.default [] (Callable_abi.method_params n) in
      let rec unqualified = function Tref (_, t) | Tconst t -> unqualified t | t -> t in
      let param i =
        if i = pos then receiver
        else
          let i = if i > pos then i - 1 else i in
          Option.bind (List.nth_opt declared i) (fun ty -> spellable (unqualified ty))
      in
      (List.init arity param, pos)
  in
  CPPmethod_value
    { mv_method = n;
      mv_access = Adot;
      mv_receiver = receiver_pos;
      mv_params = params;
      mv_type_args = Cpp_names.method_type_args n tys }

let lower_method_calls (d : settled) : settled =
  let rec fe e =
    match e with
    | CPPfun_call (_, CPPglob (n, tys, (None | Some {ci_inline = None; _})), args) as call -> (
      match Cpp_names.lookup_method_this_pos n with
      | None -> map_expr fe fs Fun.id call
      | Some pos -> (
        match Common.extract_at_pos pos (call_args args) with
        | Some receiver, rest ->
          (* Every inductive is a value type, reached with a dot; [this] is a
             raw pointer and a [CPPderef] dereferences a smart one, and both
             are reached with an arrow instead.  A method takes its receiver
             as a const [this], so moving it gives the method nothing, and
             on a coinductive's projection picks the overload that copies the
             field out ({!Borrow_projection}). *)
          let receiver = match fe receiver with CPPmove r -> r | r -> r in
          let access, receiver =
            match receiver with
            | CPPthis -> (Aarrow, CPPthis)
            | CPPderef p -> (Aarrow, p)
            | receiver -> (Adot, receiver)
          in
          CPPmethod_call
            { mc_method = n;
              mc_access = access;
              mc_receiver = receiver;
              mc_type_args = Cpp_names.method_type_args n tys;
              mc_args = List.map fe rest }
        | None, _ -> map_expr fe fs Fun.id call ) )
    | CPPglob (n, tys, (None | Some {ci_inline = None; _})) -> (
      match Cpp_names.lookup_method_this_pos n with
      | Some pos -> method_value n tys pos
      | None -> e )
    | e -> map_expr fe fs Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  map_decl fe fs Fun.id d

(* A projection reads a field, and the field's name does not depend on what
   the record was instantiated at, so its type arguments are ignored rather
   than required to be absent: one of a module obtained by functor
   application is applied at a type, and once fell through to an ordinary
   call of a function a suppressed projection never has. *)
let lower_projections (d : settled) : settled =
  let rec fe e =
    match e with
    | CPPfun_call (_, CPPglob (r, _, (None | Some {ci_inline = None; _})), args)
      when Table.is_projection r && call_args args <> [] -> (
      match call_args args with
      | record :: rest ->
        CPPprojection {pj_projection = r; pj_record = fe record; pj_args = List.map fe rest}
      | [] -> assert false )
    | CPPglob (r, _, (None | Some {ci_inline = None; _})) when Table.is_projection r ->
      CPPprojection_value r
    | e -> map_expr fe fs Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  map_decl fe fs Fun.id d

(* A string literal outside any nested statement: as a [?:] branch it stays a
   [const char*], where the lambda's declared return type converted it. *)
let rec reads_string_literal e =
  match e with
  | CPPstring _ -> true
  | _ -> fold_expr_children ~on_expr:(fun found e -> found || reads_string_literal e)
           ~on_stmts:(fun found _ -> found) false e

(* The two values a lambda's body chooses between, when all it does is choose:
   a match of one alternative against the rest, an [if], or a mapped two-way
   case whose template is an [if]. *)
let chosen_values = function
  | { cl_params = {rev = []}; cl_body = [Smatch (scrut, branches, wildcard)];
      cl_capture = Immediate; _ } -> (
    let returns_only br =
      match br with
      | { smb_field_bindings = []; smb_extra_conds = []; smb_body = [Sreturn (Some e)]; _ } ->
        Some e
      | _ -> None
    in
    let tested br e1 e2 =
      Some (mk_call (CPPstd_holds_alternative br.smb_ctor_type) [scrut.sc_expr], e1, e2)
    in
    match branches, wildcard with
    | [br1; br2], None -> (
      match returns_only br1, returns_only br2 with
      | Some e1, Some e2 -> tested br1 e1 e2
      | _ -> None )
    | [br1], Some [Sreturn (Some e2)] -> (
      match returns_only br1 with Some e1 -> tested br1 e1 e2 | None -> None )
    | _ -> None )
  | { cl_params = {rev = []}; cl_body = [Sif (cond, [Sreturn (Some e1)], [Sreturn (Some e2)])]; _ }
    when not (reads_string_literal e1 || reads_string_literal e2) ->
    Some (cond, e1, e2)
  | { cl_params = {rev = []};
      cl_body = [Scustom_case (_, scrut, _, [(_, _, [Sreturn (Some e1)]); (_, _, [Sreturn (Some e2)])], cmatch)];
      _ }
    when String.trim cmatch.cm_template = "if (%scrut) { %br0 } else { %br1 }"
         && not (reads_string_literal e1 || reads_string_literal e2) ->
    Some (scrut, e1, e2)
  | _ -> None

(* The guards read the lambda as written, before anything nested inside it is
   rewritten: a nested conditional exposes the string literals its own lambda
   kept inside a statement. *)
let lower_conditionals (d : settled) : settled =
  let rec fe e =
    match e with
    | CPPfun_call (_, CPPlambda l, {rev = []}) -> (
      match chosen_values l with
      | Some (c, e1, e2) -> CPPcond (fe c, fe e1, fe e2)
      | None -> map_expr fe fs Fun.id e )
    | e -> map_expr fe fs Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  map_decl fe fs Fun.id d

let lower_access_moves (d : settled) : settled =
  let rec fe e =
    match e with
    | CPPaccess (acc, CPPmove inner, id) -> CPPmove (fe (CPPaccess (acc, inner, id)))
    | CPPaccess_call (acc, CPPmove inner, m, args) -> fe (CPPaccess_call (acc, inner, m, args))
    | e -> map_expr fe fs Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  map_decl fe fs Fun.id d

(** {2 Literal types} *)

let rec is_literal_type ty =
  (not (is_any_shaped ty))
  &&
  match ty with
  | Tshared_ptr _ | Tvoid | Tvar _ | Tinstance _ | Tpromoted _ | Tany | Topaque | Tauto
  | Tunresolved ->
    false
  (* [std::function] erases what it holds. *)
  | Tfun _ | Tdecay _ -> false
  | Tglob (r, _, _) when is_axiom_type_ref r -> false
  | Tglob (r, [], _) when Table.is_custom_scalar_ref r -> true
  (* A generated inductive other than an enum has user-provided constructors
     that are not [constexpr], so it is not a literal type. *)
  | Tglob ((GlobRef.IndRef _ as r), tys, _) ->
    Table.is_enum_inductive r && List.for_all is_literal_type tys
  | Tconst t | Tref (_, t) | Tptr t | Tnondeduced t | Tnamespace (_, t) | Tqualified (t, _) ->
    is_literal_type t
  | Tvariant (_, tys) -> List.for_all is_literal_type tys
  (* A defined constant with no arguments is an alias nothing here sees
     through, as is a [Tid] with none. *)
  | Tglob (GlobRef.ConstRef _, [], _) | Tid (_, []) -> false
  | Tglob (_, tys, _) | Tid (_, tys) | Tid_external (_, tys) -> List.for_all is_literal_type tys
  | Trebind (h, x) -> is_literal_type h && is_literal_type x
  | Thole | Terased _ -> true
  | Texpr_type _ | Tdecltype_auto -> false
  (* An applied associated type is whatever the instance makes it. *)
  | Ttyctor _ | Tapply _ -> false

let literal_signature ret params = List.for_all is_literal_type (ret :: List.map snd params)

let eligible b = if b then Eligible else Ineligible

let decide_constexpr (d : settled) : settled =
  let method_ mf =
    { mf with
      mf_constexpr =
        eligible
          ( mf.mf_receiver = Static && (not mf.mf_no_pure)
          && literal_signature mf.mf_ret_type mf.mf_params ) }
  in
  let rec fields fs = List.map (fun (f, vis, tag) -> (field f, vis, tag)) fs
  and field = function
    | Fmethod mf -> Fmethod (method_ mf)
    | Fmember_decl (OLmethod mf) -> Fmember_decl (OLmethod (method_ mf))
    | Fnested_struct (id, fs) -> Fnested_struct (id, fields fs)
    | f -> f
  in
  let struct_ ds = {ds with ds_fields = fields ds.ds_fields} in
  let rec decl = function
    | Dtemplate (tps, c, d) -> Dtemplate (tps, c, decl d)
    | Dnspace (r, ds) -> Dnspace (r, List.map decl ds)
    | Dfun f ->
      let types, throws =
        match f.df_shape with
        | Ddef (params, body) ->
          (List.map snd params, match body with [Sreturn (Some (CPPabort _))] -> true | _ -> false)
        | Ddecl params -> (List.map snd params, false)
      in
      Dfun
        { f with
          df_constexpr =
            eligible ((not (throws || f.df_no_pure)) && List.for_all is_literal_type (f.df_ret :: types)) }
    | Dasgn a ->
      let literal =
        match a.da_init with
        | CPPnumeral _ | CPPuint _ | CPPint _ | CPPbool _ | CPPenum_val _ -> true
        (* A mapped constant constructor of a literal type ([true]) is that
           type's literal. *)
        | CPPglob ((GlobRef.ConstructRef _ as r), [], _) -> Table.is_custom r
        | _ -> false
      in
      Dasgn {a with da_constexpr = eligible (literal && is_literal_type a.da_type)}
    | Dstruct ds -> Dstruct (struct_ ds)
    | Dfields ds -> Dfields (struct_ ds)
    | Dmember_def ({dm_field = OLmethod mf; _} as m) ->
      Dmember_def {m with dm_field = OLmethod (method_ mf)}
    | d -> d
  in
  decl d

(** [bind_free_tvars decl] spells [std::any] every type variable a body names
    that nothing in scope declares.

    A declaration's head is the authority on what type variables it has.  The
    head is built from the instance context a definition sits in; the body is
    generated against the ML type, which still carries the definition's own
    [forall].  Where the two disagree the body wins nothing -- it names [T2]
    under a head declaring [T1], and a name nothing declares does not compile.
    Erasing the use is the same repair {!Minicpp.drop_tparams} makes for a
    lambda, one level up, and for the same reason: half a quantifier is worth
    less than none.

    Scope is threaded rather than collected, because it genuinely nests -- a
    function template inside a struct template inside a namespace, and a
    lambda with template parameters of its own inside all three.  The
    signature counts as declaring: whatever a parameter or the return type
    names, the head had to declare for the signature itself to compile, so the
    body may name it too.

    Only bodies are rewritten.  A signature naming a variable its head does
    not declare is the same defect, but the honest repair there is a different
    one -- give the head the parameter -- and erasing it here would hide the
    case rather than fix it. *)
let bind_free_tvars (d : settled) : settled =
  let add_ids ids bound =
    List.fold_left (fun acc id -> Id.Set.add id acc) bound ids
  in
  let add_ty ty bound = Id.Set.union (tvar_spellings ty) bound in
  let add_tys tys bound = List.fold_left (fun acc t -> add_ty t acc) bound tys in
  let erase bound =
    map_cpp_type (fun t ->
      match t with
      | Tvar _ when not (Id.Set.exists (fun b -> tvar_is b t) bound) -> Tany
      | _ -> t )
  in
  (* A lambda is the one expression that introduces type variables, so it is
     the one expression this has to spell out. *)
  let rec fe bound e =
    match e with
    | CPPlambda l ->
      let bound = add_ids l.cl_tparams bound in
      CPPlambda (map_lambda (fs bound) (erase bound) l)
    | _ -> map_expr (fe bound) (fs bound) (erase bound) e
  and fs bound s =
    match map_stmt (fe bound) (fs bound) (erase bound) s with
    (* A structured binding writes none of its field types -- [const auto
       &[a0, a1]] spells only the names -- so a free variable among them is
       not a name the compiler can fail on, and erasing it would convert an
       imprecision in the IR into a decision about representation, which the
       printer then has to paper over with a cast at every use.  Restore them
       from the statement as it came in. *)
    | Smatch (scrut, branches', dflt) ->
      let restore b' b =
        {b' with smb_field_bindings = b.smb_field_bindings}
      in
      let branches =
        match s with
        | Smatch (_, branches, _)
          when List.length branches = List.length branches' ->
          List.map2 restore branches' branches
        | _ -> branches'
      in
      Smatch (scrut, branches, dflt)
    | s' -> s'
  in
  let body bound stmts = List.map (fs bound) stmts in
  let method_scope bound mf =
    bound
    |> add_ids (List.map snd mf.mf_tparams)
    |> add_ty mf.mf_ret_type
    |> add_tys (List.map snd mf.mf_params)
  in
  let member bound = function
    | OLmethod mf ->
      let bound = method_scope bound mf in
      OLmethod {mf with mf_body = body bound mf.mf_body}
    | OLdestructor stmts -> OLdestructor (body bound stmts)
  in
  let rec field bound ((f, vis, tag) as fld) =
    match f with
    | Fmethod mf ->
      let bound = method_scope bound mf in
      (Fmethod {mf with mf_body = body bound mf.mf_body}, vis, tag)
    | Fconstructor fc ->
      let bound =
        bound
        |> add_ids (List.map snd fc.fc_tparams)
        |> add_tys (List.map snd fc.fc_params)
      in
      (Fconstructor {fc with fc_body = body bound fc.fc_body}, vis, tag)
    | Fdestructor stmts -> (Fdestructor (body bound stmts), vis, tag)
    | Fnested_struct (id, fields) ->
      (Fnested_struct (id, List.map (field bound) fields), vis, tag)
    (* An {!Fmember_decl} is the half without a body; the body is the
       {!Dmember_def} that follows, and is reached there. *)
    | _ -> fld
  in
  let rec go bound d =
    match d with
    | Dtemplate (tps, cstr, inner) ->
      Dtemplate (tps, cstr, go (add_ids (List.map snd tps) bound) inner)
    | Dnspace (r, decls) -> Dnspace (r, List.map (go bound) decls)
    | Dstruct st -> Dstruct (struct_ bound st)
    | Dfields st -> Dfields (struct_ bound st)
    | Dmember_def dm ->
      let bound = add_ids (List.map snd dm.dm_tparams) bound in
      Dmember_def {dm with dm_field = member bound dm.dm_field}
    | Dfun ({df_shape = Ddef (params, stmts); df_ret; _} as f) ->
      let bound = bound |> add_ty df_ret |> add_tys (List.map snd params) in
      Dfun {f with df_shape = Ddef (params, body bound stmts)}
    (* A global's initialiser is a body like any other, and its declared type
       is as much a signature as a function's return type. *)
    | Dasgn a -> Dasgn {a with da_init = fe (add_ty a.da_type bound) a.da_init}
    | _ -> d
  and struct_ bound st =
    let bound = add_ids (List.map snd st.ds_tparams) bound in
    {st with ds_fields = List.map (field bound) st.ds_fields}
  in
  go Id.Set.empty d

(** [materialise decl] replaces every {!Minicpp.Topaque} in [decl] with
    {!Minicpp.Tany}.

    [Topaque] means "the representation is unknown here"; it prints as
    [std::any] but licenses nothing, so a site that meets one must fall back to
    the tolerant helper rather than assume a box.  That is the honest answer
    while a type is still being inferred — but writing [std::any] down in a
    header is precisely the act that decides the representation, and from then
    on the value {e is} boxed.

    Rather than ask each of the many declaration emitters to remember
    {!Ml_type_util.materialise_opaque}, apply it once to the whole declaration
    on the way out of translation.  Print-neutral by construction: [Topaque] and
    [Tany] have the same C++ spelling. *)
let materialise (d : cpp_decl) : settled =
  let ft = Ml_type_util.materialise_opaque in
  let rec fe e = map_expr fe fs ft e
  and fs s = map_stmt fe fs ft s in
  map_decl fe fs ft d

type view =
  | Template of (template_type * Id.t) list * cpp_constraint option * settled
  | Namespace of GlobRef.t option * settled list
  | Decl of cpp_decl

(* The seam is hereditary -- {!materialise} rewrites a declaration together
   with everything nested inside it -- so a settled declaration's children are
   settled. *)
let view (d : settled) =
  match d with
  | Dtemplate (temps, cstr, inner) -> Template (temps, cstr, inner)
  | Dnspace (r, decls) -> Namespace (r, decls)
  | d -> Decl d

let split_definition (d : settled) = Minicpp.split_definition d
let strip_template_defaults (d : settled) = Minicpp.strip_template_defaults d
