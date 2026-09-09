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
    populated by {!Cpp_ind} as declarations are processed and read here and by
    {!Cpp_print} (which suppresses [__attribute__((pure))] on functions whose
    type mentions one, since they may call a throwing axiom stub). *)

let axiom_type_refs : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 16

(** Register a GlobRef as an axiom type. *)
let register_axiom_type (r : GlobRef.t) = Hashtbl.replace axiom_type_refs r ()

(** Whether a GlobRef has been registered as an axiom type. *)
let is_axiom_type_ref (r : GlobRef.t) = Hashtbl.mem axiom_type_refs r

(** {2 The boxedness oracle} *)

(** Names introduced by [using X = std::any;].  Populated as declarations are
    walked, in the order they are emitted, so an alias is visible exactly where
    C++ would see it. *)
let any_type_aliases : Id.Set.t ref = ref Id.Set.empty

(** [is_any_shaped ty] — [ty] is spelled [std::any] in the generated code,
    whether directly, through a type modifier, through an alias introduced by a
    [using] declaration, or because it is an axiom type. *)
let rec is_any_shaped = function
  | Tany | Topaque -> true
  | Tmod (_, inner) | Tref inner | Tnamespace (_, inner) -> is_any_shaped inner
  | Tid (id, []) -> Id.Set.mem id !any_type_aliases
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
    [crane_any_cast]. *)
let tolerant ty = instance_dependent ty <> None || needs_deep_recovery ty

(** The two method-registry queries the boxed-result test needs.  The registry
    sits above this module in the dependency order, so {!Cpp_print} installs
    them at load time. *)
type method_queries = {
  mq_returns_any : GlobRef.t -> bool;  (** is the result declared [std::any]? *)
  mq_is_method : GlobRef.t -> bool;  (** is this global called as a method? *)
}

let method_queries =
  ref {mq_returns_any = (fun _ -> false); mq_is_method = (fun _ -> false)}

(** [returns_a_box e] -- [e] is a call whose result is declared [std::any], so
    reading it at a concrete type needs a cast.  Method results are the only
    boxed-return positions the registry tracks; a nested [any_cast] counts too,
    because the tolerant caster hands back a box. *)
let returns_a_box = function
  | CPPaccess_call (Aarrow, CPPglob (n, _, _), _, _) ->
    !method_queries.mq_returns_any n
  | CPPfun_call (_, CPPglob (n, _, _), _) when !method_queries.mq_is_method n ->
    !method_queries.mq_returns_any n
  | CPPfun_call (_, CPPget' (_, n), _) -> !method_queries.mq_returns_any n
  | CPPfun_call (_, CPPany_cast _, _) -> true
  | _ -> false

(** [castable_to ty] -- [ty] names something [any_cast] can ask for.  A type
    variable or an unresolved type does not. *)
let rec castable_to = function
  | Tvar _ -> false
  | Tunresolved | Ttodo | Tany | Topaque | Tauto -> false
  | Tmod (_, inner) -> castable_to inner
  | Tglob (GlobRef.ConstRef _, _, _) -> false
  | _ -> true

(** {2 The pass} *)

(** Record any [std::any] alias a declaration introduces, so that later casts
    in the same emission order can see it. *)
let note_alias id ty =
  if is_any_shaped ty then any_type_aliases := Id.Set.add id !any_type_aliases

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
      Table.mark_needs_erase_fn ();
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
         && boxed_var boxed e ->
    let t = Ml_type_util.resolve_tvars_to_any (Option.get ret) in
    Sreturn (Some (resolve_expr boxed (CPPany_cast (t, e))))
  | Scustom_case (rty, scrut, targs, branches, custom) ->
    Scustom_case (rty, resolve_expr boxed scrut, targs,
      List.map
        (fun (ps, bty, body) ->
          let boxed =
            List.fold_left
              (fun acc (id, ty) ->
                if is_any_shaped ty then Id.Set.add id acc else acc)
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

(** [unbox ty e] -- see [cpp_erasure.mli]. *)
let unbox ty e =
  match e with
  (* [any_cast] to an erased type does not unwrap the box: it asks whether the
     box holds a *further* box, and throws when it does not. *)
  | _ when Ml_type_util.prints_as_any ty -> e
  (* A cast applied straight to a box built here is dead work. *)
  | CPPbox (_, inner) -> inner
  | _ -> CPPany_cast (ty, e)

(** [unbox_tolerant ty e] -- see [cpp_erasure.mli]. *)
let unbox_tolerant ty e =
  match e with
  | CPPbox (_, inner) -> inner
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
  | Dstruct s -> Dstruct {s with ds_fields = List.map resolve_field s.ds_fields}
  (* A constant initialised from a boxed call has to unbox to reach its own
     declared type.  The printer used to decide this while rendering; saying it
     in the IR means the cast goes through the normalisation above like every
     other one. *)
  | Dasgn (id, ty, e) when returns_a_box e && castable_to ty ->
    Dasgn (id, ty, resolve_expr (unbox (Ml_type_util.resolve_tvars_to_any ty) e))
  | _ -> map_decl resolve_expr resolve_stmt (fun t -> t) d

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

(** [settled_child ~parent d] -- see [cpp_erasure.mli].  [parent] is evidence,
    not data: a declaration nested inside a settled one is settled. *)
let settled_child ~parent:_ (d : cpp_decl) : settled = d
