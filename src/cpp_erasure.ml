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

(** {2 The pass} *)

(** Record any [std::any] alias a declaration introduces, so that later casts
    in the same emission order can see it. *)
let note_alias id ty =
  if is_any_shaped ty then any_type_aliases := Id.Set.add id !any_type_aliases

let rec resolve_expr e =
  match e with
  | CPPany_cast (ty, inner) ->
    let inner = resolve_expr inner in
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
  | _ -> map_expr resolve_expr resolve_stmt (fun t -> t) e

and resolve_stmt s =
  ( match s with
  | Susing (id, ty) -> note_alias id ty
  | _ -> () );
  map_stmt resolve_expr resolve_stmt (fun t -> t) s

let rec resolve_field ((f, vis, tag) as field) =
  match f with
  | Fnested_using ([], id, ty) ->
    note_alias id ty;
    field
  | Fnested_struct (id, fields) ->
    (Fnested_struct (id, List.map resolve_field fields), vis, tag)
  | _ -> map_field resolve_expr resolve_stmt (fun t -> t) field

(** [resolve_casts decl] rewrites every [CPPany_cast] in [decl] to say which
    caster the printer should emit: dropped where the cast is the identity,
    {!Minicpp.CPPany_cast_tolerant} where the shape is only knowable at
    instantiation time, and left alone otherwise.

    Call it on declarations in emission order: [using] aliases are recorded as
    they are met, mirroring where C++ would have them in scope. *)
let rec resolve_casts (d : cpp_decl) : cpp_decl =
  match d with
  (* Spelled out rather than left to [map_decl] only where the alias registry
     has to see a field, or where the recursion must be into [resolve_casts]
     itself so that it does. *)
  | Dtemplate (tps, constr, inner) ->
    Dtemplate (tps, Option.map resolve_expr constr, resolve_casts inner)
  | Dnspace (r, decls) -> Dnspace (r, List.map resolve_casts decls)
  | Dstruct s -> Dstruct {s with ds_fields = List.map resolve_field s.ds_fields}
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
let materialise (d : cpp_decl) : cpp_decl =
  let ft = Ml_type_util.materialise_opaque in
  let rec fe e = map_expr fe fs ft e
  and fs s = map_stmt fe fs ft s in
  map_decl fe fs ft d
