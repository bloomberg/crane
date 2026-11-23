(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Erasure judgements: whether a Core type or term, a binder or a generated
    expression is a [std::any] box, an opaque erased type or a function
    value, and which family arguments a generic declaration erases.  The
    questions {!Coerce} and lowering decide boxing and recovery
    by; builds nothing. *)

open Base.Common
open Names
open Base.Core_util
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query

(** Check if the return type of a Core function type is erased, i.e. it
    becomes [std::any] in C++.  This covers three cases:
    - Promoted type vars (erased carrier projections like [Obj C]).
    - [Core.Type.Unknown] arising from dependent type families.
    - Erased type constants — non-promoted type-valued record fields
      (e.g. [Hom : Obj -> Obj -> Type] in [PreCategory]) registered during
      extraction via {!Base.Table.add_erased_type_const}. *)
let rec core_return_type_is_erased = function
  | Core.Type.Arrow {result = ret; _} -> core_return_type_is_erased ret
  | Core.Type.Meta { contents = Some t } -> core_return_type_is_erased t
  | Core.Type.Global_app {head = g; _} when Base.Table.is_promoted_type_var g -> true
  | Core.Type.Global_app {head = g; _} when Base.Table.is_erased_type_const g -> true
  | Core.Type.Unknown -> true
  | _ -> false

(** [core_projection_field_type a] -- the type of the field a single-branch
    record projection reads, applied to whatever the projection applies it to.

    A projection is a [Core.Expr.Match] over the instance whose one branch returns a
    destructured field, and the class declares that field's type.  The
    branch's own return annotation does not: it is written where the class's
    carrier is erased, so it says [Core.Type.Unknown] in the position the field names.
    This is therefore the only place a projection's result type is written
    down. *)
let core_projection_field_type = function
  | Core.Expr.Match {scrutinee_type = Core.Type.Global_app {head = r; _}; branches = pv; _} when Array.length pv = 1 ->
    let {Core.Match.Branch.binders = ids; body = proj_body; _} = pv.(0) in
    let n = List.length ids in
    let projected = function
      | Core.Expr.Bound_variable {index = i; _}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} when i >= 1 && i <= n ->
        Some (n - i, 0)
      | Core.Expr.Apply {callee = ( Core.Expr.Bound_variable {index = i; _}
            | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} ); arguments = args}
        when i >= 1 && i <= n ->
        Some (n - i, count_real_core_args args)
      | _ -> None
    in
    ( match projected proj_body with
    | Some (idx, nargs) ->
      ( match
          List.nth_opt (filter_value_types (Base.Table.record_field_types r)) idx
        with
      | Some field_ty -> if nargs = 0 then Some field_ty
                         else strip_arrows_n nargs field_ty
      | None -> None )
    | None -> None )
  | _ -> None

(** Check if a Core expression is (or starts with) a record field projection
    whose projected field returns a promoted type var (erased to [std::any] in
    C++).  This detects the gap between Coq-level types and C++ types that
    arises when a record like [Functor] uses erased carriers ([Obj = std::any])
    in its field types.

    For example, [object_of forward_functor 7] is an [Core.Expr.Apply] wrapping an
    [Core.Expr.Match] record projection.  The projected field [object_of] has Core type
    [carrier → carrier] whose return type [carrier] is a promoted var.  The
    Coq type says the result is [nat = unsigned int], but the C++ expression
    [forward_functor->object_of(7u)] actually returns [std::any]. *)
let rec core_body_returns_erased_field = function
  | Core.Expr.Apply {callee = ( Core.Expr.Global ({callee = r; _} as use)
        | Core.Expr.Coerce {value = Core.Expr.Global ({callee = r; _} as use); _}
        | Core.Expr.Boxed_value {value = Core.Expr.Global ({callee = r; _} as use); _}
        | Core.Expr.Lambda_group_barrier {value = Core.Expr.Global ({callee = r; _} as use); _} ); arguments = args} as
          full ->
    let direct =
      match find_type_opt r with
      | Some ty ->
        let ty = Base.Core_util.instantiate_written ~reader:"core_body_returns_erased_field" use ty in
        ( match strip_arrows_n (count_real_core_args args) ty with
        | Some ret_ty -> core_return_type_is_erased ret_ty
        | None -> false )
      | None -> false
    in
    direct ||
    (match full with Core.Expr.Apply {callee = f; _} -> core_body_returns_erased_field f | _ -> false)
  | Core.Expr.Apply {callee = f; _} -> core_body_returns_erased_field f
  | Core.Expr.Coerce {value = f; _}
  | Core.Expr.Boxed_value {value = f; _}
  | Core.Expr.Lambda_group_barrier {value = f; _} ->
    core_body_returns_erased_field f
  | Core.Expr.Match _ as c ->
    ( match core_projection_field_type c with
    | Some field_ty -> core_return_type_is_erased field_ty
    | None -> false )
  | _ -> false

(** Whether [expr] is a pair recovered from a box, i.e. one whose [any_cast]
    named the erased shape [pair<any, any>] and whose components are therefore
    boxes in their own right. *)
let reads_recovered_pair (e : Cpp_ir.Lowered.Expr.t) =
  match Cpp_ir.Typed.head e with
  | Any_cast (Entity_application (g, args, _), _) | Tolerant_any_cast (Entity_application (g, args, _), _) ->
    is_prod_global g && args <> [] && List.for_all Cpp_ir.Types.prints_as_any args
  | _ -> false

(** [yields_boxed_component expr] -- whether [expr] reads a component out of a
    pair that was itself recovered from a box, and so hands back a
    [std::any] however concrete its Core type looks.

    A boxed pair stores each component separately boxed, so recovering it
    lands on [pair<any, any>] and [.first] on that is still a box.  The
    accessor path in {!Application.eta_fun} builds exactly this shape, and the
    let-binding and tail-position paths ask here rather than being told out of
    band: the emitted expression is the evidence, so no flag has to be
    threaded from producer to consumer. *)
let yields_boxed_component (e : Cpp_ir.Lowered.Expr.t) =
  match Cpp_ir.Typed.head e with
  | Call (_, Entity (_, _, Some {inline = Some {shape = Pair_projection _; _}; _}), [arg]) -> reads_recovered_pair arg
  (* The accessor is not always a custom-inline call: a projection out of a
     [std::pair] is a plain member read, and that is the same evidence. *)
  | Access (Dot, arg, _) -> reads_recovered_pair arg
  | _ -> false

(** Whether the statements a let-binding's right-hand side generated assign a
    value that is really a box.  The right-hand side is generated as an
    assignment, so the bound value is the one expression in it. *)
let stmts_yield_boxed : Cpp_ir.Lowered.Stmt.t list -> bool = function
  | [Bind_variable (_, _, v)] -> yields_boxed_component v
  | _ -> false

(** Whether [r] is a type family over a value -- [sem : idx -> Type] --
    whose applications Core writes without their argument, so that a generic
    declaration erases them where an instantiation can name them. *)
let value_indexed_family r =
  match r with
  (* A class's or record's type field is a function of the instance, not a
     family over a value. *)
  | GlobRef.ConstRef kn
    when Base.Table.is_projection r || Structures.Structure.is_projection kn ->
    false
  | GlobRef.ConstRef _ -> (
    try
      let env = Global.env () in
      let ty, _ = Typeops.type_of_global_in_context env r in
      let prods, head = Reduction.whd_decompose_prod env ty in
      (* A class argument -- a section's [{Pa : Params}] -- is an instance,
         resolved where the family is used, not a value it is indexed by. *)
      let is_class_type t =
        match Constr.kind (fst (Constr.decompose_app t)) with
        | Constr.Ind (ind, _) -> Typeclasses.is_class (GlobRef.IndRef ind)
        | Constr.Const (c, _) -> Typeclasses.is_class (GlobRef.ConstRef c)
        | _ -> false
      in
      Constr.isSort head
      && List.exists
           (fun d ->
             let dty = Context.Rel.Declaration.get_type d in
             let _, h = Reduction.whd_decompose_prod env dty in
             (not (Constr.isSort h)) && not (is_class_type dty) )
           prods
    with _ -> false )
  | _ -> false

(** [erase_type_args_to_any ty] boxes a compound type's arguments but leaves a
    ground type alone: [deque<Nat>] becomes [deque<any>], while [Nat] stays
    [Nat].  This is the shape a box built out of a pattern binder physically
    has, and so the type an [any_cast] recovering it must name.  Deliberately
    weaker than {!Cpp_passes.Erasure}'s [erase_type_to_any], which boxes the leaf
    too. *)
let rec erase_type_args_to_any : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Entity_application (g, (_ :: _ as args), ns) -> Entity_application (g, List.map erase_type_args_to_any args, ns)
  | Entity_application (_, [], _) as t -> t
  | In_namespace (ns_g, inner) -> In_namespace (ns_g, erase_type_args_to_any inner)
  | _ -> Any

(** The shape a value physically has once it has been through a [std::any]:
    unchanged for a leaf, and one level of template with every argument boxed
    for a compound ([pair<Nat, tup>] becomes [pair<any, any>]).  A compound's
    components are separately boxed, so the erasure stops at one level --
    nesting it would name [pair<any, pair<any, any>>] for a box whose second
    component is itself only a box.  This is the type an [any_cast] reading
    such a value back has to name, whatever concrete type the context has in
    mind for it. *)
let boxed_shape_of : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Entity_application (g, (_ :: _ as args), ns) -> Entity_application (g, List.map (fun _ -> Cpp_ir.Type.Any) args, ns)
  | t -> t

(** [core_erases_to_box env t] -- whether [t] is represented as a [std::any]
    here.  Conversion is what answers this: a value-dependent type such as
    [syms_semty xs], or a type variable this scope leaves unresolved, is only
    revealed as a box once converted, and a [Type]-valued definition hides one
    behind a [using] alias that {!Types.resolves_to_any_type} follows. *)
let core_erases_to_box cx env t = Types.resolves_to_any_type cx (Types.cpp_of_core cx env t)

(** [glob_declared_cod_erases r] -- whether the declaration of [r] returns a
    box.  A declaration is converted from the global's own Core type with no
    type variables in scope, and that conversion erases a result no parameter
    pins down -- a type index, say -- however concrete the type is at a given
    call site.  So the question can only be asked of the whole type: the
    codomain alone converts to the type variable and reveals nothing. *)
let glob_declared_cod_erases cx r =
  match callee_core_type cx r with
  | Some ty -> (
    match Types.cpp_ir_of_core_type cx (empty_env ()) [] (type_simpl ty) with
    | Function (_, cod) -> Cpp_ir.Types.prints_as_any cod
    | _ -> false )
  | None -> false

(** [reads_erased_pair_component env t] -- whether the coerced term [t]
    reads a component out of a pair recovered from a box, decided on Core:
    a global call whose one value argument is a coercion from a box planned
    at a product position, which lowering recovers at the erased shape
    [pair<any, any>] ({!boxed_shape_of}).  Such a component is itself a
    box. *)
let reads_erased_pair_component cx env t =
  match t with
  | Core.Expr.Apply {callee = Core.Expr.Global _; arguments = args} -> (
    match List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args with
    | [Core.Expr.Coerce {source_type = from; occurrence = occ; _}] -> (
      Cpp_ir.Types.prints_as_any (Types.cpp_of_core cx env from)
      &&
      match List.find_opt (fun (o, _) -> Core.Occurrence.equal o occ) cx.ctx.lexical.planned_positions with
      | Some (_, Some (Cpp_ir.Type.Entity_application (g, _ :: _, _))) -> is_prod_global g
      | _ -> false )
    | _ -> false )
  | _ -> false

(** Whether an application reads its result out of a value that carries
    erasure.

    An accessor's Core result type says nothing on its own: the second component
    of a dependent pair is a bare type variable whatever the pair holds.  What
    decides is the value being projected from -- a [SigT<std::any, std::any>]
    hands back a box, a [SigT<List<uint64_t>, List<uint64_t>>] hands back a
    list.  So the arguments are the evidence, and each is asked at whichever
    is the better authority on its C++ type: the type a variable's binder is
    planned at, or the term's own Core type. *)
let app_reads_erased_value cx env args =
  let carries t =
    Base.Type_util.has_erased_type_in_type (Types.unfold_cpp_typedef cx env t)
  in
  (* A typeclass dictionary is not one of the values the result is read out
     of: it is how the call states its type arguments, and C++ resolves the
     result through it. *)
  let is_dictionary a =
    match infer_core_body_type (strip_magic a) with
    | Some ty -> (
      match resolve_meta ty with
      | Core.Type.Global_app {head = r; _} -> Base.Table.is_typeclass r
      | _ -> false )
    | None -> false
  in
  List.exists
    (fun a ->
      if is_dictionary a then false
      else
      match strip_magic a with
      | Core.Expr.Bound_variable {index = i; occurrence = occ} -> (
        let carried = Option.map (fun t -> carries (strip_cpp_ref_const t)) in
        match Binders.planned_binder_type_or_derive cx ~use:"erased argument"
          ~agree:(fun p l -> carried p = carried l) env i occ with
        | Some t -> carries (strip_cpp_ref_const t)
        | None -> false )
      | a -> (
        match infer_core_body_type a with
        | Some ty -> carries (Types.cpp_of_core cx env ty)
        | None -> false ) )
    args

(** Whether [e] denotes a value whose Core type is a function (at least one value
    arrow).  Used to decide, at a constructor argument that is stored into an
    erased ([std::any]) field, whether to route it through the [crane_erase_fn]
    runtime helper so the canonical [std::function<std::any(std::any...)>]
    representation is stored (matching the [any_cast] on the application side)
    rather than a raw closure.  An [Core.Expr.Bound_variable] already erased to [std::any]
    ({!Binders.read_is_boxed}) is excluded: it is not callable, so wrapping it
    would miscompile.  [var i occ] says whether the read of the variable [i]
    at [occ] holds a box, and the variable's Core type: by default as lowering
    has them in scope. *)
let core_expr_is_function_value cx ?(var = fun i occ -> (Binders.read_is_boxed cx i occ,
  get_env_type_opt cx i)) e =
  match strip_magic e with
  | Core.Expr.Bound_variable {index = i; occurrence = occ} ->
    let boxed, ty = var i occ in
    (not boxed) && ( match ty with Some t -> count_core_value_arrows t >= 1 | None -> false )
  (* A partial application of a global whose codomain mentions a
     value-dependent erased type (e.g. [mk_action n : domty n -> bool]) is
     wrapped in [Core.Expr.Coerce] by the kernel's typing coercion even at the
     application node itself, not just around the whole expression — so
     [strip_magic] above (which only strips the outer expression) does not
     expose the [Core.Expr.Global] underneath. Look through it here, locally, rather
     than in [infer_core_body_type] itself (whose result also feeds unrelated
     callers like lambda return-type annotation), so this fix cannot change
     behavior anywhere but function-value detection. *)
  | Core.Expr.Apply
    {callee =
      (Core.Expr.Coerce {value = f; _} | Core.Expr.Boxed_value {value = f; _}
        | Core.Expr.Lambda_group_barrier {value = f; _});
                     arguments = args} ->
    ( match infer_core_body_type (Core.Expr.Apply {callee = f; arguments = args}) with
    | Some t -> count_core_value_arrows t >= 1
    | None -> false )
  | other ->
    ( match infer_core_body_type other with
    | Some t -> count_core_value_arrows t >= 1
    (* Inference is best-effort and gives up when a binder's type is itself a
       type-level computation ([sem (TArr a b)] for a [Fixpoint sem : ty ->
       Type]).  A syntactic lambda is a function value whatever its type, so
       fall back on the shape rather than on the failed inference. *)
    | None -> ( match other with Core.Expr.Lambda _ -> true | _ -> false ) )

(** [is_boxed_source t] -- whether a value whose C++ type is [t] is
    physically inside a [std::any], and so may be read back out with an
    [any_cast].

    {!Base.Type_util.is_boxed_type} answers this structurally, which misses a
    named alias for the box: a [Type]-valued definition is emitted as
    [using sel = std::any], and only following the alias chain reveals that a
    parameter of type [sel] is a box.  An opaque type is deliberately
    excluded -- it prints as [std::any] without promising one, so nothing may
    be cast out of it. *)
let is_boxed_source cx (t : Cpp_ir.Lowered.Type.t) =
  is_boxed_type t
  ||
  match t with
  | Obligation Opaque_type -> false
  | Entity_application _ -> Types.resolves_to_any_type cx t
  | _ -> false

(** [classify_erasure ty] -- the erasure status of one side of a value
    boundary, as the single question worth asking about it.

    Three answers are easy to confuse, and the difference decides whether a
    value may be boxed, [any_cast] out of, or left alone:

    - [`Unknown] -- the type was not tracked. Boxing into such a slot is
      allowed; casting {e out} of it never is, since nothing says a box is
      there.
    - [`Boxed] -- the value really is inside a [std::any], so an [any_cast]
      recovers it.  Follows alias chains: a [Type]-valued definition emitted
      as [using sel = std::any] is a box under a name.
    - [`Opaque] -- spelled [std::any] but promising nothing about the
      representation (an opaque type).  Distinct from [`Unknown]: there
      the type is untracked, here it is untrackable.  Nothing may be boxed or
      cast on the strength of it.
    - [`Concrete t] -- an ordinary type.

    Prefer this to assembling an answer out of {!Base.Type_util.prints_as_any},
    {!Base.Type_util.is_boxed_type} and {!Types.resolves_to_any_type} at each site:
    those sit at different layers (see [type_util.mli]) and a site that
    picks the wrong one silently gets [false]. *)
let classify_erasure cx : Cpp_ir.Lowered.Type.t option -> _ = function
  | None -> `Unknown
  | Some f when is_boxed_source cx f -> `Boxed
  | Some f when Cpp_ir.Types.prints_as_any f -> `Opaque
  | Some f -> `Concrete f

(** [spells_as_any t] -- whether [t] is written [std::any] in the
    generated code, following the alias chains that
    {!Cpp_ir.Types.prints_as_any}, being structural, cannot see through. *)
let spells_as_any cx t = Cpp_ir.Types.prints_as_any t || Types.resolves_to_any_type cx t

(** True when environment variable at de Bruijn index [i] has an erased C++
    type (i.e. [std::any] or a dummy type, arising from dependent-parameter
    collapse).  Returns [false] if [i] is out of range.

    This deliberately converts the binder's Core type under [tvars] rather than
    reading {!Binders.binder_cpp_type}, and it is not a re-derivation of the binding
    site's answer: the two say different things, and callers pair them
    precisely to tell those things apart.  A binder the assignment types
    concretely, whose Core type is an out-of-scope variable, is a value held in
    a box under a concrete static type -- exactly the one that has to be
    unboxed.  Reading the assignment here would collapse the contrast and
    drop the [any_cast] (measured: [existential_erased_apply_bad_cpp] and
    [list_cons_erasure_bleed] stop casting). *)
let is_env_var_erased cx env tvars i =
  match get_env_type_opt cx i with
  | Some core_ty ->
    Cpp_ir.Types.prints_as_any (Types.cpp_ir_of_core_type cx env tvars core_ty)
  | None -> false

(** Check whether a Core expression's C++ type is erased ([std::any]).
    Used by the coercion handler ([Expr.gen_crossing]) to decide whether [any_cast] is needed. *)
let rec core_expr_is_erased cx env (t : Core.Expr.t) : bool =
  let tvars = get_current_type_vars cx in
  match t with
  | Core.Expr.Bound_variable {index = i; _} -> is_env_var_erased cx env tvars i
  | Core.Expr.Apply {callee = f; arguments = args} ->
    let n_value_args =
      List.length (List.filter (fun a ->
        match a with Core.Expr.Erased_value _ -> false | _ -> true) args)
    in
    let core_ty_opt = match f with
      | Core.Expr.Global {callee = r; _} -> find_type_opt r
      | Core.Expr.Bound_variable {index = i; _} -> get_env_type_opt cx i
      | _ -> None
    in
    ( match core_ty_opt with
      | Some core_ty -> core_codomain_erases_to_any n_value_args core_ty
      | None -> false )
  | Core.Expr.Global {callee = r; _} ->
    ( match callee_core_type cx r with
      | Some core_ty -> Cpp_ir.Types.prints_as_any (Types.cpp_of_core cx env core_ty)
      | None -> false )
  | Core.Expr.Coerce {value = inner; _}
  | Core.Expr.Boxed_value {value = inner; _}
  | Core.Expr.Lambda_group_barrier {value = inner; _} ->
    core_expr_is_erased cx env inner
  | Core.Expr.Match {scrutinee_type = case_ty; _} ->
    ( match case_ty with
      | Core.Type.Variable _ | Core.Type.Unknown -> true
      | _ -> false )
  | _ -> false

(** Whether an [Core.Expr.Coerce (from, into, _, _)] node says its subterm is
    physically inside a [std::any] here, and so has to be opened before it can
    be used.  (An [Core.Expr.Boxed_value] always does; an [Core.Expr.Lambda_group_barrier] carries no type gap at
    all.)

    A coercion is a box only when one of its two types erases at this
    instantiation: a coercion between two types that are both written down
    concretely -- a typeclass carrier resolved by the instance being
    generated, say -- is a static mismatch the C++ types already agree on, and
    casting on account of it would read a box that was never built. *)
let coercion_is_boxed cx env ~from ~into =
  let erases ty = core_erases_to_box cx env ty in
  erases from || erases into
