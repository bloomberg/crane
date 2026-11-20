(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership and passing: which parameters a body owns, whether a
    parameter of a given C++ or Core type is lent by reference, and the
    const/reference decoration and passing mode that follow from it.  Read by
    lowering and the declaration generators. *)

open Names
open Util
open Lowering_state
open Base.Type_util

(** The de Bruijn indices of the [n] innermost parameters a body owns: those
    [owned] says are passed by value, of a type worth moving.  That is one
    {!Ownership_ir.Region.worth_moving} accepts as reading [ty]; but an erased Core
    type says nothing of how the value is held, and there the type the head
    [declared] it at is read instead ({!Ownership_ir.Region.worth_moving_cpp}):
    [x] in an instance's [fun (A : Type) (x : A) => Some x] is a boxed
    [crane::obj]. *)
let owned_parameters ?(declared : int -> Cpp_ir.Lowered.Type.t option = fun _ -> None) n ~owned ~ty =
  let worth i =
    match (resolve_meta (ty i), declared i) with
    | (Core.Type.Erased _ | Core.Type.Unknown | Core.Type.Axiom), Some cty -> Ownership_ir.Region.worth_moving_cpp cty
    | ty, _ -> Ownership_ir.Region.worth_moving ty
  in
  List.filter_map (fun i -> if owned i && worth i then Some (i + 1) else None) (List.init n Fun.id)

(** Which of [params], innermost first, the function whose [body] stands
    under them owns ({!Core_plan.Ownership.read_off}): those {!Core_plan.Ownership} settled for
    the global [owner] where they cover [params], and otherwise -- a global
    nothing settled, a lambda -- what its own body reads. *)
let infer_owned_flags cx ?owner body params =
  let matches_reuse = Option.map (fun r -> Core.Ref.User.Set.mem r cx.ctx.input.program.reusing_matches) owner in
  let read_off_body () = Core_plan.Ownership.read_off ?matches_reuse ~settled:(settled_ownership cx) params body in
  match Option.bind owner (settled_ownership cx) with
  | Some settled when List.length settled = List.length params ->
    if Base.Probe.checking () && settled <> read_off_body () then
      Base.Probe.violation "ownership summary"
        Pp.(
          str "the parameters of " ++ Names.GlobRef.print (Option.get owner)
          ++ str " are not owned as their body reads them" );
    settled
  | _ -> read_off_body ()

(** Whether the C++ type [cpp_ty] names a value inductive
    (an inductive neither enum, coinductive nor custom scalar), as itself or through a type
    abbreviation: [Definition t elt := list (key * elt)] declares [t<T2>] an
    alias of [List<std::pair<key, T2>>], a value copied whole as surely as one
    named [List] is. *)
let rec names_value_inductive (cpp_ty : Cpp_ir.Lowered.Type.t) =
  ( match cpp_ty with
  | Entity_application ((GlobRef.IndRef _ as g), _, _) | In_namespace ((GlobRef.IndRef _ as g), _) ->
    (not (Base.Table.is_enum_inductive g)) && (not (Base.Table.is_coinductive g)) && not (Base.Table.is_custom_scalar_ref g)
  | _ -> false )
  ||
  match cpp_ty with
  | Entity_application ((GlobRef.ConstRef kn as r), args, _) when not (Base.Table.is_custom r) -> (
    match Base.Table.lookup_typedef_unchecked kn with
    | Some body -> abbreviates_value_inductive args body
    | None -> false )
  | _ -> false

(* Whether the body [body] of a type abbreviation applied to the C++ types
   [args] is a value inductive ({!names_value_inductive}): a variable of the
   abbreviation stands for the argument written for it. *)
and abbreviates_value_inductive args body =
  match resolve_meta body with
  | Core.Type.Global_app {head = (GlobRef.IndRef _ as r); _} ->
    (not (Base.Table.is_enum_inductive r)) && (not (Base.Table.is_coinductive r)) && not (Base.Table.is_custom_scalar_ref r)
  | Core.Type.Global_app {head = (GlobRef.ConstRef kn as r);
                          type_arguments = inner; _} when not (Base.Table.is_custom r) -> (
    match Base.Table.lookup_typedef_unchecked kn with
    | Some body -> abbreviates_value_inductive args (Base.Core_util.type_subst_list inner body)
    | None -> false )
  | Core.Type.Variable {variable = j; _} when j >= 1 -> (
    match List.nth_opt args (j - 1) with Some t -> names_value_inductive t | None -> false )
  | _ -> false

(* Whether the body [body] of a type abbreviation is a closure: an arrow,
   under the type abstractions erasure removes -- [IFun A B := forall T, A T
   -> B T], an event handler's type -- or an abbreviation of one.  Read off
   the body as written, its variables not substituted, so that the Core and
   the C++ readings of a parameter's type agree. *)
let rec body_is_closure (body : Core.Type.t) =
  match resolve_meta body with
  | Core.Type.Arrow {parameter = d; result = rest} when Base.Core_util.is_erased_type d -> body_is_closure rest
  | Core.Type.Arrow _ -> true
  | Core.Type.Global_app {head = GlobRef.ConstRef kn as r; _} when not (Base.Table.is_custom r) ->
    abbreviates_closure kn
  | _ -> false

(* Whether the type abbreviation [kn] names a closure ({!body_is_closure}). *)
and abbreviates_closure kn =
  match Base.Table.lookup_typedef_unchecked kn with Some body -> body_is_closure body | None -> false

(** Whether a parameter of C++ type [cpp_ty] that its function does not own
    is lent by const reference, read off the C++ type: a [shared_ptr], a
    value inductive (an inductive named through an abbreviation too,
    {!names_value_inductive}), or a template type parameter or dependent
    type, whose size is unknown.

    A closure and a coinductive value are a pointer to a shared block, as a
    [shared_ptr] is: copying one in is a retain, and dropping it at the end
    of the call a release.  Borrowed, they too are passed by const
    reference -- a closure named through an abbreviation too
    ({!abbreviates_closure}). *)
let cpp_lent_by_reference (cpp_ty : Cpp_ir.Lowered.Type.t) =
  let rec shared_block (t : Cpp_ir.Lowered.Type.t) =
    match t with
    | Function _ -> true
    | Non_deduced t | In_namespace (_, t) -> shared_block t
    | Entity_application ((GlobRef.ConstRef kn as r), _, _) when not (Base.Table.is_custom r) ->
      Base.Table.is_coinductive r || abbreviates_closure kn
    | Entity_application (r, _, _) -> Base.Table.is_coinductive r
    | _ -> false
  in
  match cpp_ty with
  | Shared_pointer _ -> true
  | _ when shared_block cpp_ty -> true
  | _ when names_value_inductive cpp_ty -> true
  | Variable _ | Member _ -> true
  | _ -> false

(** Whether a parameter of Core type [ty] that its function does not own is
    lent by const reference, read off the Core type: a value inductive --
    named as itself, or through an abbreviation whose body is one -- a
    closure, a coinductive, a type variable, and a reified interaction tree,
    each a value a copy of which costs a clone or a retain.  [None] where
    the Core type does not say: one nothing determined, an erased or
    promoted type, an abstract one, a type variable applied -- under the
    abstractions over types erasure removes. *)
let rec core_lent_by_reference cx ty =
  match resolve_meta ty with
  | ty when is_monadic_core_type ty && cx.ctx.input.itree_mode = Reified -> Some true
  | Core.Type.Global_app {head = (GlobRef.IndRef _ as r); _} ->
    Some ((not (Base.Table.is_enum_inductive r)) && not (Base.Table.is_custom_scalar_ref r))
  | Core.Type.Global_app {head = (GlobRef.ConstRef kn as r); type_arguments = args; _}
    when (not (Base.Table.is_custom r)) && not (Base.Table.is_promoted_type_var r || Base.Table.is_erased_type_const r) -> (
    (* A closure through an abbreviation is written at whatever the
       abbreviation's C++ spelling is -- the closure, or an erased box where
       its parameters are erased -- so the C++ type decides. *)
    if abbreviates_closure kn then None
    else
    match Base.Table.lookup_typedef_unchecked kn with
    | Some body -> (
      (* As {!names_value_inductive} reads an abbreviation: its body a value
         inductive, or a variable standing for one. *)
      match resolve_meta (Base.Core_util.type_subst_list args body) with
      | Core.Type.Global_app {head = (GlobRef.IndRef _ | GlobRef.ConstRef _); _} as unfolded -> (
        match core_lent_by_reference cx unfolded with
        | Some lent ->
          Some
            (lent && match unfolded with Core.Type.Global_app {head = r; _} -> not (Base.Table.is_coinductive r) | _ -> true)
        | None -> None )
      | _ -> Some false )
    | None -> None )
  | Core.Type.Global_app {head = r; _} when Base.Table.is_custom r -> Some false
  (* A type abstraction erasure removes is no closure: what it returns is
     the value. *)
  | Core.Type.Arrow {parameter = d; result = rest} when Base.Core_util.is_erased_type d -> core_lent_by_reference cx rest
  | Core.Type.Arrow _ | Core.Type.Variable _ -> Some true
  | _ -> None

(** How a parameter of C++ type [cpp_ty] is passed ({!Cpp_ir.Param_mode}),
    and the type it is declared at.  An owned parameter is passed by value
    (the caller moves it in); a borrowed one by const reference where it is
    lent by reference ({!core_lent_by_reference} of its Core type [core]
    where that says, {!cpp_lent_by_reference} otherwise), and by value
    otherwise.  Under [CRANE_CHECK_IR] the two readings are checked against
    each other. *)
let wrap_param_by_ownership cx ?(is_owned = false) ?core (cpp_ty : Cpp_ir.Lowered.Type.t) :
    Cpp_ir.Lowered.Type.t * Cpp_ir.Param_mode.t =
  let by_cpp = cpp_lent_by_reference cpp_ty in
  let lent =
    match Option.bind core (core_lent_by_reference cx) with
    | Some by_core ->
      if Base.Probe.checking () && by_core <> by_cpp then
        Base.Probe.violation "parameter convention"
          Pp.(
            str "the Core type of a parameter says it is "
            ++ str (if by_core then "lent by reference" else "copied")
            ++ str ", its C++ type the other" );
      by_core
    | None -> by_cpp
  in
  let mode = if is_owned then Cpp_ir.Param_mode.owned else if lent then Cpp_ir.Param_mode.lent else Cpp_ir.Param_mode.copied in
  (Cpp_ir.Param_mode.declare mode.form cpp_ty, mode)
