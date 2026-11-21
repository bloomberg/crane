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

(** What the function whose [body] stands under [params], innermost first,
    does with each of them ({!Core_plan.Access}): what {!Core_plan.Access}
    settled for the global [owner] where it covers [params], and otherwise
    -- a lambda, a local function -- what its own body reads. *)
let infer_access cx ?owner body params =
  match Option.bind owner (own_access cx) with
  | Some settled when List.length settled = List.length params -> settled
  | _ -> Core_plan.Access.read_off ~settled:(settled_access cx) (List.length params) body

(** The typed mapping of the parameter type [core] or [cpp_ty], if it is a
    typed-mapped type. *)
let mapped_plan ?core (cpp_ty : Cpp_ir.Lowered.Type.t) =
  match Option.map resolve_meta core with
  | Some (Core.Type.Global_app {head = r; _}) when Base.Mapping_plan.is_type_head r -> Some (Base.Mapping_plan.find r)
  | Some _ -> None
  | None -> (
    match cpp_ty with
    | Entity_application (r, _, _) | In_namespace (_, Entity_application (r, _, _))
      when Base.Mapping_plan.is_type_head r ->
      Some (Base.Mapping_plan.find r)
    | _ -> None )

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
  (* A typed-mapped type is lent as its canonical read style says
     ({!Base.Mapping_plan.read_by_value}).  A component is read by value
     only when copying it is known to be free: one whose cost is unknown --
     a functor's abstract [A.t], which may be a list -- or one that costs a
     clone or a retain makes a [ReadByComponents] value lent. *)
  | Entity_application (r, ts, _) | In_namespace (_, Entity_application (r, ts, _))
    when Base.Mapping_plan.is_type_head r ->
    not
      (Base.Mapping_plan.read_by_value (Base.Mapping_plan.find r) ~argument:(fun i ->
           match List.nth_opt ts i with Some t -> is_trivially_copyable_type t | None -> false))
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
  (* A typed-mapped type: its canonical read style, where the Core type of
     each argument it depends on says whether that argument is read by
     value -- only when copying it is known to be free, as
     {!cpp_lent_by_reference} reads it.  An argument the Core type does not
     determine leaves the C++ type to decide. *)
  | Core.Type.Global_app {head = r; type_arguments = args; _} when Base.Mapping_plan.is_type_head r -> (
    let undetermined = ref false in
    let argument i =
      match List.nth_opt args i with
      | Some t when Option.has_some (core_lent_by_reference cx t) -> core_is_trivially_copyable t
      | _ ->
        undetermined := true;
        false
    in
    let by_value = Base.Mapping_plan.read_by_value (Base.Mapping_plan.find r) ~argument in
    if !undetermined then None else Some (not by_value) )
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
    each other.

    A borrowed parameter of a typed-mapped type whose [access]
    ({!Core_plan.Access}) asks for more than a read takes the form its
    access model gives that access (design 6.6, 12.5): [T&] to replace it or
    to write a mutable value in place, the model's write-through form to
    write through a handle.  Where [reference_allowed] is false -- a
    function named as a value, a method -- a mutable reference is a copy by
    value instead.  Where [view_allowed], a [Preferred] read or write takes
    the mapping's read or writable view (design 12.5), declared at the view
    type. *)
let rec wrap_param_by_ownership cx ?(is_owned = false) ?access ?(reference_allowed = false) ?(view_allowed = false)
    ?core (cpp_ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t * Cpp_ir.Param_mode.t =
  (* A borrowed parameter of a typed-mapped type takes the form its access
     requires (design 12.5), where that is not the canonical read form. *)
  let plan = mapped_plan ?core cpp_ty in
  let physical =
    match (is_owned, access, plan) with
    | false, Some r, Some p -> Core_plan.Access.physical ~reference_allowed ~view_allowed p r
    | _ -> Base.Mapping_plan.As_read
  in
  (* A view is declared at the view type, at the mapped type's arguments. *)
  let mapped_arguments =
    match cpp_ty with
    | Entity_application (r, tys, _) | In_namespace (_, Entity_application (r, tys, _))
      when Base.Mapping_plan.is_type_head r ->
      Some tys
    | _ -> None
  in
  let physical =
    match (physical, mapped_arguments) with
    | Base.Mapping_plan.Physical_view _, None -> Base.Mapping_plan.As_read
    | physical, _ -> physical
  in
  let invalidates = match access with Some (r : Core_plan.Access.requirement) -> r.invalidates | None -> false in
  let ty, mode =
  match physical with
  | Base.Mapping_plan.Physical_view k ->
    let view : Cpp_ir.Param_mode.view =
      match k with Base.Mapping_plan.Read_view -> Read_view | Base.Mapping_plan.Write_view -> Write_view
    in
    let plan = Option.get plan in
    ( Base.Mapping_plan.view_type plan k (Option.get mapped_arguments),
      Cpp_ir.Param_mode.make Borrowed (By_view (view, plan.head)) )
  | Base.Mapping_plan.Physical_value -> (cpp_ty, Cpp_ir.Param_mode.copied)
  | Base.Mapping_plan.Physical_const_reference ->
    (Cpp_ir.Param_mode.declare By_const_reference cpp_ty, Cpp_ir.Param_mode.lent)
  | Base.Mapping_plan.Physical_mutable_reference ->
    (Cpp_ir.Param_mode.declare By_reference cpp_ty, Cpp_ir.Param_mode.make Borrowed By_reference)
  | Base.Mapping_plan.As_read -> wrap_canonical cx ~is_owned ?core cpp_ty
  in
  (ty, if invalidates then {mode with Cpp_ir.Param_mode.invalidates_views = true} else mode)

and wrap_canonical cx ~is_owned ?core (cpp_ty : Cpp_ir.Lowered.Type.t) =
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
