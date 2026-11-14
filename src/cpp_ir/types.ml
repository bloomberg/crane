(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Rewriting and searching types, at either phase.  A [decltype]'s
    expression is never entered: it is an expression, and a rewrite of the
    code around it reaches it there. *)

open Grammar

(** Whether [t] is written as the erased box [crane::obj]: the erased types,
    and a lowered type whose representation is not yet known. *)
let prints_as_any : type p. p Type.t -> bool = function
  | Any | Erased _ | Obligation Opaque_type -> true
  | _ -> false

(** [rewrite f t]: where [f] answers, its answer replaces the node and is
    not descended into; elsewhere the node is rebuilt from its rewritten
    children exactly as it was -- no application is renormalised, and a type
    constructor's head is reached like any other child. *)
let rec rewrite : type p. (p Type.t -> p Type.t option) -> p Type.t -> p Type.t =
 fun f t ->
  match f t with
  | Some t -> t
  | None -> (
    let go = rewrite f in
    match t with
    | Entity_application (r, tys, args) -> Entity_application (r, List.map go tys, args)
    | Foreign fr -> Foreign {fr with types = List.map go fr.types}
    | Named (id, tys) -> Named (id, List.map go tys)
    | External (id, tys) -> External (id, List.map go tys)
    | Function (dom, cod) -> Function (List.map go dom, go cod)
    | Const t -> Const (go t)
    | Shared_pointer t -> Shared_pointer (go t)
    | Reference (k, t) -> Reference (k, go t)
    | Pointer t -> Pointer (go t)
    | Variant (k, ts) -> Variant (k, List.map go ts)
    | In_namespace (r, t) -> In_namespace (r, go t)
    | Member (t, id) -> Member (go t, id)
    | Apply (h, ts) -> Apply (go h, List.map go ts)
    | Decay t -> Decay (go t)
    | Non_deduced t -> Non_deduced (go t)
    | Rebind (h, x) -> Rebind (go h, go x)
    | Type_constructor t -> Type_constructor (go t)
    | Type_of _ | Decltype_auto | Variable _ | Instance _ | Promoted_member _ | Void | Any | Auto | Carrier_parameter
    | Erased _ | Obligation _ ->
      t )

(** [rebind_applied_head h args] is [h], an instantiated carrier standing
    for a family written applied, read at [args]: each erased leaf inside it
    is the one argument, unless that argument is erased itself or there is
    not exactly one.  A family's own struct keeps its erased index. *)
let rebind_applied_head : type p. p Type.t -> p Type.t list -> p Type.t =
 fun h args ->
  match args with
  | [a] when not (prints_as_any a) -> (
    let family = Tparam_kinds.has_family in
    let rec sub (t : p Type.t) : p Type.t =
      match t with
      | Any | Obligation Opaque_type -> a
      | Entity_application (r, _, _) when family r -> t
      | Entity_application (r, tys, es) -> Entity_application (r, List.map sub tys, es)
      | Named (id, tys) -> Named (id, List.map sub tys)
      | External (id, tys) -> External (id, List.map sub tys)
      | Non_deduced t -> Non_deduced (sub t)
      | Rebind (h, x) -> Rebind (sub h, sub x)
      | Reference (Forwarding, t) -> Reference (Forwarding, sub t)
      | In_namespace (r, t) -> In_namespace (r, sub t)
      | Const t -> Const (sub t)
      | Function (d, c) -> Function (List.map sub d, sub c)
      | Shared_pointer t -> Shared_pointer (sub t)
      | t -> t
    in
    match h with
    | (Entity_application (r, _, _) | In_namespace (_, Entity_application (r, _, _))) when family r -> h
    | Entity_application (r, tys, es) -> Entity_application (r, List.map sub tys, es)
    | In_namespace (r, Entity_application (g, tys, es)) -> In_namespace (r, Entity_application (g, List.map sub tys, es))
    | h -> h )
  | _ -> h

(** [map f t] applies [f] to every type in [t], outermost first, not
    entering a type constructor: an application whose head becomes erased is
    erased, and one whose head becomes an instantiated template is that
    template read at the argument ({!rebind_applied_head}). *)
let rec map : type p. (p Type.t -> p Type.t) -> p Type.t -> p Type.t =
 fun f t ->
  let go = map f in
  let t = f t in
  match t with
  | Entity_application (r, tys, args) -> Entity_application (r, List.map go tys, args)
  | Foreign fr -> Foreign {fr with types = List.map go fr.types}
  | Named (id, tys) -> Named (id, List.map go tys)
  | External (id, tys) -> External (id, List.map go tys)
  | Function (dom, cod) -> Function (List.map go dom, go cod)
  | Const t -> Const (go t)
  | Shared_pointer t -> Shared_pointer (go t)
  | Reference (k, t) -> Reference (k, go t)
  | Pointer t -> Pointer (go t)
  | Variant (k, ts) -> Variant (k, List.map go ts)
  | In_namespace (r, t) -> In_namespace (r, go t)
  | Member (t, id) -> Member (go t, id)
  | Apply (h, ts) -> (
    let rec applied_head (h : p Type.t) =
      match h with Entity_application (_, _ :: _, _) -> true | In_namespace (_, h) -> applied_head h | _ -> false
    in
    match go h with
    | h when match h with Type_constructor h' -> prints_as_any h' | h' -> prints_as_any h' -> Any
    | h when applied_head h -> rebind_applied_head h (List.map go ts)
    | h -> Apply (h, List.map go ts) )
  | Decay t -> Decay (go t)
  | Non_deduced t -> Non_deduced (go t)
  | Rebind (h, x) -> Rebind (go h, go x)
  | Type_of _ | Decltype_auto | Type_constructor _ | Variable _ | Instance _ | Promoted_member _ | Void | Any | Auto
  | Carrier_parameter | Erased _ | Obligation _ ->
    t

(** [apply h args] is [h] applied to [args] where a substitution puts [h] in
    head position: an erased head erases the application, an instantiated
    template is read at the argument ({!rebind_applied_head}), and a type
    constructor whose body names its {!Type.Carrier_parameter} is that body
    with the argument in its place. *)
let apply : type p. p Type.t -> p Type.t list -> p Type.t =
 fun h args ->
  let rec applied_head (h : p Type.t) =
    match h with Entity_application (_, _ :: _, _) -> true | In_namespace (_, h) -> applied_head h | _ -> false
  in
  let erased_head = match h with Type_constructor h' -> prints_as_any h' | h' -> prints_as_any h' in
  match (h, args) with
  | _ when erased_head -> Any
  | h, _ when applied_head h -> rebind_applied_head h args
  | Type_constructor body, [arg] ->
    let fired = ref false in
    let reduced =
      map
        (fun (t : p Type.t) ->
          match t with
          | Carrier_parameter ->
            fired := true;
            arg
          | t -> t )
        body
    in
    if !fired then reduced else Apply (h, args)
  | _ -> Apply (h, args)

(** [substitute sub t] replaces each numbered type variable [i] of [t] for
    which [sub] answers, reaching inside a type constructor -- replacing one
    template name with another leaves it printable -- and not inside a
    [decltype].  An application whose head was substituted is rebuilt by
    {!apply}: that is where a higher-kinded parameter's carrier arrives. *)
let rec substitute : type p. (int -> p Type.t option) -> p Type.t -> p Type.t =
 fun sub t ->
  let go = substitute sub in
  match t with
  | Variable (Index (i, _)) -> ( match sub i with Some t' -> t' | None -> t )
  | Entity_application (r, tys, args) -> Entity_application (r, List.map go tys, args)
  | Foreign fr -> Foreign {fr with types = List.map go fr.types}
  | Named (id, tys) -> Named (id, List.map go tys)
  | External (id, tys) -> External (id, List.map go tys)
  | Function (dom, cod) -> Function (List.map go dom, go cod)
  | Const t -> Const (go t)
  | Shared_pointer t -> Shared_pointer (go t)
  | Reference (k, t) -> Reference (k, go t)
  | Pointer t -> Pointer (go t)
  | Variant (k, ts) -> Variant (k, List.map go ts)
  | In_namespace (r, t) -> In_namespace (r, go t)
  | Member (t, id) -> Member (go t, id)
  | Apply (h, ts) -> apply (go h) (List.map go ts)
  | Decay t -> Decay (go t)
  | Non_deduced t -> Non_deduced (go t)
  | Rebind (h, x) -> Rebind (go h, go x)
  | Type_constructor t -> Type_constructor (go t)
  | Type_of _ | Decltype_auto | Variable (Named _) | Instance _ | Promoted_member _ | Void | Any | Auto
  | Carrier_parameter | Erased _ | Obligation _ ->
    t

(** The site a function type stands at, which decides how its chain of
    arrows is spelled: flat where a declaration writes it
    ([crane::fn<R(A, B)>]), curried where a type variable stands for it
    ([crane::fn<crane::fn<R(B)>(A)>]), or flat for the first [n] parameters
    a declaration wrote and curried for the rest.  [Declared_at 0] is
    [Through_tvar]. *)
type arrow_site = Declared | Through_tvar | Declared_at of int

(** [spell_arrows site t] respells every function type in [t] as [site]
    spells it. *)
let rec spell_arrows : type p. arrow_site -> p Type.t -> p Type.t =
 fun site t ->
  match site with
  | Declared -> t
  | Through_tvar | Declared_at 0 ->
    map
      (fun (t : p Type.t) ->
        match t with
        | Function (a :: (_ :: _ as rest), cod) -> Function ([a], Function (rest, cod))
        | t -> t )
      t
  | Declared_at n -> (
    match t with
    | Function (dom, cod) when List.length dom > n ->
      let outer = List.filteri (fun i _ -> i < n) dom in
      let inner = List.filteri (fun i _ -> i >= n) dom in
      Function (outer, spell_arrows Through_tvar (Function (inner, cod)))
    | _ -> t )

(** Whether [p] holds of [t] or of a type inside it.  Unlike {!map}, this
    looks inside a [Type_constructor]: only its head is printed, but the head
    is printed, so it mentions whatever names it. *)
let rec exists : type p. (p Type.t -> bool) -> p Type.t -> bool =
 fun p t ->
  p t
  ||
  match t with
  | Entity_application (_, tys, _) | Named (_, tys) | External (_, tys) | Variant (_, tys) -> List.exists (exists p) tys
  | Foreign fr -> List.exists (exists p) fr.types
  | Function (dom, cod) -> List.exists (exists p) dom || exists p cod
  | Const t | Shared_pointer t | Reference (_, t) | Pointer t | In_namespace (_, t) | Member (t, _) | Decay t
  | Non_deduced t | Type_constructor t ->
    exists p t
  | Type_of _ | Decltype_auto -> false
  | Rebind (h, x) -> exists p h || exists p x
  | Apply (t, ts) -> exists p t || List.exists (exists p) ts
  | Variable _ | Instance _ | Promoted_member _ | Void | Any | Auto | Carrier_parameter | Erased _ | Obligation _ ->
    false

(** Whether [a] and [b] are one type once every arrow chain in each is spelled
    curried, as a type variable spells it. *)
let same_arrows a b = spell_arrows Through_tvar a = spell_arrows Through_tvar b

(** [t] respelled as [site] spells its arrows, or [None] where that
    changes nothing. *)
let respell_arrows site t =
  let spelled = spell_arrows site t in
  if spelled = t then None else Some spelled

(** Every type variable [t] names, under the name each is written. *)
let variable_names t =
  let acc = ref Names.Id.Set.empty in
  ignore
    (exists
       (fun t ->
         (match t with
          | Variable (Index (_, Some n) | Named n) -> acc := Names.Id.Set.add n !acc
          | Variable (Index (i, None)) -> acc := Names.Id.Set.add (Core.Positional.id i) !acc
          | _ -> ());
         false )
       t );
  !acc

(** [t] without the spelling a parameter declaration adds: a reference,
    [const], or [std::type_identity_t]. *)
let rec strip_param_spelling : type p. p Type.t -> p Type.t = function
  | Non_deduced t | Const t | Reference (_, t) -> strip_param_spelling t
  | t -> t
