(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which local fixpoints may outlive their scope.  See
    [analyze_closures.mli]. *)


type group = Lifted | In_place | Closures

(* The function an application applies, under any coercion. *)
let callee = Core.Expr.strip_crossings

let arity f = List.length (fst (Base.Core_util.collect_lams f))

(* Whether [use] is a monadic bind generated as sequencing, as the unit's
   effect operations [effects] say. *)
let sequential_bind effects use = Effects.lookup effects use = Some {operation = Bind; mode = Sequential}

let rec group ~effects ~n_outer ?continuation ~cofix ids bodies =
  if Base.Type_util.own_type_variables ~n_outer (List.map snd (Array.to_list ids)) then Lifted
  else if
    escapes_in_bodies ~effects ~n_outer ~cofix bodies || Option.cata (escapes ~effects ~n_outer 1) false continuation
  then Closures
  else In_place

(* Whether the local fixpoint at [k] may outlive its scope as [t] uses it:
   named other than as the function an application applies, or named at all
   inside a closure. *)
and escapes ~effects ~n_outer k t =
  let in_place_group ?continuation ~cofix g =
    group ~effects ~n_outer ?continuation ~cofix (Core.Recursion.Group.functions g)
      (Core.Recursion.Group.bodies g) = In_place
  in
  let rec go k = function
    | Core.Expr.Bound_variable {index = i; _} -> i = k
    | Core.Expr.Apply {callee = f; arguments = args}
      when (match callee f with Core.Expr.Bound_variable {index = i; _} -> i = k | _ -> false) ->
      List.exists (go k) args
    | Core.Expr.Apply {callee = Core.Expr.Fixpoint g; arguments = args}
      when List.length args >= arity (Core.Recursion.Group.selected_member g).body && in_place_group ~cofix:false g ->
      in_place k (Core.Recursion.Group.bodies g) || List.exists (go k) args
    | Core.Expr.Apply {callee = Core.Expr.Cofixpoint g; arguments = args}
      when List.length args >= arity (Core.Recursion.Group.selected_member g).body && in_place_group ~cofix:true g ->
      in_place k (Core.Recursion.Group.bodies g) || List.exists (go k) args
    | Core.Expr.Let {value = Core.Expr.Fixpoint g; body = b; _} when in_place_group ~continuation:b ~cofix:false g ->
      in_place k (Core.Recursion.Group.bodies g) || go (k + 1) b
    | Core.Expr.Let {value = Core.Expr.Cofixpoint g; body = b; _} when in_place_group ~continuation:b ~cofix:true g ->
      in_place k (Core.Recursion.Group.bodies g) || go (k + 1) b
    (* A bind generated as sequencing runs its continuation's body inline. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = (_ :: _ :: _ as args)}
      when sequential_bind effects use -> (
      match List.rev args with
      | continuation :: rest -> (
        List.exists (go k) rest
        ||
        match Base.Core_util.collect_lams continuation with
        | [], _ -> go k continuation
        | ids, body -> go (k + List.length ids) body )
      | [] -> false )
    | Core.Expr.Apply {callee = f; arguments = args} -> go k f || List.exists (go k) args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> go k a
    | Core.Expr.Lambda {body; _} -> Base.Core_util.ast_occurs (k + 1) body
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      Array.exists (Base.Core_util.ast_occurs (k + Array.length ids)) bodies
    | Core.Expr.Let {value = a; body = b; _} -> go k a || go (k + 1) b
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      go k scrut
      || Array.exists
           (fun {Core.Match.Branch.binders = ids; body = body; _} -> go (k + List.length ids) body)
           branches
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.exists (go k) args
    | Core.Expr.Persistent_array {elements = elts; default = def} -> Array.exists (go k) elts || go k def
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ -> false
  (* A group generated in place runs where it is called, and its bodies read
     what they close over there. *)
  and in_place k bodies =
    let n = Array.length bodies in
    Array.exists
      (fun f ->
        let params, body = Base.Core_util.collect_lams f in
        go (k + n + List.length params) body )
      bodies
  in
  go k t

(* Whether a member of the group escapes in a member's own body, which
   stands under its parameters and the group's members, the last innermost.
   A cofixpoint's body is suspended, so any mention of one there does. *)
and escapes_in_bodies ~effects ~n_outer ~cofix bodies =
  let n = Array.length bodies in
  Array.exists
    (fun f ->
      let params, body = Base.Core_util.collect_lams f in
      let k = List.length params in
      List.exists
        (fun j ->
          let member = k + n - j in
          if cofix then Base.Core_util.ast_occurs member body else escapes ~effects ~n_outer member body )
        (List.init n Fun.id) )
    bodies
