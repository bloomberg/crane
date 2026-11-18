(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which local fixpoints may outlive their scope.  See
    [closures.mli]. *)


type group = Lifted | In_place | Closures

type suspends_constructor =
  binder_type:(int -> Core.Type.t option) -> Names.GlobRef.t -> Core.Expr.t list -> bool

(* The function an application applies, under any coercion. *)
let callee = Core.Expr.strip_crossings

let arity f = List.length (fst (Base.Core_util.collect_lams f))

(* Whether [use] is a monadic bind generated as sequencing, as the unit's
   effect operations [effects] say. *)
let sequential_bind effects use = Effects.lookup effects use = Some {operation = Bind; mode = Sequential}

(* [lex] under the binders [ids], (name, type) pairs innermost first. *)
let push ids lex =
  Core.Lexenv.push
    (List.map
       (fun (x, ty) -> {Core.Lexenv.id = Base.Core_util.id_of_binder_name x; type_ = ty; role = Core.Lexenv.Value})
       ids )
    lex

(* [lex] under the members [ids] of a group, the last innermost. *)
let push_members ids lex =
  push (List.rev_map (fun (g, ty) -> (Core.Binder_name.Source g, ty)) (Array.to_list ids)) lex

(* [lex] under the parameters [params] of a member, innermost first, as
   {!Base.Core_util.collect_lams} has them. *)
let push_params params lex = push params lex

(* The constructor a term builds, where a suspension may hold its
   arguments: a coinductive one not mapped to custom code, of the inductive
   it heads. *)
let construction = function
  | Core.Expr.Construct {result_type = Core.Type.Global_app {head = n; _}; constructor = c; arguments = args; _}
    when not (Base.Table.is_custom c) ->
    Some (n, args)
  | _ -> None

(* [f ~tail e] for [e] and the terms in the tail of [e] that statements
   hand on to the same continuation: the body of a let, the branches of a
   match, the continuation of a bind generated as sequencing. *)
let rec tails ~effects f e =
  f e;
  match e with
  | Core.Expr.Let {body = b; _} -> tails ~effects f b
  | Core.Expr.Match {branches; _} ->
    Array.iter (fun {Core.Match.Branch.body = b; _} -> tails ~effects f b) branches
  | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = _ :: _ :: _ as args} when sequential_bind effects use
    -> (
    match List.rev args with
    | continuation :: _ -> tails ~effects f (snd (Base.Core_util.collect_lams continuation))
    | [] -> () )
  | _ -> ()

let suspended_tail ~effects body =
  let found = ref [] in
  tails ~effects
    (function
      | Core.Expr.Let {value = Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g; _}
      | Core.Expr.Apply {callee = Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g; _} ->
        found := g.occurrence :: !found
      | _ -> () )
    body;
  !found

let rec group ~effects ~n_outer ~suspends ~lex ~suspended ?continuation ~cofix ids bodies =
  if Base.Type_util.own_type_variables ~n_outer (List.map snd (Array.to_list ids)) then Lifted
  else if
    escapes_in_bodies ~effects ~n_outer ~suspends ~lex ~cofix ids bodies
    ||
    match continuation with
    | Some (binder, b) -> escapes ~effects ~n_outer ~suspends ~tail:suspended (push [binder] lex) 1 b
    | None -> suspended
  then Closures
  else In_place

(* Whether the local fixpoint at [k] may outlive its scope as [t], standing
   in [lex], uses it: named other than as the function an application
   applies, or named at all inside a closure -- a lambda, a group not
   generated in place, the thunk suspending a coinductive constructor's
   arguments -- or, where [tail] says the continuation [t] hands its value
   to suspends it whole, in that value. *)
and escapes ~effects ~n_outer ~suspends ~tail lex k t =
  let in_place_group ~lex ~suspended ?continuation ~cofix g =
    group ~effects ~n_outer ~suspends ~lex ~suspended ?continuation ~cofix (Core.Recursion.Group.functions g)
      (Core.Recursion.Group.bodies g) = In_place
  in
  (* [tail]: whether [t] is in the tail of the continuation, which is
     suspended whole; what stands there runs in the thunk. *)
  let rec go ~tail lex k t =
    match t with
    | Core.Expr.Bound_variable {index = i; _} -> i = k
    | Core.Expr.Let {binder = x; binder_type = ty; value = Core.Expr.Fixpoint g; body = b; _}
      when in_place_group ~lex ~suspended:tail ~continuation:((x, ty), b) ~cofix:false g ->
      in_place lex k g || go ~tail (push [(x, ty)] lex) (k + 1) b
    | Core.Expr.Let {binder = x; binder_type = ty; value = Core.Expr.Cofixpoint g; body = b; _}
      when in_place_group ~lex ~suspended:tail ~continuation:((x, ty), b) ~cofix:true g ->
      in_place lex k g || go ~tail (push [(x, ty)] lex) (k + 1) b
    | Core.Expr.Let {binder = x; binder_type = ty; value = a; body = b; _} ->
      go ~tail:false lex k a || go ~tail (push [(x, ty)] lex) (k + 1) b
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      go ~tail:false lex k scrut
      || Array.exists
           (fun {Core.Match.Branch.binders = ids; body = body; _} ->
             go ~tail (push (List.rev ids) lex) (k + List.length ids) body )
           branches
    (* A bind generated as sequencing runs its continuation's body inline. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = (_ :: _ :: _ as args)}
      when sequential_bind effects use -> (
      match List.rev args with
      | continuation :: rest -> (
        List.exists (go ~tail:false lex k) rest
        ||
        match Base.Core_util.collect_lams continuation with
        | [], _ -> go ~tail lex k continuation
        | ids, body -> go ~tail (push ids lex) (k + List.length ids) body )
      | [] -> false )
    | _ when tail -> Base.Core_util.ast_occurs k t
    | Core.Expr.Apply {callee = f; arguments = args}
      when (match callee f with Core.Expr.Bound_variable {index = i; _} -> i = k | _ -> false) ->
      List.exists (go ~tail lex k) args
    | Core.Expr.Apply {callee = Core.Expr.Fixpoint g; arguments = args}
      when List.length args >= arity (Core.Recursion.Group.selected_member g).body
           && in_place_group ~lex ~suspended:false ~cofix:false g ->
      in_place lex k g || List.exists (go ~tail lex k) args
    | Core.Expr.Apply {callee = Core.Expr.Cofixpoint g; arguments = args}
      when List.length args >= arity (Core.Recursion.Group.selected_member g).body
           && in_place_group ~lex ~suspended:false ~cofix:true g ->
      in_place lex k g || List.exists (go ~tail lex k) args
    | Core.Expr.Apply {callee = f; arguments = args} -> go ~tail lex k f || List.exists (go ~tail lex k) args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> go ~tail lex k a
    | Core.Expr.Lambda {body; _} -> Base.Core_util.ast_occurs (k + 1) body
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      Array.exists (Base.Core_util.ast_occurs (k + Array.length ids)) bodies
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> (
      match construction t with
      | Some (n, args) when suspends ~binder_type:(Core.Lexenv.type_opt lex) n args ->
        List.exists (Base.Core_util.ast_occurs k) args
      | _ -> List.exists (go ~tail lex k) args )
    | Core.Expr.Persistent_array {elements = elts; default = def} ->
      Array.exists (go ~tail lex k) elts || go ~tail lex k def
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
  and in_place lex k g =
    let ids = Core.Recursion.Group.functions g in
    let n = Array.length ids in
    let lex = push_members ids lex in
    Array.exists
      (fun f ->
        let params, body = Base.Core_util.collect_lams f in
        go ~tail:false (push_params params lex) (k + n + List.length params) body )
      (Core.Recursion.Group.bodies g)
  in
  go ~tail lex k t

(* Whether a member of the group escapes in a member's own body, which
   stands under its parameters and the group's members, the last innermost.
   A cofixpoint's body is suspended, so any mention of one there does. *)
and escapes_in_bodies ~effects ~n_outer ~suspends ~lex ~cofix ids bodies =
  let n = Array.length bodies in
  let lex = push_members ids lex in
  Array.exists
    (fun f ->
      let params, body = Base.Core_util.collect_lams f in
      let k = List.length params in
      let lex = push_params params lex in
      List.exists
        (fun j ->
          let member = k + n - j in
          if cofix then Base.Core_util.ast_occurs member body
          else escapes ~effects ~n_outer ~suspends ~tail:false lex member body )
        (List.init n Fun.id) )
    bodies
