(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

module Arrows_ = Arrows
module Value_type_ = Value_type
module Types_ = Types
open Grammar

type t = {
  expr : Lowered.Expr.t;
  ty : Lowered.Value_type.t;
}

let v ~ty expr = {expr; ty}
let typed t expr = {expr; ty = Typed t}
let unannotated : Lowered.Value_type.t = Deduced Unannotated

(** The grouping a lambda's own type has: its parameters, then those of the
    lambda it returns, if its body is only that, and so on; [None] where its
    result is not written. *)
let expansion : (Lowered.Coercion.plan -> Lowered.Expr.t -> Lowered.Expr.t) ref = ref (fun _ e -> e)

let rec head (e : Lowered.Expr.t) : Lowered.Expr.t =
  match e with Coerce (c, e) -> !expansion c.plan (head e) | e -> e

let generic (l : lowered Lambda.t) =
  l.type_params <> [] || List.exists (fun ((t : Lowered.Type.t), _) -> Types_.exists (fun t -> t = Auto) t) l.params

let rec closure_arrows (l : lowered Lambda.t) : Lowered.Arrows.t option =
  let group = List.map fst l.params in
  let body : Lowered.Stmt.t list = match l.body with [Return (Some e)] -> [Return (Some (head e))] | body -> body in
  match (l.return_type, body) with
  | Some result, _ -> Some {groups = [group]; result}
  | None, [Return (Some (Lambda inner))] when inner.type_params = [] ->
    Option.map (fun (a : Lowered.Arrows.t) -> {a with groups = group :: a.groups}) (closure_arrows inner)
  | None, body -> Option.map (fun result : Lowered.Arrows.t -> {groups = [group]; result}) (joined_returns body)

(** The type C++ deduces for a lambda's result from its [body]: the one
    nameable type every [return] at its own level has, an abort fitting any;
    [None] where a return's type is not read off its node, or two differ. *)
and joined_returns body : Lowered.Type.t option =
  let types = ref [] and unknown = ref false in
  let rec stmt (s : Lowered.Stmt.t) =
    match s with
    | Return (Some e) -> (
      match carried e with
      | Some (Typed t) -> types := t :: !types
      | Some Never -> ()
      | _ -> unknown := true )
    | Return None -> unknown := true
    | s -> Subterms.stmt ~expr:(fun _ -> ()) ~stmts:(List.iter stmt) s
  in
  List.iter stmt body;
  match !types with
  | t :: rest when (not !unknown) && List.for_all (( = ) t) rest -> Some t
  | _ -> None

and carried : Lowered.Expr.t -> Lowered.Value_type.t option = fun e ->
  match e with
  | Converting_construct (t, _)
  | Box (t, _)
  | Any_cast (t, _)
  | Tolerant_any_cast (t, _)
  | Convert (t, _)
  | Container_cast (t, _, _)
  | Baked_value (t, _)
  | Unbox ((To t | Or_keep t | List (t, _)), _)
  | Call ({yields = Yields t; _}, _, _)
  | Call (_, Lambda {params = []; return_type = Some t; _}, []) ->
    Some (Typed t)
  | Call (_, Lambda ({params = []; _} as l), []) when not (generic l) -> (
    match closure_arrows l with Some {groups = [[]]; result} -> Some (Typed result) | _ -> None )
  | Abort _ -> Some Never
  | Foreign_text _ -> Some (Deduced Foreign_text)
  | Runtime h -> Some (Deduced (Runtime_helper h))
  | Requires _ | Concept_application _ | Convertible_to _ -> Some (Deduced Requirement)
  | Move e | Forward (_, e) -> carried e
  | Function_value e -> (
    match carried e with
    | Some (Closure a | Function_name (_, a)) -> Some (Typed (Arrows_.to_type a))
    | Some (Typed (Function _)) as t -> t
    | _ -> None )
  | Erase_callable (Boxed_whole, _) | Erased_call _ -> Some (Typed Any)
  | Erase_callable (At_signature cod, e) ->
    Option.map
      (fun (a : Lowered.Arrows.t) -> Value_type_.Typed (Function (List.map (fun _ -> Type.Any) (List.concat a.groups), cod)))
      (Option.bind (carried e) Value_type_.arrows)
  | Coerce _ -> carried (head e)
  | Lambda l when generic l -> Some (Deduced Generic_lambda)
  | Lambda l -> Option.map (fun a -> Value_type_.Closure a) (closure_arrows l)
  | _ -> None

let of_node ~fallback expr = {expr; ty = Option.default fallback (carried expr)}
let rewrap f x = {x with expr = f x.expr}

(** The type left once [groups] of a callable returning [result] are still
    to come: [result] itself where none is. *)
let rest_type groups result : Lowered.Type.t =
  match groups with [] -> result | groups -> Arrows_.to_type {groups; result}

let applied (f : Lowered.Value_type.t) n : Lowered.Value_type.t option =
  let rec take (groups : Lowered.Type.t list list) result n : Lowered.Type.t option =
    match groups with
    | _ when n = 0 -> Some (rest_type groups result)
    | g :: rest when List.length g <= n -> take rest result (n - List.length g)
    | g :: rest -> Some (rest_type (List.filteri (fun i _ -> i >= n) g :: rest) result)
    | [] -> ( match Arrows_.of_type result with Some a -> take a.groups a.result n | None -> None )
  in
  Option.map (fun t -> Value_type_.Typed t) (Option.bind (Value_type_.arrows f) (fun a -> take a.groups a.result n))

let apply ?first ?(prefix = "_sat") f args =
  let rec go (call : Lowered.Expr.t list -> Lowered.Expr.t) ~pending (ty : Lowered.Value_type.t) fe args =
    if args = [] && not pending then {expr = fe; ty}
    else
      match Value_type_.arrows ty with
      | Some {groups = g :: rest; result} ->
        let n = List.length g and given = List.length args in
        if given >= n then
          let e = call (List.filteri (fun i _ -> i < n) args) in
          go (Build.call e) ~pending:false (Typed (rest_type rest result)) e (List.filteri (fun i _ -> i >= n) args)
        else
          let waiting =
            List.mapi
              (fun i t -> (t, Some (Names.Id.of_string (Printf.sprintf "%s%d" prefix i))))
              (List.filteri (fun i _ -> i >= given) g)
          in
          let body = call (args @ List.map (fun (_, id) : Lowered.Expr.t -> Local (Option.get id)) waiting) in
          { expr = Build.lambda waiting None [Return (Some body)] ~capture:Stored;
            ty = Closure {groups = [List.map fst waiting]; result = rest_type rest result} }
      | _ -> {expr = call args; ty = unannotated}
  in
  let call, pending = match first with Some c -> (c, true) | None -> (Build.call f.expr, false) in
  go call ~pending f.ty f.expr args

let rec const_type : Lowered.Type.t -> bool = function
  | Const _ -> true
  | Reference (_, t) | In_namespace (_, t) -> const_type t
  | _ -> false

let category x : Value_category.t =
  match x.expr with
  | Local _ -> ( match x.ty with Typed t when const_type t -> Const_lvalue | _ -> Mutable_lvalue )
  | Move _ -> Xvalue
  | _ -> Prvalue
