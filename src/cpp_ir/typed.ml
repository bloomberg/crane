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
let not_yet : Lowered.Value_type.t = Deduced Not_yet_typed
let untyped expr = {expr; ty = not_yet}

(** The grouping a lambda's own type has: its parameters, then those of the
    lambda it returns, if its body is only that, and so on; [None] where its
    result is not written. *)
let generic (l : lowered Lambda.t) =
  l.type_params <> [] || List.exists (fun ((t : Lowered.Type.t), _) -> Types_.exists (fun t -> t = Auto) t) l.params

let rec closure_arrows (l : lowered Lambda.t) : Lowered.Arrows.t option =
  let group = List.map fst l.params in
  match (l.return_type, l.body) with
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
      match node_type e with
      | Typed t -> types := t :: !types
      | Never -> ()
      | _ -> unknown := true )
    | Return None -> unknown := true
    | s -> Subterms.stmt ~expr:(fun _ -> ()) ~stmts:(List.iter stmt) s
  in
  List.iter stmt body;
  match !types with
  | t :: rest when (not !unknown) && List.for_all (( = ) t) rest -> Some t
  | _ -> None

and node_type : Lowered.Expr.t -> Lowered.Value_type.t = function
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
    Typed t
  | Call (_, Lambda ({params = []; _} as l), []) when not (generic l) -> (
    match closure_arrows l with Some {groups = [[]]; result} -> Typed result | _ -> not_yet )
  | Abort _ -> Never
  | Foreign_text _ -> Deduced Foreign_text
  | Runtime h -> Deduced (Runtime_helper h)
  | Requires _ | Concept_application _ | Convertible_to _ -> Deduced Requirement
  | Move e | Forward (_, e) -> node_type e
  | Function_value e -> (
    match node_type e with
    | Closure a | Function_name (_, a) -> Typed (Arrows_.to_type a)
    | Typed (Function _) as t -> t
    | _ -> not_yet )
  | Erase_callable (Boxed_whole, _) | Erased_call _ -> Typed Any
  | Erase_callable (At_signature cod, e) -> (
    match Value_type_.arrows (node_type e) with
    | Some a -> Typed (Function (List.map (fun _ -> Type.Any) (List.concat a.groups), cod))
    | None -> not_yet )
  | Lambda l when generic l -> Deduced Generic_lambda
  | Lambda l -> ( match closure_arrows l with Some a -> Closure a | None -> not_yet )
  | _ -> not_yet

let of_node expr = {expr; ty = node_type expr}
let rewrap f x = {x with expr = f x.expr}
let or_type ty x = if Value_type_.not_yet_typed x.ty then {x with ty} else x

let rec const_type : Lowered.Type.t -> bool = function
  | Const _ -> true
  | Reference (_, t) | In_namespace (_, t) -> const_type t
  | _ -> false

let category x : Value_category.t =
  match x.expr with
  | Local _ -> ( match x.ty with Typed t when const_type t -> Const_lvalue | _ -> Mutable_lvalue )
  | Move _ -> Xvalue
  | _ -> Prvalue
