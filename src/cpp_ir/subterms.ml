(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** One level of descent into the code a term holds: its expressions, and
    its statement lists as lists, so that a visitor threading a scope
    through a block sees the block whole.  Types are not visited.

    The order is fixed and some visitors depend on it: a call's callee, then
    its arguments last first; of a requires expression, the expressions it
    constrains and not the constraints; any other children in the order they
    are written. *)

open Grammar

(** The expressions and statement lists an expression holds directly. *)
let expr : type p. expr:(p Expr.t -> unit) -> stmts:(p Stmt.t list -> unit) -> p Expr.t -> unit =
 fun ~expr ~stmts e ->
  let each = List.iter expr in
  match e with
  | Local _ | Entity _ | Method_value _ | Projection_value _ | Allocate _ | Literal _ | Convertible_to _ | Abort _
  | Enum_value _ | In_place | In_place_index _ | Holds_alternative _ | Declval _ | Type_name _ | Type_member _
  | Numeral _ | Foreign_text _ | Runtime _ | Concept_application _ | This | Shared_from_this _ ->
    ()
  | Call (_, f, args) ->
    expr f;
    each (List.rev args)
  | Erased_call (f, a) ->
    expr f;
    expr a
  | Tolerant_call (f, args) ->
    expr f;
    each args
  | Converting_construct (_, args) -> each args
  | Box (_, e)
  | Dereference e
  | Move e
  | Forward (_, e)
  | Member (e, _)
  | Project (e, _, _)
  | Access (_, e, _)
  | Scope (e, _, _)
  | Any_cast (_, e)
  | Tolerant_any_cast (_, e)
  | Convert (_, e)
  | Unbox (_, e)
  | Container_cast (_, e, _)
  | Erase_callable (_, e)
  | Function_value e
  | Unary (_, e)
  | Variant_get_if (_, e) ->
    expr e
  | Suspend (_, e) -> expr e
  | Lambda l -> stmts l.body
  | Aggregate a -> each a.values
  | Local_aggregate a -> each a.values
  | Persistent_array (es, d) ->
    Array.iter expr es;
    expr d
  | Access_call (_, o, _, args) ->
    expr o;
    each args
  | Method_call m ->
    expr m.receiver;
    each m.args
  | Projection p ->
    expr p.record;
    each p.args
  | Requires q -> List.iter (fun (e, _) -> expr e) q.constraints
  | Binary (_, a, b) ->
    expr a;
    expr b
  | Conditional (c, a, b) ->
    expr c;
    expr a;
    expr b
  | Braced es -> each es
  | Variant_get (_, e) -> Option.iter expr e
  | Foreign (_, f) -> each f.values

(** The expressions and statement lists a statement holds directly. *)
let stmt : type p. expr:(p Expr.t -> unit) -> stmts:(p Stmt.t list -> unit) -> p Stmt.t -> unit =
 fun ~expr ~stmts s ->
  match s with
  | Return (Some e) | Expression e | Structured_binding (_, e) | Bind_variable (_, _, e) -> expr e
  | Return None | Declare _ | Throw _ | Assert _ | Foreign_text _ | Comment _ | Local_struct _ | Local_type_alias _
  | Declare_value_initialized _ | Continue | Break ->
    ()
  | If_constexpr i ->
    stmts i.then_;
    stmts i.else_
  | If i ->
    expr i.condition;
    stmts i.then_;
    stmts i.else_
  | If_declaration i ->
    expr i.init;
    stmts i.then_;
    stmts i.else_
  | Switch w ->
    expr w.scrutinee;
    List.iter (fun (_, b) -> stmts b) w.branches;
    Option.iter stmts w.default
  | Custom_match m ->
    expr m.scrutinee;
    List.iter (fun (b : p Custom_match.branch) -> stmts b.body) m.branches
  | Assign (l, r) ->
    expr l;
    expr r
  | For_range (_, e, b) ->
    expr e;
    stmts b
  | While (c, b) ->
    expr c;
    stmts b
  | Block b -> stmts b
  | Foreign_block b -> List.iter expr b.values
  | Match (sc, branches, default) ->
    expr sc.expr;
    List.iter
      (fun (b : p Match.branch) ->
        List.iter expr b.extra_conditions;
        stmts b.body )
      branches;
    Option.iter stmts default
