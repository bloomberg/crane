(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Flattening of deeply nested initialiser expressions.

    A compile-time value extracts to one constructor application per element,
    so a four-hundred-element list, or the unary [nat] for three thousand, is a
    single expression nested that deep.  C++ compilers parse an expression by
    recursive descent and run out of stack well before that.

    The same value written as a run of local bindings costs the parser nothing,
    each binding being one shallow expression.  This pass rewrites an
    initialiser that is too deep into such a run, inside an immediately-invoked
    lambda so that it stays an expression. *)

open Names

type expr = Cpp_ir.Lowered.Expr.t

(** Nesting a compiler parses comfortably.  Below this an initialiser is left
    exactly as it was, so the pass is invisible to all but the pathological
    cases it exists for. *)
let max_depth = 100

(** Nesting of each binding the flattening produces.  Well under
    {!max_depth}, and large enough that the run is a fraction of the
    expression's size. *)
let chunk_depth = 32

(** Whether descending into a subexpression is sound: a piece can be lifted
    out ahead of it only if it is evaluated with it.  A lambda's body runs
    when it is called, and a conditional's or a connective's second operand
    only if the first says so. *)
let descendable : expr -> bool = function
  | Lambda _ | Conditional _ | Binary ((And | Or), _, _) -> false
  | _ -> true

(** The expressions [e] evaluates directly, not through a statement: of a
    requires expression, the expressions it constrains and not the
    constraints. *)
let operands (e : expr) =
  match e with
  | Requires q -> List.map fst q.constraints
  | _ ->
    let found = ref [] in
    let ignore_ _ = () in
    Cpp_ir.Children.expr {expr = (fun c -> found := c :: !found); stmt = ignore_; type_ = ignore_} e;
    !found

(** The expression's nesting, counting only what {!descendable} admits: what
    is not descended into is not restructured either, so it does not
    contribute. *)
let rec depth e =
  if not (descendable e) then 1 else 1 + List.fold_left (fun acc c -> max acc (depth c)) 0 (operands e)

(** A rewrite of an expression's children by [expr], its statements and
    types left as they are. *)
let children expr : Cpp_ir.Lowered.phase Cpp_ir.Map.t = Cpp_ir.Map.make ~expr ~stmt:Fun.id ~type_:Fun.id ()

(** [e] evaluated in place: a nullary lambda borrowing its scope, called at
    once. *)
let invoked_in_place body : expr =
  Call
    ( {yields = Untyped; params = Unknown; constructs = None; occurrence = None},
      Lambda
        { params = [];
          type_params = [];
          return_type = None;
          body;
          capture = Runs_in_place;
          moved = [];
          binders = [];
          fixpoint = None },
      [] )

(** [flatten_expr e] is [e] rewritten so that no remaining nesting reaches
    {!chunk_depth}, paired with the bindings the lifted pieces were given, in
    the order they must be emitted.  Each piece is used exactly once, hence the
    move.

    What {!descendable} rejects is not restructured, but it may still hide a
    too-deep expression of its own, so it is handed back to {!bound_expr}. *)
let rec flatten_expr e =
  let stmts = ref [] in
  let next = ref 0 in
  let rec go e =
    if not (descendable e) then
      bound_expr e
    else begin
      let e = Cpp_ir.Map.expr (children go) e in
      if depth e < chunk_depth then
        e
      else begin
        let id = Id.of_string (Printf.sprintf "_lit%d" !next) in
        incr next;
        stmts := (Bind_variable (id, Declare (Auto, None), e) : Cpp_ir.Lowered.Stmt.t) :: !stmts;
        Move (Local id)
      end
    end
  in
  let e = go e in
  (List.rev !stmts, e)

(** [bound_expr e] is [e] with every too-deep subexpression replaced by an
    immediately-invoked lambda that computes it as a run of bindings.  Being an
    expression itself, the replacement needs no statement context and so fits
    wherever the original stood: an initialiser, a return, a call argument. *)
and bound_expr e =
  if descendable e && depth e > max_depth then begin
    let stmts, e = flatten_expr e in
    invoked_in_place (stmts @ [Return (Some e)])
  end
  else
    Cpp_ir.Map.expr (bounded ()) e

and bound_stmt s = Cpp_ir.Map.stmt (bounded ()) s

(** The rewrite bounding every expression and statement below a node. *)
and bounded () = Cpp_ir.Map.make ~expr:bound_expr ~stmt:bound_stmt ~type_:Fun.id ()

(** [flatten decl] rewrites every expression in [decl] whose nesting exceeds
    {!max_depth}, and leaves the rest untouched. *)
let flatten (decl : Cpp_ir.Lowered.Decl.t) = Cpp_ir.Map.decl (bounded ()) decl
