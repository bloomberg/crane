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
open Minicpp

(** Nesting a compiler parses comfortably.  Below this an initialiser is left
    exactly as it was, so the pass is invisible to all but the pathological
    cases it exists for. *)
let max_depth = 100

(** Nesting of each binding the flattening produces.  Well under
    {!max_depth}, and large enough that the run is a fraction of the
    expression's size. *)
let chunk_depth = 32

(** Whether descending into a subexpression is sound: a piece can be lifted
    out ahead of it only if it is evaluated with it. *)
let descendable = evaluates_children

(** The expression's nesting, counting only what {!descendable} admits: what
    is not descended into is not restructured either, so it does not
    contribute. *)
let rec depth e =
  if not (descendable e) then
    1
  else
    1
    + fold_expr_children
        ~on_expr:(fun acc c -> max acc (depth c))
        ~on_stmts:(fun acc _ -> acc)
        0 e

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
      let e = map_expr go (fun s -> s) (fun t -> t) e in
      if depth e < chunk_depth then
        e
      else begin
        let id = Id.of_string (Printf.sprintf "_lit%d" !next) in
        incr next;
        stmts := Sasgn (id, Declare Tauto, e) :: !stmts;
        CPPmove (CPPvar id)
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
    mk_iife None (stmts @ [Sreturn (Some e)])
  end
  else
    map_expr bound_expr bound_stmt (fun t -> t) e

and bound_stmt s = map_stmt bound_expr bound_stmt (fun t -> t) s

(** [flatten decl] rewrites every expression in [decl] whose nesting exceeds
    {!max_depth}, and leaves the rest untouched. *)
let flatten decl = map_decl bound_expr bound_stmt (fun t -> t) decl
