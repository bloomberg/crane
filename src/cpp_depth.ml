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

(** Whether descending into a subexpression is sound.  A lambda's body binds
    its own names, and a conditional's branches are not both evaluated, so
    neither can have a piece lifted out ahead of it. *)
let descendable = function
  | CPPlambda _ | CPPoverloaded _ | CPPcond _ -> false
  | _ -> true

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

(** [flatten_expr ty e] is [e] rewritten so that no remaining nesting reaches
    {!chunk_depth}, paired with the bindings the lifted pieces were given, in
    the order they must be emitted.  Each piece is used exactly once, hence the
    move. *)
let flatten_expr e =
  let stmts = ref [] in
  let next = ref 0 in
  let rec go e =
    if not (descendable e) then
      e
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

(** [flatten decl] rewrites every initialiser in [decl] whose nesting exceeds
    {!max_depth}, and leaves the rest untouched. *)
let rec flatten decl =
  match decl with
  | Dasgn (r, ty, e) when depth e > max_depth ->
    let stmts, e = flatten_expr e in
    Dasgn
      ( r,
        ty,
        mk_call (mk_lambda [] (Some ty) (stmts @ [Sreturn (Some e)]) ~by_value:false) [] )
  | Dtemplate (tps, c, inner) -> Dtemplate (tps, c, flatten inner)
  | Dnspace (r, decls) -> Dnspace (r, List.map flatten decls)
  | _ -> decl
