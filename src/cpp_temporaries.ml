(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Putting back the temporaries {!Normalize} introduced.

    Normalize names every recursive call it takes out of an expression, so
    that loopification meets the call as a statement it can split the
    function at.  Where it does split, the name becomes frame state or the
    binding of [_result]; everywhere else it is a local the Rocq source never
    had.  This pass returns each such temporary to the one place it is read,
    which, where nothing was split, restores the expression Normalize took it
    out of: Normalize only binds a call from a strictly evaluated position,
    in evaluation order, and never out of a branch, a lambda or a let body.

    A temporary is known by its name ({!Mlutil.is_temporary_id}).  It goes
    back when it is read exactly once, by the first statement after the run
    of temporaries it heads, at a position that statement evaluates
    unconditionally -- never into a reference's initialiser or the scrutinee
    of a match that borrows it, where a reference into the inlined value
    would outlive it. *)

open Names
open Minicpp

(* Occurrences of [x] in a statement list, binding sites included: a
   temporary assigned to again is not one to inline. *)
let rec count_expr x n e =
  match e with
  | CPPvar y when Id.equal x y -> n + 1
  | _ -> fold_expr_children ~on_expr:(count_expr x) ~on_stmts:(count_stmts x) n e

and count_stmt x n s =
  let n = match s with Sasgn (y, _, _) when Id.equal x y -> n + 1 | _ -> n in
  fold_stmt_children ~on_expr:(count_expr x) ~on_stmts:(count_stmts x) n s

and count_stmts x n stmts = List.fold_left (count_stmt x) n stmts

(* [e] with its read of [x] replaced by [v], if that read is evaluated
   whenever [e] is. *)
let rec subst_expr x v e =
  match e with
  | CPPvar y when Id.equal x y -> Some v
  (* A move out of the temporary moves out of what it held: once, and only
     if that is an lvalue -- a move of a call's result would cost the copy
     elision it was written to give. *)
  | CPPmove (CPPvar y) when Id.equal x y ->
    Some
      ( match v with
      | CPPvar _ | CPPaccess _ | CPPderef _ -> CPPmove v
      | _ -> v )
  | _ when not (evaluates_children e) -> None
  | _ ->
    let found = ref false in
    let in_child c =
      if !found then c
      else
        match subst_expr x v c with
        | Some c' ->
          found := true;
          c'
        | None -> c
    in
    let e' = map_expr in_child Fun.id Fun.id e in
    if !found then Some e' else None

(* [s] with its read of [x] replaced by [v], if [s] evaluates that read
   unconditionally and holds on to no reference into it: a value
   declaration, not a reference, and a match only if it takes its scrutinee
   by value. *)
let subst_stmt x v s =
  let in_expr rebuild e = Option.map rebuild (subst_expr x v e) in
  match s with
  | Sreturn (Some e) -> in_expr (fun e -> Sreturn (Some e)) e
  | Sexpr e -> in_expr (fun e -> Sexpr e) e
  | Sasgn (y, (Declare ty as t), e) when not (is_reference_type ty) ->
    in_expr (fun e -> Sasgn (y, t, e)) e
  | Sasgn (y, Existing, e) -> in_expr (fun e -> Sasgn (y, Existing, e)) e
  | Sif (c, a, b) -> in_expr (fun c -> Sif (c, a, b)) c
  | Scustom_case (ty, scrut, tys, brs, ({cm_scrutinee = Scrut_owned; _} as cm)) ->
    in_expr (fun scrut -> Scustom_case (ty, scrut, tys, brs, cm)) scrut
  | _ -> None

let is_temporary = function
  | Sasgn (y, Declare _, _) -> Mlutil.is_temporary_id y
  | _ -> false

(* [rest] with [x] replaced by [v] in the first statement past the leading
   temporaries, if that is where [x] is read. *)
let rec inline_into x v = function
  | s :: rest when is_temporary s && count_stmt x 0 s = 0 ->
    Option.map (fun rest -> s :: rest) (inline_into x v rest)
  | s :: rest -> Option.map (fun s -> s :: rest) (subst_stmt x v s)
  | [] -> None

(* A statement list with its temporaries put back, the last first: by the
   time a temporary is considered, every temporary between it and its use
   has already gone back into that use. *)
let rec stmts = function
  | [] -> []
  | s :: rest -> (
    let rest = stmts rest in
    let s = stmt s in
    match s with
    | Sasgn (x, Declare _, v) when Mlutil.is_temporary_id x && count_stmts x 0 rest = 1 ->
      Option.default (s :: rest) (inline_into x v rest)
    | _ -> s :: rest )

and stmt s = map_stmt ~fl:stmts expr stmt Fun.id s

and expr e = map_expr ~fl:stmts expr stmt Fun.id e

(** [decl d] is [d] with its temporaries put back. *)
let decl d = map_decl ~fl:stmts expr stmt Fun.id d
