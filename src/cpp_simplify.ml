(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small local simplifications.  See [cpp_simplify.mli]. *)

open Names
open Minicpp

(* A [bool]: what a comparison or a connective yields. *)
let is_bool = function
  | CPPbinop ((Beq | Bneq | Band | Bor), _, _) | CPPunop (Unot, _) | CPPbool _ -> true
  | _ -> false

(* A function type, as written or through an alias for one ([stateT]). *)
let rec is_function_type = function
  | Tfun _ -> true
  | Tglob (GlobRef.ConstRef kn, _, _) -> (
    match Table.lookup_typedef_unchecked kn with
    | Some ml -> ( match Mlutil.ml_resolve ml with Miniml.Tarr _ -> true | _ -> false )
    | None -> false )
  | Tnamespace (_, t) -> is_function_type t
  | _ -> false

(* Drop each binding of a pure value nothing after it reads or assigns. *)
let rec drop_unused = function
  | [] -> []
  | Sasgn (x, Declare _, e) :: rest
    when pure_expr e
         && (not (List.exists (Id.equal x) (free_vars_body rest)))
         && not (Id.Set.mem x (assigned_vars rest)) ->
    drop_unused rest
  | s :: rest -> s :: drop_unused rest

(* The variable [e] reads a member of, through a chain of member reads: a
   field, a pair's component through its projection mapping, a
   [crane::field]'s contents. *)
let rec member_root = function
  | CPPaccess (Adot, e, _) | CPPget (e, _) | CPPget' (e, _, _) -> path_root e
  | CPPfun_call
      (_, CPPglob (_, _, Some {ci_inline = Some {it_shape = Inline_pair_projection _; _}; _}), {rev = [e]})
  | CPPfun_call (_, CPPrt Crane_rt.Unbox_field, {rev = [e]}) ->
    path_root e
  | _ -> None

and path_root = function CPPvar x -> Some x | e -> member_root e

(* Whether [stmts] move from [v] anywhere, or from anything inside it, or
   reach into it mutably -- a reuse arm decomposes its scrutinee through
   [v_mut()]. *)
let takes_from v stmts =
  let rec fe found e =
    found
    || ( match e with
       | CPPmove e -> path_root e = Some v
       | CPPaccess (_, e, f) | CPPaccess_call (_, e, f, _) ->
         String.equal (Id.to_string f) "v_mut" && path_root e = Some v
       | _ -> false )
    || fold_expr_children ~on_expr:fe ~on_stmts:fl false e
  and fl found l =
    found || List.exists (fold_stmt_children ~on_expr:fe ~on_stmts:fl false) l
  in
  fl false stmts

(* A local copied out of a member of another -- [T2 s0 = si.first] -- is a
   [const] reference to it instead, where the other is neither assigned nor
   moved from afterwards, and the local neither assigned nor taken from: the
   other outlives it,
   and {!Last_use} moves from nothing a reference binds into, so what it
   names stays put.  The copy it saved is made only by a use that keeps the
   value.  A type a copy costs nothing for -- a scalar, a pointer -- is
   copied as it was. *)
let rec bind_by_reference = function
  | [] -> []
  | Sasgn (x, Declare ty, rhs) :: rest
    when (match ty with Tref _ | Tconst (Tref _) -> false | _ -> true)
         && (ty = Tauto || Loopify.worthwhile_move_type ty)
         && ( match member_root rhs with
            | Some v ->
              let assigned = assigned_vars rest in
              not
                ( Id.Set.mem x assigned || Id.Set.mem v assigned
                || takes_from v rest || takes_from x rest )
            | None -> false ) ->
    let ty = match ty with Tconst _ -> ty | _ -> Tconst ty in
    Sasgn (x, Declare (Tref (Lvalue, ty)), rhs) :: bind_by_reference rest
  | s :: rest -> s :: bind_by_reference rest

(* Under Reuse, a match-only scrutinee may be marked owned so that a reuse arm
   can consume it; one reached through a [const] reference or a pointer cannot
   be, and its matches borrow -- see {!Minicpp.borrow_bound_matches}. *)
let borrow_bound ss = if Table.reuse () then borrow_bound_matches ss else ss

let rec stmts ss = borrow_bound (bind_by_reference (drop_unused (List.map stmt ss)))

and stmt s =
  match s with
  | Sif (c, t, e) -> (
    match expr c with
    | CPPbool b -> Sblock (stmts (if b then t else e))
    | c -> (
      match (stmts t, stmts e) with
      | [Sreturn (Some (CPPbool true))], [Sreturn (Some (CPPbool false))] when is_bool c ->
        Sreturn (Some c)
      | t, e -> Sif (c, t, e) ) )
  | _ -> map_stmt ~fl:stmts expr stmt Fun.id s

and expr e =
  match e with
  | CPPcond (CPPbool b, x, y) -> expr (if b then x else y)
  (* [k(a)(b)] through a local: a curried closure applied to both arguments
     at once, which allocates nothing for the closure in between when [k]
     was written as one lambda returning another. *)
  | CPPfun_call
      (sg, CPPfun_call (_, ((CPPvar _ | CPPmove (CPPvar _)) as k), {rev = [a]}), {rev = [b]}) ->
    CPPfun_call (sg, CPPrt Crane_rt.Apply2, of_reversed [expr b; expr a; k])
  (* A lambda that only returns another lambda hands it back unboxed: the
     [fn] it converts into still boxes it where it is kept, and
     [crane::apply2] runs it where it is applied at once. *)
  | CPPlambda ({cl_ret = Some t; cl_body = [Sreturn (Some (CPPlambda _))]; _} as l)
    when is_function_type t ->
    map_expr ~fl:stmts expr stmt Fun.id (CPPlambda {l with cl_ret = None})
  | _ -> map_expr ~fl:stmts expr stmt Fun.id e

let transform_decl d = map_decl ~fl:stmts expr stmt Fun.id d
