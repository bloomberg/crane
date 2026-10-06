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

let rec stmts ss = drop_unused (List.map stmt ss)

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
