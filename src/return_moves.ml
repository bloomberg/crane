(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The moves a [return] writes.  See [return_moves.mli]. *)

open Names
open Minicpp
module IdMap = Id.Map

let is_borrowed = Loopify_analysis.is_borrowed

(* What a [return] moves without being told.  A call or a construction is
   built in the caller's object, so a move around it only suppresses copy
   elision.  So is a variable C++ moves implicitly -- a local or parameter of
   the innermost function, held by value.  A structured binding, a reference,
   a loop variable and, inside a lambda, whatever it captures are not: a
   return of one copies unless the move is written. *)
type held = Moved_on_return | Copied_on_return

let prvalue = function
  | CPPfun_call _ | CPPaccess_call _ | CPPmethod_call _ | CPPprojection _ | CPPstruct _
  | CPPstructmk _ | CPPstruct_id _ ->
    true
  | _ -> false

let drop_return_moves d =
  let hold env ids h = List.fold_left (fun env id -> IdMap.add id h env) env ids in
  (* A name not declared where this walk sees it -- by a foreign fragment --
     keeps the reading the printer gave every name before. *)
  let held env x = try IdMap.find x env with Not_found -> Moved_on_return in
  let by_type ty = if is_borrowed ty then Copied_on_return else Moved_on_return in
  let rec stmts env = function
    | [] -> []
    | s :: rest -> stmt env s :: stmts (declare env s) rest
  and declare env = function
    | Sasgn (id, Declare (ty, _), _) -> hold env [id] (by_type ty)
    | Sdecl (id, _, _) | Sdecl_init (id, _) -> hold env [id] Moved_on_return
    | Sbind (ids, _) -> hold env ids Copied_on_return
    | _ -> env
  and stmt env s =
    match s with
    | Sreturn (Some (CPPmove (CPPvar x as v))) when held env x = Moved_on_return ->
      Sreturn (Some v)
    | Sreturn (Some (CPPmove e)) when prvalue e -> Sreturn (Some (expr env e))
    | Smatch (scrut, branches, els) ->
      let branch b =
        let fields = List.map (fun fb -> fb.fb_name) b.smb_field_bindings in
        let bound = match b.smb_var with Some v -> v :: fields | None -> fields in
        let env = hold env bound Copied_on_return in
        {b with smb_extra_conds = List.map (expr env) b.smb_extra_conds; smb_body = stmts env b.smb_body}
      in
      Smatch
        ( {scrut with sc_expr = expr env scrut.sc_expr},
          List.map branch branches,
          Option.map (stmts env) els )
    | Scustom_case (ty, scrut, tys, branches, cm) ->
      let branch (ps, rty, body) =
        (ps, rty, stmts (hold env (List.map (fun p -> p.cp_name) ps) Copied_on_return) body)
      in
      Scustom_case (ty, expr env scrut, tys, List.map branch branches, cm)
    | Sif_decl (id, ty, c, t, e) ->
      let inner = hold env [id] (by_type ty) in
      Sif_decl (id, ty, expr env c, stmts inner t, stmts inner e)
    | Sfor_range (id, e, body) ->
      Sfor_range (id, expr env e, stmts (hold env [id] Copied_on_return) body)
    | _ -> map_stmt ~fl:(stmts env) (expr env) (stmt env) Fun.id s
  and expr env e =
    match e with
    | CPPlambda l ->
      let captured = IdMap.map (fun _ -> Copied_on_return) env in
      let own = List.filter_map snd (lambda_params l.cl_params) in
      CPPlambda {l with cl_body = stmts (hold captured own Moved_on_return) l.cl_body}
    | _ -> map_expr ~fl:(stmts env) (expr env) (stmt env) Fun.id e
  in
  map_decl ~fl:(stmts IdMap.empty) (expr IdMap.empty) (stmt IdMap.empty) Fun.id d
