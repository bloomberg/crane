(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every fixpoint takes the shape its type says.  See [fix_shape.mli]. *)

open Names
open Miniml

let rec float_lets_under_lams = function
  | MLletin (x, t, a, b, occ) -> (
    match float_lets_under_lams b with
    | MLlam (y, ty, c) ->
      MLlam (y, ty, float_lets_under_lams (MLletin (x, t, Mlutil.ast_lift 1 a, Mlutil.permut_rels 1 1 c, occ)))
    | b -> MLletin (x, t, a, b, occ) )
  | e -> e

(* [cofix o := Cons 1 o] as [(cofix o (_ : unit) := Cons 1 (o tt)) tt]. *)
let thunk_nullary_cofix x ids funs occ =
  match (Table.resolve_unit_type (), Table.resolve_tt_ctor ()) with
  | Some u, Some tt ->
    let unit_ty = Tglob (u, [], []) in
    let tt_v = MLcons (unit_ty, tt, []) in
    let n = Array.length ids in
    (* Under the new binder the block's functions are [MLrel (k + 1)] to
       [MLrel (k + n)] at [k] binders deeper still. *)
    let rec call_self k = function
      | MLrel i when i > k && i <= k + n -> MLapp (MLrel i, [tt_v])
      | t -> Mlutil.ast_map_lift call_self k t
    in
    let thunk f = MLlam (Id (Id.of_string "u"), unit_ty, call_self 1 (Mlutil.ast_lift 1 f)) in
    let ids = Array.map (fun (id, ty) -> (id, Tarr (unit_ty, ty))) ids in
    MLapp (MLfix (x, ids, Array.map thunk funs, true, occ), [tt_v])
  | _ -> CErrors.anomaly (Pp.str "Fix_shape: a parameterless local cofixpoint needs unit")

let rec expr e =
  match Mlutil.ast_map expr e with
  | MLfix (x, ids, funs, is_cofix, occ) ->
    let funs = Array.map float_lets_under_lams funs in
    if is_cofix && Array.for_all (function MLlam _ -> false | _ -> true) funs then
      thunk_nullary_cofix x ids funs occ
    else MLfix (x, ids, funs, is_cofix, occ)
  | e -> e

let decl = function
  | Dterm (r, b, ty) -> Dterm (r, expr b, ty)
  | Dfix fds ->
    Dfix (List.map (fun fd -> {fd with fd_body = expr (float_lets_under_lams fd.fd_body)}) fds)
  | d -> d

let structure = Modutil.map_struct_decls decl
