(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every fixpoint takes the shape its type says.  See [fix_shape.mli]. *)

open Names

(* The [let]s go under the lambdas one at a time, from the innermost, each
   lifted over the binder it crosses. *)
let rec float_lets_under_lams = function
  | Core.Expr.Let {binder = x; binder_type = t; value = a; body = b; occurrence = occ} -> (
    match float_lets_under_lams b with
    | Core.Expr.Lambda {parameter = y; parameter_type = ty; body = c} ->
      Core.Expr.Lambda {parameter = y;
                        parameter_type = ty;
                        body = float_lets_under_lams (Core.Expr.Let {binder = x;
                                                                     binder_type = t;
                                                                     value = Core_util.ast_lift 1 a;
                                                                     body = Core_util.permut_rels 1 1 c;
                                                                     occurrence = occ})}
    | b -> Core.Expr.Let {binder = x; binder_type = t; value = a; body = b; occurrence = occ} )
  | e -> e

(* [cofix o := Cons 1 o] as [(cofix o (_ : unit) := Cons 1 (o tt)) tt]. *)
let thunk_nullary_cofix x ids funs occ =
  match (Table.resolve_unit_type (), Table.resolve_tt_ctor ()) with
  | Some u, Some tt ->
    let unit_ty = Core.Type.Global_app {head = u; type_arguments = []; index_arguments = []} in
    let tt_v = Core.Expr.Construct {result_type = unit_ty;
                                    constructor = tt;
                                    arguments = [];
                                    occurrence = Core.Occurrence.fresh ()} in
    let n = Array.length ids in
    (* Under the new binder the block's functions are [Core.Expr.Bound_variable (k + 1)] to
       [Core.Expr.Bound_variable (k + n)] at [k] binders deeper still. *)
    let rec call_self k = function
      | Core.Expr.Bound_variable {index = i; _} as f when i > k && i <= k + n ->
        Core.Expr.Apply {callee = f; arguments = [tt_v]}
      | t -> Core_util.ast_map_lift call_self k t
    in
    let thunk f =
      Core.Expr.Lambda
        { parameter = Core.Binder_name.Source (Id.of_string "u");
          parameter_type = unit_ty;
          body = call_self 1 (Core_util.ast_lift 1 f) }
    in
    let ids = Array.map (fun (id, ty) -> (id, Core.Type.Arrow {parameter = unit_ty; result = ty})) ids in
    Core.Expr.Apply
      { callee = Core.Expr.Cofixpoint (Core.Recursion.Group.of_arrays ~selected:x ids (Array.map thunk funs) occ);
        arguments = [tt_v] }
  | _ -> CErrors.anomaly (Pp.str "Fix_shape: a parameterless local cofixpoint needs unit")

(* Bottom-up: every fixpoint's functions get their [let]s floated, then a
   cofixpoint none of whose functions is a lambda is thunked. *)
let rec expr e =
  match Core_util.ast_map expr e with
  | Core.Expr.Fixpoint g -> Core.Expr.Fixpoint (Core.Recursion.Group.map_bodies float_lets_under_lams g)
  | Core.Expr.Cofixpoint g ->
    let g = Core.Recursion.Group.map_bodies float_lets_under_lams g in
    let funs = Core.Recursion.Group.bodies g in
    if Array.for_all (function Core.Expr.Lambda _ -> false | _ -> true) funs then
      thunk_nullary_cofix g.selected (Core.Recursion.Group.functions g) funs g.occurrence
    else Core.Expr.Cofixpoint g
  | e -> e

let decl = function
  | Core.Decl.Value {entity = r; body = b; type_ = ty} -> Core.Decl.Value {entity = r; body = expr b; type_ = ty}
  | Core.Decl.Recursive_group fds ->
    Core.Decl.Recursive_group
      (Core.Nonempty.map
         (fun (fd : Core.Recursion.Definition.t) ->
           {fd with Core.Recursion.Definition.body = expr (float_lets_under_lams fd.body)} )
         fds )
  | d -> d

let structure = Modutil.map_struct_decls decl
