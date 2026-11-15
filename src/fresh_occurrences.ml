(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every term is an occurrence of its own.  See [fresh_occurrences.mli]. *)


(* A group recursing at a ground instance stays one under its new
   occurrence ({!Table.add_erased_fix_group}). *)
let fix_occurrence occ =
  let occ' = Core.Occurrence.fresh () in
  if Table.is_erased_fix_group occ then Table.add_erased_fix_group occ';
  occ'

let rec term e =
  match Mlutil.ast_map term e with
  | Core.Expr.Bound_variable {index = i; _} -> Core.Expr.fresh_rel i
  | Core.Expr.Let {binder = x; binder_type = ty; value = a; body = b; _} ->
    Core.Expr.Let {binder = x; binder_type = ty; value = a; body = b; occurrence = Core.Occurrence.fresh ()}
  | Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; _} ->
    Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; occurrence = Core.Occurrence.fresh ()}
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = args; _} ->
    Core.Expr.Construct {result_type = ty; constructor = r; arguments = args; occurrence = Core.Occurrence.fresh ()}
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; _} ->
    Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = Core.Occurrence.fresh ()}
  | Core.Expr.Boxed_value {value = a; _} -> Core.Expr.Boxed_value {value = a; occurrence = Core.Occurrence.fresh ()}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    Core.Expr.Lambda_group_barrier {value = a; occurrence = Core.Occurrence.fresh ()}
  | Core.Expr.Fixpoint g -> Core.Expr.Fixpoint (Core.Recursion.Group.with_occurrence g (fix_occurrence g.occurrence))
  | Core.Expr.Cofixpoint g ->
    Core.Expr.Cofixpoint (Core.Recursion.Group.with_occurrence g (fix_occurrence g.occurrence))
  | Core.Expr.Global use -> Core.Expr.Global (Core.Global_use.refresh use)
  | e -> e

let decl = function
  | Core.Decl.Value {entity = r; body = b; type_ = ty} -> Core.Decl.Value {entity = r; body = term b; type_ = ty}
  | Core.Decl.Recursive_group fds ->
    Core.Decl.Recursive_group
      (Core.Nonempty.map (Core.Recursion.Definition.map_body term) fds)
  | d -> d

let structure = Modutil.map_struct_decls decl
