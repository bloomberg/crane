(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)


let apply f args = Numeral_literal.fold (Mlutil.canonical_app f args)

let rec spine = function
  | Core.Expr.Apply {callee = f; arguments = args} -> apply (spine f) (List.map spine args)
  | Core.Expr.Construct _ as e when Numeral_literal.folds e -> Numeral_literal.fold e
  | e -> Mlutil.ast_map spine e

let canonical_head = function
  | Core.Expr.Apply {callee = Core.Expr.Global _; _} | Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _ | Core.Expr.Runtime_error _ | Core.Expr.Erased_value _ -> false
  | Core.Expr.Match {branches = [|_|]; _} -> false
  | _ -> true

let canonical_application = function
  | Core.Expr.Apply {callee = f; _} as e -> canonical_head f && not (Numeral_literal.folds e)
  | Core.Expr.Construct _ as e -> not (Numeral_literal.folds e)
  | _ -> true

let rec is_canonical e =
  canonical_application e
  &&
  let canonical = ref true in
  Mlutil.ast_iter (fun c -> if !canonical && not (is_canonical c) then canonical := false) e;
  !canonical

let check s =
  if Probe.checking () then
    Modutil.struct_iter
      (fun d ->
        List.iter
          (fun (fd : Core.Recursion.Definition.t) ->
            if not (is_canonical fd.body) then
              Probe.violation "non-canonical application"
                Pp.(str "a body of " ++ Printer.pr_global fd.entity ++ str " after normalization") )
          (Mlutil.term_defs d) )
      (fun _ -> ())
      (fun _ -> ())
      s

let structure =
  Modutil.map_struct_decls (function
    | Core.Decl.Value {entity = r; body = b; type_ = ty} -> Core.Decl.Value {entity = r; body = spine b; type_ = ty}
    | Core.Decl.Recursive_group fds ->
      Core.Decl.Recursive_group (Core.Nonempty.map (fun (fd : Core.Recursion.Definition.t) -> {fd with Core.Recursion.Definition.body = spine fd.body}) fds)
    | d -> d )
