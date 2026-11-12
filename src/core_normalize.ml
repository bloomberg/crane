(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

let apply f args = Numeral_literal.fold (Mlutil.canonical_app f args)

let rec spine = function
  | MLapp (f, args) -> apply (spine f) (List.map spine args)
  | e -> Mlutil.ast_map spine e

let canonical_head = function
  | MLapp (MLglob _, _) | MLmagic _ -> false
  | MLcase (_, _, [|_|], _) -> false
  | _ -> true

let canonical_application = function
  | MLapp (f, _) as e -> canonical_head f && not (Numeral_literal.folds e)
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
          (fun (fd : ml_fix_def) ->
            if not (is_canonical fd.fd_body) then
              Probe.violation "non-canonical application"
                Pp.(str "a body of " ++ Printer.pr_global fd.fd_ref ++ str " after normalization") )
          (Mlutil.term_defs d) )
      (fun _ -> ())
      (fun _ -> ())
      s

let structure =
  Modutil.map_struct_decls (function
    | Dterm (r, b, ty) -> Dterm (r, spine b, ty)
    | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = spine fd.fd_body}) fds)
    | d -> d )
