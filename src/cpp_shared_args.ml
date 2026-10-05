(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An argument a mapping splices more than once, evaluated once.  See
    [cpp_shared_args.mli]. *)

open Names
open Minicpp

(* Whether evaluating [e] a second time costs nothing and does nothing. *)
let rec free_to_repeat e =
  match e with
  | CPPvar _ | CPPint _ | CPPuint _ | CPPbool _ | CPPfloat _ | CPPstring _
  | CPPenum_val _ | CPPnullptr | CPPlit _ ->
    true
  | CPPderef e | CPPget' (e, _, _) | CPPaccess (_, e, _) -> free_to_repeat e
  | _ -> false

(* The text of a mapping that splices some argument more than once. *)
let repeating_text = function
  | CPPglob (_, _, Some {ci_inline = Some {it_linear = false; it_text; _}; _}) -> Some it_text
  | _ -> None

(* [e] with each argument it must evaluate once named, at every position [e]
   evaluates unconditionally; [bind x a] binds [x] to [a] ahead of [e], in
   evaluation order. *)
let rec name_args fresh bind e =
  if not (evaluates_children e) then e
  else
    let e = map_expr (name_args fresh bind) Fun.id Fun.id e in
    match e with
    | CPPfun_call (sg, f, args) -> (
      match repeating_text f with
      | Some text ->
        let named =
          List.mapi
            (fun i a ->
              if Foreign_template.arg_mentions text i > 1 && not (free_to_repeat a)
              then (
                let x = fresh () in
                bind x a;
                CPPvar x )
              else a)
            (call_args args)
        in
        CPPfun_call (sg, f, of_reversed (List.rev named))
      | None -> e )
    | _ -> e

(* The statements a rewrite of [s] puts ahead of it, and [s] rewritten: only
   where [s] evaluates its expression once, as its first act. *)
let in_stmt fresh s =
  let bound = ref [] in
  let bind x a = bound := Sasgn (x, Declare (Tref (Forwarding, Tauto)), a) :: !bound in
  let e' e = name_args fresh bind e in
  let s =
    match s with
    | Sreturn (Some e) -> Sreturn (Some (e' e))
    | Sexpr e -> Sexpr (e' e)
    | Sasgn (y, t, e) -> Sasgn (y, t, e' e)
    | Sif (c, a, b) -> Sif (e' c, a, b)
    | s -> s
  in
  List.rev !bound @ [s]

let transform_decl d =
  let used = ref Id.Set.empty in
  let note_ids stmts = used := Id.Set.union !used (Id.Set.of_list (declared_ids stmts @ free_vars_body stmts)) in
  let n = ref 0 in
  let rec fresh () =
    incr n;
    let x = Id.of_string (Printf.sprintf "_once%d" !n) in
    if Id.Set.mem x !used then fresh () else x
  in
  let rec block stmts =
    note_ids stmts;
    List.concat_map (fun s -> in_stmt fresh (stmt s)) stmts
  and stmt s = map_stmt ~fl:block expr stmt Fun.id s
  and expr e = map_expr ~fl:block expr stmt Fun.id e in
  map_decl ~fl:block expr stmt Fun.id d
