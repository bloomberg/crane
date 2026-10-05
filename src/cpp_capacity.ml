(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Capacity for a vector reserved from the count of the loop that fills it.
    See [cpp_capacity.mli]. *)

open Names
open Minicpp
module MS = Mapping_semantics

(* The declared meaning of the mapping [e] applies, and its arguments. *)
let applied e =
  match e with
  | CPPfun_call (_, CPPglob (r, _, _), args) ->
    Option.map (fun m -> (m, call_args args)) (MS.find r)
  | CPPglob (r, _, _) -> Option.map (fun m -> (m, [])) (MS.find r)
  | _ -> None

let mentions v stmts = List.exists (Id.equal v) (free_vars_body stmts)

(* [s] appends to [v], and reads [v] no other way. *)
let appends_to v s =
  match s with
  | Sexpr e -> (
    match applied e with
    | Some (MS.Vec_push (c, x), args) -> (
      match (List.nth_opt args c, List.nth_opt args x) with
      | Some (CPPvar v'), Some a -> Id.equal v v' && not (mentions v [Sexpr a])
      | _ -> false )
    | _ -> false )
  | _ -> false

(* Whether [stmts] can leave the loop they are in, or start its next
   iteration early, other than from a lambda nested in them. *)
let rec leaves stmts =
  List.exists
    (fun s ->
      match s with
      | Sreturn _ | Sbreak | Scontinue | Sthrow _ -> true
      | _ ->
        fold_stmt_children
          ~on_expr:(fun acc _ -> acc)
          ~on_stmts:(fun acc b -> acc || leaves b)
          false s)
    stmts

(* Whether [stmts] assign [n]. *)
let rec assigns n stmts =
  List.exists
    (fun s ->
      match s with
      | Sasgn (n', Existing, _) when Id.equal n n' -> true
      | _ ->
        fold_stmt_children
          ~on_expr:(fun acc _ -> acc)
          ~on_stmts:(fun acc b -> acc || assigns n b)
          false s)
    stmts

(** [Some n] when [s] is a loop appending to [v] once per iteration, for as
    many iterations as the counter [n] holds where [s] starts:
    {v while (true) { match n { 0 => leave | S n' => body; n = n' } } v}
    with exactly one statement of [body] an append to [v], none of the rest
    mentioning [v], leaving the loop or assigning [n]. *)
let counted_appends v s =
  match s with
  | Swhile
      ( CPPbool true,
        [Scustom_case (_, CPPvar n, _, [([], _, base); ([(n', _)], _, step)], cm)] )
    when (match cm.cm_inductive with
          | GlobRef.IndRef ind -> MS.nat_width ind <> None
          | _ -> false) -> (
    let exits = match List.rev base with (Sreturn _ | Sbreak) :: _ -> true | _ -> false in
    match List.rev step with
    | Sasgn (n'', Existing, CPPvar m) :: rev_body
      when exits && Id.equal n n'' && Id.equal m n' ->
      let body = List.rev rev_body in
      let pushes, rest = List.partition (appends_to v) body in
      if List.length pushes = 1 && (not (mentions v rest)) && (not (leaves body))
         && not (assigns n body)
      then Some n
      else None
    | _ -> None )
  | _ -> None

(* The reserve the mappings declare, of [n] elements in [v]. *)
let reserve v n =
  match MS.unique_declaration (function MS.Vec_reserve _ -> true | _ -> false) with
  | Some r -> (
    match MS.find r with
    | Some (MS.Vec_reserve (c, k)) when List.sort compare [c; k] = [0; 1] ->
      let args = if c = 0 then [CPPvar v; CPPvar n] else [CPPvar n; CPPvar v] in
      Some
        (Sexpr
           (CPPfun_call
              (call_opaque, CPPglob (r, [], Some (Table.custom_info r)), of_reversed (List.rev args))))
    | _ -> None )
  | None -> None

(* [stmts], the statements after [v] is made, with a reserve in front of the
   loop that fills it, if the first statement mentioning [v] is that loop or
   a block leading to it. *)
let rec reserve_before_fill v stmts =
  match stmts with
  | s :: rest when not (mentions v [s]) ->
    Option.map (fun rest -> s :: rest) (reserve_before_fill v rest)
  | (Sblock inner) :: rest ->
    Option.map (fun inner -> Sblock inner :: rest) (reserve_before_fill v inner)
  | s :: rest -> (
    match counted_appends v s with
    | Some n -> Option.map (fun r -> r :: s :: rest) (reserve v n)
    | None -> None )
  | [] -> None

let rec block = function
  | [] -> []
  | (Sasgn (v, Declare _, e) as s) :: rest
    when (match applied e with Some (MS.Vec_new, _) -> true | _ -> false) ->
    let rest = block rest in
    stmt s :: Option.default rest (reserve_before_fill v rest)
  | s :: rest -> stmt s :: block rest

and stmt s = map_stmt ~fl:block expr stmt Fun.id s

and expr e = map_expr ~fl:block expr stmt Fun.id e

let transform_decl d = map_decl ~fl:block expr stmt Fun.id d
