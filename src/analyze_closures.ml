(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which local fixpoints may outlive their scope.  See
    [analyze_closures.mli]. *)

open Miniml

type group = Lifted | In_place | Closures

let rec callee = function MLmagic (_, f) -> callee f | f -> f

let arity f = List.length (fst (Mlutil.collect_lams f))

let sequential_bind use = Core_effects.find use = Some {operation = Bind; mode = Sequential}

let rec group ~n_outer ?continuation ~cofix ids bodies =
  if Ml_type_util.own_type_variables ~n_outer (List.map snd (Array.to_list ids)) then Lifted
  else if
    escapes_in_bodies ~n_outer ~cofix bodies || Option.cata (escapes ~n_outer 1) false continuation
  then Closures
  else In_place

(* Whether the local fixpoint at [k] may outlive its scope as [t] uses it:
   named other than as the function an application applies, or named at all
   inside a closure. *)
and escapes ~n_outer k t =
  let rec go k = function
    | MLrel (i, _) -> i = k
    | MLapp (f, args) when (match callee f with MLrel (i, _) -> i = k | _ -> false) ->
      List.exists (go k) args
    | MLapp (MLfix (x, ids, bodies, cofix, _), args)
      when List.length args >= arity bodies.(x) && group ~n_outer ~cofix ids bodies = In_place ->
      in_place k bodies || List.exists (go k) args
    | MLletin (_, _, MLfix (_, ids, bodies, cofix, _), b, _)
      when group ~n_outer ~continuation:b ~cofix ids bodies = In_place ->
      in_place k bodies || go (k + 1) b
    (* A bind generated as sequencing runs its continuation's body inline. *)
    | MLapp (MLglob use, (_ :: _ :: _ as args)) when sequential_bind use -> (
      match List.rev args with
      | continuation :: rest -> (
        List.exists (go k) rest
        ||
        match Mlutil.collect_lams continuation with
        | [], _ -> go k continuation
        | ids, body -> go (k + List.length ids) body )
      | [] -> false )
    | MLapp (f, args) -> go k f || List.exists (go k) args
    | MLmagic (_, a) -> go k a
    | MLlam (_, _, body) -> Mlutil.ast_occurs (k + 1) body
    | MLfix (_, ids, bodies, _, _) -> Array.exists (Mlutil.ast_occurs (k + Array.length ids)) bodies
    | MLletin (_, _, a, b, _) -> go k a || go (k + 1) b
    | MLcase (_, scrut, branches) ->
      go k scrut || Array.exists (fun (ids, _, _, body) -> go (k + List.length ids) body) branches
    | MLcons (_, _, args) | MLtuple args -> List.exists (go k) args
    | MLparray (elts, def) -> Array.exists (go k) elts || go k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> false
  (* A group generated in place runs where it is called, and its bodies read
     what they close over there. *)
  and in_place k bodies =
    let n = Array.length bodies in
    Array.exists
      (fun f ->
        let params, body = Mlutil.collect_lams f in
        go (k + n + List.length params) body )
      bodies
  in
  go k t

(* Whether a member of the group escapes in a member's own body, which
   stands under its parameters and the group's members, the last innermost.
   A cofixpoint's body is suspended, so any mention of one there does. *)
and escapes_in_bodies ~n_outer ~cofix bodies =
  let n = Array.length bodies in
  Array.exists
    (fun f ->
      let params, body = Mlutil.collect_lams f in
      let k = List.length params in
      List.exists
        (fun j ->
          let member = k + n - j in
          if cofix then Mlutil.ast_occurs member body else escapes ~n_outer member body )
        (List.init n Fun.id) )
    bodies
