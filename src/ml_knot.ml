(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml

let same = GlobRef.CanOrd.equal

let rec mentions f = function
  | MLglob {callee; _} when same callee f -> true
  | e ->
    let found = ref false in
    Mlutil.ast_iter (fun e -> if mentions f e then found := true) e;
    !found

(* Whether [e] is the eta-expansion of [f], with each binder whether [f]
   takes it, outermost first: lambdas calling [f] on their binders in
   order, but those erased, which a well-founded recursion's proof
   arguments are. *)
let eta_of f e =
  let binders, body = Mlutil.collect_lams e in
  let binders = List.rev binders in
  let m = List.length binders in
  let kept = List.map (fun (_, ty) -> not (Mlutil.isTdummy ty)) binders in
  let reads = List.filter_map (fun (i, k) -> if k then Some (m - i) else None) (List.mapi (fun i k -> (i, k)) kept) in
  let reads_binder a i = match a with MLrel (i', _) -> Int.equal i i' | _ -> false in
  match body with
  | MLapp (MLglob {callee; _}, args)
    when m > 0 && same callee f && List.compare_lengths args reads = 0 && List.for_all2 reads_binder args reads ->
    Some kept
  | _ -> None

(* [body], under [k] parameters, with each call of the parameter [j],
   outermost first, a call of [f] passing the arguments [kept] says it
   takes: [None] where it reads that parameter otherwise, or calls it with
   other than one argument for each.  The parameter passed whole to a term
   [defs] defines -- a clause helper Equations generates for a [with] or a
   [where], given the recursion as an argument -- reads it where that
   term's body does: the call is that body, instantiated there. *)
let tie defs f ~kept k j body =
  let exception Read in
  let knot d = function MLrel (i, _) -> i = k - j + d | _ -> false in
  let rec self d e =
    match e with
    | MLapp (MLrel (i, _), args) when i = k - j + d && List.compare_lengths args kept = 0 ->
      let args = List.filter_map (fun (a, taken) -> if taken then Some (self d a) else None) (List.combine args kept) in
      MLapp (MLglob (Global_use.monomorphic f), args)
    | MLrel (i, _) when i = k - j + d -> raise_notrace Read
    | MLapp (MLglob use, args) when List.exists (knot d) args -> (
      match (Ref.User.Map.find_opt use.callee defs, Ml_specialize.body_of defs use) with
      | Some (Ml_specialize.Term _), Some helper -> (
        match Ml_specialize.instantiate helper args with Some e -> self d e | None -> raise_notrace Read )
      | _ -> raise_notrace Read )
    | _ -> Mlutil.ast_map_lift self d e
  in
  try Some (self 0 body) with Read -> None

(* The function [fd] with the knot it ties, if it ties one, tied. *)
let fixpoint defs (fd : ml_fix_def) =
  let f = fd.fd_ref in
  if (not (Table.should_loopify f)) || Table.is_custom f || Mlutil.type_maxvar fd.fd_type > 0 then None
  else
    let params, inner = Mlutil.collect_lams fd.fd_body in
    match inner with
    | MLapp (MLglob ({callee = g; _} as use), args) when not (same g f) -> (
      let indexed = List.mapi (fun i a -> (i, a)) args in
      let knots = List.filter_map (fun (i, a) -> Option.map (fun kept -> (i, kept)) (eta_of f a)) indexed in
      match (knots, Ref.User.Map.find_opt g defs) with
      | [(j, kept)], Some (Ml_specialize.Term _)
        when not (List.exists (fun (i, a) -> i <> j && mentions f a) indexed) -> (
        match Ml_specialize.body_of defs use with
        | None -> None
        | Some functional -> (
          let gparams, gbody = Mlutil.collect_lams functional in
          let k = List.length gparams in
          if k <> List.length args then None
          else
            match tie defs f ~kept k j gbody with
            | None -> None
            | Some tied ->
              let args = List.mapi (fun i a -> if i = j then MLdummy Kprop else a) args in
              Option.map
                (fun body -> {fd with fd_body = Mlutil.named_lams params (Mlutil.normalize body)})
                (Ml_specialize.instantiate (Mlutil.named_lams gparams tied) args) ) )
      | _ -> None )
    | _ -> None

let structure struc =
  let defs = Ml_specialize.definitions struc in
  let rec elems l =
    List.map
      (fun (lbl, se) ->
        match se with
        | SEdecl (Dfix [fd]) -> (
          match fixpoint defs fd with Some fd -> (lbl, SEdecl (Dfix [fd])) | None -> (lbl, se) )
        | SEmodule ({ml_mod_expr = MEstruct (mp, l); _} as m) ->
          (lbl, SEmodule {m with ml_mod_expr = MEstruct (mp, elems l)})
        | se -> (lbl, se) )
      l
  in
  List.map (fun (mp, l) -> (mp, elems l)) struc
