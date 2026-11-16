(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

let same = GlobRef.CanOrd.equal

(* Whether [e] names the global [f] anywhere. *)
let rec mentions f = function
  | Core.Expr.Global {callee; _} when same callee f -> true
  | e ->
    let found = ref false in
    Base.Core_util.ast_iter (fun e -> if mentions f e then found := true) e;
    !found

(* Whether [e] is the eta-expansion of [f], with each binder whether [f]
   takes it, outermost first: lambdas calling [f] on their binders in
   order, but those erased, which a well-founded recursion's proof
   arguments are. *)
let eta_of f e =
  let binders, body = Base.Core_util.collect_lams e in
  let binders = List.rev binders in
  let m = List.length binders in
  let kept = List.map (fun (_, ty) -> not (Base.Core_util.is_erased_type ty)) binders in
  let reads = List.filter_map (fun (i, k) -> if k then Some (m - i) else None) (List.mapi (fun i k -> (i, k)) kept) in
  let reads_binder a i = match a with Core.Expr.Bound_variable {index = i'; _} -> Int.equal i i' | _ -> false in
  match body with
  | Core.Expr.Apply {callee = Core.Expr.Global {callee; _}; arguments = args}
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
  let knot d = function Core.Expr.Bound_variable {index = i; _} -> i = k - j + d | _ -> false in
  let rec self d e =
    match e with
    | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; _};
                       arguments = args} when i = k - j + d && List.compare_lengths args kept = 0 ->
      let args = List.filter_map (fun (a, taken) -> if taken then Some (self d a) else None) (List.combine args kept) in
      Core.Expr.Apply {callee = Core.Expr.Global (Core.Global_use.monomorphic f); arguments = args}
    | Core.Expr.Bound_variable {index = i; _} when i = k - j + d -> raise_notrace Read
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when List.exists (knot d) args -> (
      match (Core.Ref.User.Map.find_opt use.callee defs, Specialize.body_of defs use) with
      | Some (Specialize.Term _), Some helper -> (
        match Specialize.instantiate helper args with Some e -> self d e | None -> raise_notrace Read )
      | _ -> raise_notrace Read )
    | _ -> Base.Core_util.ast_map_lift self d e
  in
  try Some (self 0 body) with Read -> None

(* The function [fd] with the knot it ties, if it ties one, tied. *)
let fixpoint defs (fd : Core.Recursion.Definition.extracted) =
  let f = fd.entity in
  if (not (Base.Table.should_loopify f)) || Base.Table.is_custom f || Base.Core_util.type_maxvar fd.type_ > 0 then None
  else
    let params, inner = Base.Core_util.collect_lams fd.body in
    match inner with
    | Core.Expr.Apply {callee = Core.Expr.Global ({callee = g; _} as use); arguments = args} when not (same g f) -> (
      let indexed = List.mapi (fun i a -> (i, a)) args in
      let knots = List.filter_map (fun (i, a) -> Option.map (fun kept -> (i, kept)) (eta_of f a)) indexed in
      match (knots, Core.Ref.User.Map.find_opt g defs) with
      | [(j, kept)], Some (Specialize.Term _)
        when not (List.exists (fun (i, a) -> i <> j && mentions f a) indexed) -> (
        match Specialize.body_of defs use with
        | None -> None
        | Some functional -> (
          let gparams, gbody = Base.Core_util.collect_lams functional in
          let k = List.length gparams in
          if k <> List.length args then None
          else
            match tie defs f ~kept k j gbody with
            | None -> None
            | Some tied ->
              let args =
                List.mapi (fun i a -> if i = j then Core.Expr.Erased_value Core.Erasure_reason.Proof else a) args in
              Option.map
                (fun body ->
                  {fd with Core.Recursion.Definition.body = Base.Core_util.named_lams params (Base.Core_util.normalize body)})
                (Specialize.instantiate (Base.Core_util.named_lams gparams tied) args) ) )
      | _ -> None )
    | _ -> None

let structure struc =
  let defs = Specialize.definitions struc in
  let rec elems l =
    List.map
      (fun (lbl, se) ->
        match se with
        | Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group {head = fd; tail = []}) -> (
          match fixpoint defs fd with
          | Some fd ->
            (lbl, Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group (Core.Nonempty.singleton fd)))
          | None -> (lbl, se) )
        | Core.Module.Structure_item.Module ({Core.Module.expr = Core.Module.Expr.Structure {path = mp;
                                                                                             items = l}; _} as m) ->
          (lbl,
            Core.Module.Structure_item.Module
              {m with Core.Module.expr = Core.Module.Expr.Structure {path = mp; items = elems l}})
        | se -> (lbl, se) )
      l
  in
  List.map (fun (mp, l) -> (mp, elems l)) struc
