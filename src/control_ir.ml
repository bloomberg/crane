(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

module Loop = struct
  type t =
    | Function of Names.GlobRef.t
    | Member of Miniml.Occurrence.t * int

  let equal a b =
    match (a, b) with
    | Function g, Function g' -> Names.GlobRef.UserOrd.equal g g'
    | Member (o, m), Member (o', m') -> Miniml.Occurrence.equal o o' && Int.equal m m'
    | (Function _ | Member _), _ -> false
end

module Term = struct
  type t =
    | Loop of loop
    | Let of let_
    | Match of match_
    | Return of Miniml.ml_ast
    | Continue of continue_
    | Continue_into of continue_into

  and loop = {
    loop : Loop.t;
    parameters : (Miniml.ml_ident * Miniml.ml_type) list;
    body : t;
  }

  and let_ = {
    binder : Miniml.ml_ident;
    binder_type : Miniml.ml_type;
    value : Miniml.ml_ast;
    body : t;
  }

  and match_ = {
    scrutinee_type : Miniml.ml_type;
    scrutinee : Miniml.ml_ast;
    branches : branch list;
  }

  and branch = {
    binders : (Miniml.ml_ident * Miniml.ml_type) list;
    result_type : Miniml.ml_type;
    pattern : Miniml.ml_pattern;
    body : t;
  }

  and continue_ = {
    target : Loop.t;
    occurrence : Miniml.Occurrence.t;
    arguments : Miniml.ml_ast list;
  }

  and continue_into = {
    cells : cell list;
    next : continue_;
  }

  and cell = {
    constructor : Names.GlobRef.t;
    hole : int;
    arguments : Miniml.ml_ast list;
  }
end

open Term

let continues t =
  let rec go acc = function
    | Loop l -> go acc l.body
    | Let l -> go acc l.body
    | Match m -> List.fold_left (fun acc (b : branch) -> go acc b.body) acc m.branches
    | Return _ -> acc
    | Continue c | Continue_into {next = c; _} -> c.occurrence :: acc
  in
  List.rev (go [] t)

let rec map_returns f = function
  | Loop l -> Loop {l with body = map_returns f l.body}
  | Let l -> Let {l with body = map_returns f l.body}
  | Match m -> Match {m with branches = List.map (fun (b : branch) -> {b with body = map_returns f b.body}) m.branches}
  | Return v -> Return (f v)
  | (Continue _ | Continue_into _) as c -> c

let invariant_parameters (l : loop) =
  let n = List.length l.parameters in
  (* Each Continue of [l], with the number of binders between it and the
     loop's parameters. *)
  let rec turns depth acc = function
    | Loop inner -> turns depth acc inner.body
    | Let b -> turns (depth + 1) acc b.body
    | Match m ->
      List.fold_left (fun acc (b : branch) -> turns (depth + List.length b.binders) acc b.body) acc m.branches
    | Return _ -> acc
    | Continue c | Continue_into {next = c; _} ->
      if Loop.equal c.target l.loop then (depth, c.arguments) :: acc else acc
  in
  let turns = turns 0 [] l.body in
  List.init n (fun i ->
      List.for_all
        (fun (depth, arguments) ->
          match List.nth_opt arguments i with
          | Some (Miniml.MLrel (db, _)) -> Int.equal db (n - i + depth)
          | Some _ | None -> false )
        turns )
