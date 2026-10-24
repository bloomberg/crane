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
    | Resume of resume
    | Entry of entry

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

  and resume = {
    binder : Miniml.ml_ident;
    binder_type : Miniml.ml_type;
    value : t;
    body : t;
  }

  and entry = {
    entered : loop;
    name : (Miniml.ml_ident * Miniml.ml_type) option;
    scope : t;
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
    | Resume r -> go (go acc r.value) r.body
    | Entry e -> go (go acc e.entered.body) e.scope
  in
  List.rev (go [] t)

let resumed t =
  (* [valued]: whether [t] is run for a Resume's value, where every turn it
     ends in is resumed after.  The loop an entry enters returns to the call
     entering it, and is resumed after only where that call is. *)
  let rec go valued acc = function
    | Loop l -> go valued acc l.body
    | Let l -> go valued acc l.body
    | Match m -> List.fold_left (fun acc (b : branch) -> go valued acc b.body) acc m.branches
    | Return _ -> acc
    | Continue c | Continue_into {next = c; _} -> if valued then c.occurrence :: acc else acc
    | Resume r -> go valued (go true acc r.value) r.body
    | Entry e -> go valued (go false acc e.entered.body) e.scope
  in
  List.rev (go false [] t)

let continues_into t =
  let rec go acc = function
    | Loop l -> go acc l.body
    | Let l -> go acc l.body
    | Match m -> List.fold_left (fun acc (b : branch) -> go acc b.body) acc m.branches
    | Return _ | Continue _ -> acc
    | Continue_into c -> c :: acc
    | Resume r -> go (go acc r.value) r.body
    | Entry e -> go (go acc e.entered.body) e.scope
  in
  List.rev (go [] t)

let entries t =
  let rec go acc = function
    | Loop l -> go acc l.body
    | Let l -> go acc l.body
    | Match m -> List.fold_left (fun acc (b : branch) -> go acc b.body) acc m.branches
    | Return _ | Continue _ | Continue_into _ -> acc
    | Resume r -> go (go acc r.value) r.body
    | Entry e -> go (go (e.entered :: acc) e.entered.body) e.scope
  in
  List.rev (go [] t)

let rec map_returns f = function
  | Loop l -> Loop {l with body = map_returns f l.body}
  | Let l -> Let {l with body = map_returns f l.body}
  | Match m -> Match {m with branches = List.map (fun (b : branch) -> {b with body = map_returns f b.body}) m.branches}
  | Return v -> Return (f v)
  | (Continue _ | Continue_into _) as c -> c
  | Resume r -> Resume {r with body = map_returns f r.body}
  | Entry e -> Entry {e with scope = map_returns f e.scope}

(* The binders the body of the loop an entry enters stands under, inside
   the scope the entry stands in: a local fixpoint's name, and the loop's
   parameters. *)
let entered_binders (l : loop) =
  (match l.loop with Loop.Member _ -> 1 | Loop.Function _ -> 0) + List.length l.parameters

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
    | Resume r -> turns (depth + 1) (turns depth acc r.value) r.body
    | Entry e ->
      let within = turns (depth + entered_binders e.entered) acc e.entered.body in
      turns (depth + Option.cata (fun _ -> 1) 0 e.name) within e.scope
  in
  let turns = turns 0 [] l.body in
  List.init n (fun i ->
      List.for_all
        (fun (depth, arguments) ->
          match List.nth_opt arguments i with
          | Some (Miniml.MLrel (db, _)) -> Int.equal db (n - i + depth)
          | Some _ | None -> false )
        turns )
