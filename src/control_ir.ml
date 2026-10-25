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

(* The turns [t] continues a loop by, in order. *)
let turns t =
  let rec go acc = function
    | Loop l -> go acc l.body
    | Let l -> go acc l.body
    | Match m -> List.fold_left (fun acc (b : branch) -> go acc b.body) acc m.branches
    | Return _ -> acc
    | Continue c | Continue_into {next = c; _} -> c :: acc
    | Resume r -> go (go acc r.value) r.body
    | Entry e -> go (go acc e.entered.body) e.scope
  in
  List.rev (go [] t)

let continues t = List.map (fun c -> c.occurrence) (turns t)

let continues_of l t = List.filter_map (fun c -> if Loop.equal c.target l then Some c.occurrence else None) (turns t)

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

(* Where a value a binder inside a loop's parameters names comes from, as
   far as it comes from a parameter: stored in what the caller passed for
   it -- the parameter itself, or a constructor's field held behind the
   pointer of a value derived from it -- or merely derived from it, by
   fields, lets and coercions keeping its representation, and so perhaps
   held in a copy, which shares those pointers. *)
type provenance =
  | Stored of int
  | Derived of int

let parts_passed ~pointer_fields ~in_place (l : loop) =
  let n = List.length l.parameters in
  (* [env]: the provenance of each binder inside the loop's parameters,
     innermost first. *)
  let rec provenance env = function
    | Miniml.MLrel (db, _) -> Option.flatten (List.nth_opt env (db - 1))
    | Miniml.MLmagic (Miniml.Mcoerce (from, into), e) when in_place from into -> provenance env e
    | _ -> None
  in
  let derived env e = match provenance env e with Some (Stored i | Derived i) -> Some (Derived i) | None -> None in
  let unrelated k env = List.init k (fun _ -> None) @ env in
  (* The binders of a branch, [Prel 1] first, of its pattern matching a
     value derived from the parameter [whole]: one bound at a field its
     constructor stores behind the pointer is stored in what the caller
     passed, any other derived from it. *)
  let branch_provenance whole (b : branch) =
    let count = List.length b.binders in
    let bound = Array.make count None in
    let at fields j k =
      if k >= 1 && k <= count then bound.(k - 1) <- Some (if List.mem j fields then Stored whole else Derived whole)
    in
    let rec bind fields j = function
      | Miniml.Prel k -> at fields j k
      | Miniml.Pcons (r, ps) -> List.iteri (bind (Option.default [] (pointer_fields r))) ps
      | Miniml.Ptuple ps -> List.iteri (bind []) ps
      | Miniml.Pusual r -> List.iteri (at (Option.default [] (pointer_fields r))) (List.init count (fun i -> count - i))
      | Miniml.Pwild -> ()
    in
    bind [] (-1) b.pattern;
    Array.to_list bound
  in
  (* The provenance of the arguments of each Continue of [target] in [t]. *)
  let rec turns target env acc = function
    | Loop inner -> turns target env acc inner.body
    | Let b -> turns target (derived env b.value :: env) acc b.body
    | Match m ->
      List.fold_left
        (fun acc (b : branch) ->
          let binders =
            match derived env m.scrutinee with
            | Some (Stored i | Derived i) -> branch_provenance i b
            | None -> List.map (fun _ -> None) b.binders
          in
          turns target (binders @ env) acc b.body )
        acc m.branches
    | Return _ -> acc
    | Continue c | Continue_into {next = c; _} ->
      if Loop.equal c.target target then List.map (provenance env) c.arguments :: acc else acc
    | Resume r -> turns target (unrelated 1 env) (turns target env acc r.value) r.body
    | Entry e ->
      let scope = unrelated (Option.cata (fun _ -> 1) 0 e.name) env in
      let within = turns target (entered_env env scope e) acc e.entered.body in
      turns target scope within e.scope
  (* The binders the body of the loop [e] enters stands under, the entry
     standing under [env] and its scope under [scope]: each parameter
     derived from the parameter every Continue of the loop passes it a
     value derived from, the calls entering it and its own, the fixpoint's
     name from none. *)
  and entered_env env scope (e : entry) =
    let k = List.length e.entered.parameters in
    let within parameters = List.rev parameters @ unrelated (entered_binders e.entered - k) env in
    let origin arguments j =
      match List.nth_opt arguments j with Some (Some (Stored i | Derived i)) -> Some i | _ -> None
    in
    let entering = turns e.entered.loop scope [] e.scope in
    let agreed parameters =
      let arguments = entering @ turns e.entered.loop (within parameters) [] e.entered.body in
      List.mapi
        (fun j p ->
          match p with
          | Some (Derived i) when List.for_all (fun a -> Option.equal Int.equal (origin a j) (Some i)) arguments -> p
          | _ -> None )
        parameters
    in
    let rec settle parameters =
      let parameters' = agreed parameters in
      if parameters' = parameters then parameters else settle parameters'
    in
    let guessed j =
      match entering with a :: _ -> Option.map (fun i -> Derived i) (origin a j) | [] -> None
    in
    within (settle (List.init k guessed))
  in
  match turns l.loop (List.init n (fun k -> Some (Stored (n - 1 - k)))) [] l.body with
  | [] -> List.init n (fun _ -> false)
  | turns ->
    List.init n (fun i ->
        List.for_all
          (fun arguments -> match List.nth_opt arguments i with Some (Some (Stored j)) -> Int.equal i j | _ -> false)
          turns )

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
