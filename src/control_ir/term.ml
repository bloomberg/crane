(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t =
  | Loop of loop
  | Let of let_
  | Match of match_
  | Return of Core.Expr.t
  | Continue of continue_
  | Continue_into of continue_into
  | Resume of resume
  | Entry of entry

and loop = {
  loop : Loop.t;
  parameters : (Core.Binder_name.t * Core.Type.t) list;
  body : t;
}

and let_ = {
  binder : Core.Binder_name.t;
  binder_type : Core.Type.t;
  value : Core.Expr.t;
  body : t;
}

and match_ = {
  scrutinee_type : Core.Type.t;
  scrutinee : Core.Expr.t;
  branches : branch list;
}

and branch = {
  binders : (Core.Binder_name.t * Core.Type.t) list;
  result_type : Core.Type.t;
  pattern : Core.Pattern.t;
  body : t;
}

and continue_ = {
  target : Loop.t;
  occurrence : Core.Occurrence.t;
  arguments : Core.Expr.t list;
}

and continue_into = {
  cells : cell list;
  next : continue_;
}

and cell = {
  constructor : Names.GlobRef.t;
  hole : int;
  arguments : Core.Expr.t list;
}

and resume = {
  binder : Core.Binder_name.t;
  binder_type : Core.Type.t;
  value : t;
  body : t;
}

and entry = {
  entered : loop;
  name : (Core.Binder_name.t * Core.Type.t) option;
  scope : t;
}

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
   pointer of a value derived from it, the value lying in the field itself
   or, [Cell], in a cell the field points at -- or merely derived from it,
   by fields, lets and coercions keeping its representation, and so perhaps
   held in a copy, which shares those pointers.  A copy of a binder stored
   in a cell, the field's handle, points at that cell still; a copy of any
   other is a value of its own. *)
type provenance =
  | Stored of int
  | Cell of int
  | Derived of int

let origin_of = function Stored i | Cell i | Derived i -> i

(* The provenance of a binder's copy, kept in a frame. *)
let kept = function Cell i -> Cell i | Stored i | Derived i -> Derived i

(* The provenance of [e] under [env], the provenance of each binder inside
   a loop's parameters, innermost first. *)
let rec provenance ~in_place env = function
  | Core.Expr.Bound_variable {index = db; _} -> Option.flatten (List.nth_opt env (db - 1))
  | Core.Expr.Coerce {source_type = from; target_type = into; value = e; _} when in_place from into ->
    provenance ~in_place env e
  | _ -> None

(* Each Continue of the loop [l], in order, with the provenance of each
   binder it stands under inside [l]'s parameters, innermost first: of
   the fields [pointer_fields] gives, those [cell_fields] gives hold their
   value in a cell. *)
let turn_provenances ~pointer_fields ~cell_fields ~in_place (l : loop) =
  let n = List.length l.parameters in
  let provenance = provenance ~in_place in
  let derived env e = Option.map (fun p -> Derived (origin_of p)) (provenance env e) in
  let unrelated k env = List.init k (fun _ -> None) @ env in
  (* The binders of a branch, [Core.Pattern.Bound_variable 1] first, of its pattern matching a
     value derived from the parameter [whole]: one bound at a field its
     constructor stores behind the pointer is stored in what the caller
     passed, any other derived from it. *)
  let branch_provenance whole (b : branch) =
    let count = List.length b.binders in
    let bound = Array.make count None in
    let at (fields, cells) j k =
      if k >= 1 && k <= count then
        bound.(k - 1) <-
          Some (if List.mem j cells then Cell whole else if List.mem j fields then Stored whole else Derived whole)
    in
    let rec bind fields j = function
      | Core.Pattern.Bound_variable k -> at fields j k
      | Core.Pattern.Constructor {constructor = r; fields = ps} ->
        List.iteri (bind (Option.default [] (pointer_fields r), Option.default [] (cell_fields r))) ps
      | Core.Pattern.Tuple ps -> List.iteri (bind ([], [])) ps
      | Core.Pattern.Wildcard -> ()
    in
    bind ([], []) (-1) b.pattern;
    Array.to_list bound
  in
  (* Each Continue of [target] in [t], with the provenance of the binders it
     stands under. *)
  let rec turns target env acc = function
    | Loop inner -> turns target env acc inner.body
    | Let b -> turns target (derived env b.value :: env) acc b.body
    | Match m ->
      List.fold_left
        (fun acc (b : branch) ->
          let binders =
            match derived env m.scrutinee with
            | Some p -> branch_provenance (origin_of p) b
            | None -> List.map (fun _ -> None) b.binders
          in
          turns target (binders @ env) acc b.body )
        acc m.branches
    | Return _ -> acc
    | Continue c | Continue_into {next = c; _} -> if Loop.equal c.target target then (c, env) :: acc else acc
    | Resume r -> turns target (unrelated 1 env) (turns target env acc r.value) r.body
    | Entry e ->
      let scope = unrelated (Option.cata (fun _ -> 1) 0 e.name) env in
      let within = turns target (entered_env env scope e) acc e.entered.body in
      turns target scope within e.scope
  (* The binders the body of the loop [e] enters stands under, the entry
     standing under [env] and its scope under [scope]: each parameter
     derived from the parameter every Continue of the loop passes it a
     value derived from, the calls entering it and its own, the fixpoint's
     name from none, and what it reads of the scope as the copy a frame
     kept of it ({!kept}). *)
  and entered_env env scope (e : entry) =
    let k = List.length e.entered.parameters in
    let kept_env = List.map (Option.map kept) env in
    let within parameters = List.rev parameters @ unrelated (entered_binders e.entered - k) kept_env in
    let origin arguments j = match List.nth_opt arguments j with Some (Some p) -> Some (origin_of p) | _ -> None in
    let arguments_of = List.map (fun ((c : continue_), env) -> List.map (provenance env) c.arguments) in
    let entering = arguments_of (turns e.entered.loop scope [] e.scope) in
    let agreed parameters =
      let arguments = entering @ arguments_of (turns e.entered.loop (within parameters) [] e.entered.body) in
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
  List.rev (turns l.loop (List.init n (fun k -> Some (Stored (n - 1 - k)))) [] l.body)

(* For each parameter of the loop [l], whether every Continue of [l] passes
   it an argument whose provenance [accepted] accepts of its position;
   [false] for each where none continues [l]. *)
let passed ~accepted ~pointer_fields ~cell_fields ~in_place (l : loop) =
  let n = List.length l.parameters in
  match turn_provenances ~pointer_fields ~cell_fields ~in_place l with
  | [] -> List.init n (fun _ -> false)
  | turns ->
    List.init n (fun i ->
        List.for_all
          (fun ((c : continue_), env) ->
            match Option.map (provenance ~in_place env) (List.nth_opt c.arguments i) with
            | Some (Some p) -> accepted i p
            | Some None | None -> false )
          turns )

let parts_passed = passed ~accepted:(fun i -> function Stored j | Cell j -> Int.equal i j | Derived _ -> false)

(* Whether a field holds its value in a cell matters to no derivation. *)
let derived_passed ~pointer_fields = passed ~accepted:(fun _ _ -> true) ~pointer_fields ~cell_fields:pointer_fields

type rebuilt = {
  turn : Core.Occurrence.t;
  read_elsewhere : bool;
}

let rebuilt ~pointer_fields ~in_place (l : loop) i =
  let of_parameter = function Some p -> Int.equal i (origin_of p) | None -> false in
  (* Whether [e], under [env], reads the parameter or a binder derived from
     it. *)
  let reads env e =
    let rec go depth = function
      | Core.Expr.Bound_variable {index = db; _} ->
        db > depth && of_parameter (Option.flatten (List.nth_opt env (db - depth - 1)))
      | Core.Expr.Lambda {body = b; _} -> go (depth + 1) b
      | Core.Expr.Let {value = a; body = b; _} -> go depth a || go (depth + 1) b
      | Core.Expr.Match {scrutinee = s; branches; _} ->
        go depth s
        || Array.exists
             (fun {Core.Match.Branch.binders = ids; body = b; _} -> go (depth + List.length ids) b)
             branches
      | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
        let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
        Array.exists (go (depth + Array.length ids)) funs
      | Core.Expr.Apply {callee = f; arguments = args} -> go depth f || List.exists (go depth) args
      | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.exists (go depth) args
      | Core.Expr.Coerce {value = e; _}
      | Core.Expr.Boxed_value {value = e; _}
      | Core.Expr.Lambda_group_barrier {value = e; _} ->
        go depth e
      | Core.Expr.Persistent_array {elements; default} -> Array.exists (go depth) elements || go depth default
      | Core.Expr.Global _
      | Core.Expr.Runtime_error _
      | Core.Expr.Erased_value _
      | Core.Expr.Axiom_value _
      | Core.Expr.UInt63 _
      | Core.Expr.Numeral _
      | Core.Expr.Float64 _
      | Core.Expr.String _ -> false
    in
    go 0 e
  in
  List.filter_map
    (fun ((c : continue_), env) ->
      match List.nth_opt c.arguments i with
      | Some a when Option.is_empty (provenance ~in_place env a) ->
        let others = List.filteri (fun j _ -> j <> i) c.arguments in
        Some {turn = c.occurrence; read_elsewhere = List.exists (reads env) others}
      | Some _ | None -> None )
    (turn_provenances ~pointer_fields ~cell_fields:pointer_fields ~in_place l)

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
          | Some (Core.Expr.Bound_variable {index = db; _}) -> Int.equal db (n - i + depth)
          | Some _ | None -> false )
        turns )
