(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small closed definitions evaluated at extraction time.  See
    [ml_const_eval.mli]. *)

open Names
open Miniml
module MS = Mapping_semantics

(** Why an evaluation stopped: each leaves the definition unchanged. *)
type stop = Unknown_operation | Step_limit | Size_limit

exception Stop of stop

(** A value: the result of evaluating a term.  It holds no unevaluated
    call, resource or C++ text -- a closure holds a term, but only one a
    later application evaluates under the same rules. *)
type value =
  | Nat of Z.t * MS.width
  | Con of GlobRef.t * value list
  | Clo of value list * ml_ast  (** a lambda's body, under its environment *)
  | Fix of value list * int * int * ml_ast array
      (** the [i]-th of [k] local fixpoints, under its environment *)
  | Prim of MS.unsigned_op * MS.width * value list
      (** a declared operation, and the arguments it has so far *)
  | Erased  (** an erased argument, which nothing reads *)

(** The resources one evaluation may spend. *)
type budget = {mutable steps : int; mutable size : int}

let step_limit = 20_000

let size_limit = 4_096

let tick b =
  b.steps <- b.steps - 1;
  if b.steps < 0 then raise_notrace (Stop Step_limit)

let grow b n =
  b.size <- b.size - n;
  if b.size < 0 then raise_notrace (Stop Size_limit)

let unknown () = raise_notrace (Stop Unknown_operation)

let wrap w n = Z.logand n (MS.max_value w)

let bool_ctor b =
  Rocqlib.lib_ref (if b then "core.bool.true" else "core.bool.false")

let rec run b defs env e =
  tick b;
  match e with
  | MLrel i -> ( match List.nth_opt env (i - 1) with Some v -> v | None -> unknown () )
  | MLlam (_, _, body) -> Clo (env, body)
  | MLletin (_, _, a, body) -> run b defs (run b defs env a :: env) body
  | MLapp (f, args) -> apply b defs (run b defs env f) (List.map (run b defs env) args)
  | MLglob (r, _) -> global b defs r
  | MLcons (_, c, args) -> construct b c (List.map (run b defs env) args)
  | MLcase (_, s, brs) -> case b defs env (run b defs env s) brs
  | MLfix (i, ids, bodies, false) -> Fix (env, i, Array.length ids, bodies)
  | MLmagic (_, a) -> run b defs env a
  | MLdummy _ -> Erased
  | _ -> unknown ()

and construct b c args =
  match c with
  | GlobRef.ConstructRef (ind, _) -> (
    match (MS.nat_width ind, args) with
    | Some w, [] -> Nat (Z.zero, w)
    | Some w, [Nat (n, _)] -> Nat (wrap w (Z.succ n), w)
    | Some _, _ -> unknown ()
    | None, _ ->
      grow b 1;
      Con (c, args) )
  | _ -> unknown ()

and global b defs r =
  match MS.find r with
  | Some (MS.Unsigned (op, w)) -> Prim (op, w, [])
  | Some _ -> unknown ()
  | None ->
    if Table.is_custom r then unknown ()
    else (
      match Table.Refmap'.find_opt r defs with
      | Some body -> run b defs [] body
      | None -> unknown () )

and apply b defs f args =
  match (f, args) with
  | _, [] -> f
  | Clo (env, body), a :: rest -> apply b defs (run b defs (a :: env) body) rest
  | Fix (env, i, k, bodies), _ ->
    (* Under the group, index [j] names the fixpoint [k - j]. *)
    let group = List.init k (fun j -> Fix (env, k - 1 - j, k, bodies)) in
    apply b defs (run b defs (group @ env) bodies.(i)) args
  | Prim (op, w, have), a :: rest -> (
    let have = match a with Erased -> have | _ -> have @ [a] in
    match have with
    | [Nat (x, _); Nat (y, _)] -> apply b defs (prim op w x y) rest
    | [_; _] -> unknown ()
    | _ -> apply b defs (Prim (op, w, have)) rest )
  | (Nat _ | Con _ | Erased), _ :: _ -> unknown ()

and prim op w x y =
  let n v = Nat (wrap w v, w) and bool v = Con (bool_ctor v, []) in
  match op with
  | MS.Add -> n (Z.add x y)
  | MS.Mul -> n (Z.mul x y)
  | MS.Sub_truncated -> n (if Z.lt x y then Z.zero else Z.sub x y)
  | MS.Div -> n (if Z.equal y Z.zero then Z.zero else Z.div x y)
  | MS.Mod -> n (if Z.equal y Z.zero then x else Z.rem x y)
  | MS.Eqb -> bool (Z.equal x y)
  | MS.Ltb -> bool (Z.lt x y)
  | MS.Leb -> bool (Z.leq x y)
  | MS.Max -> n (Z.max x y)
  | MS.Min -> n (Z.min x y)

and case b defs env v brs =
  (* The constructor [v] is, and what it carries, in order. *)
  let head, fields =
    match v with
    | Con (c, fs) -> (c, fs)
    | Nat (n, w) -> (
      (* A declared natural is its constructor too: [O], or [S] of one less. *)
      let succ_or_zero =
        Array.to_list brs
        |> List.find_map (fun (_, _, p, _) ->
               match p with
               | Pusual (GlobRef.ConstructRef (ind, _) as c)
               | Pcons ((GlobRef.ConstructRef (ind, _) as c), _)
                 when MS.nat_width ind <> None ->
                 Some (ind, c)
               | _ -> None)
      in
      match succ_or_zero with
      | Some ((mind, i), _) ->
        let zero = GlobRef.ConstructRef ((mind, i), 1)
        and succ = GlobRef.ConstructRef ((mind, i), 2) in
        if Z.equal n Z.zero then (zero, []) else (succ, [Nat (Z.pred n, w)])
      | None -> unknown () )
    | _ -> unknown ()
  in
  let rec pick i =
    if i >= Array.length brs then unknown ()
    else
      let ids, _, p, body = brs.(i) in
      match p with
      | Pusual c when GlobRef.CanOrd.equal c head -> run b defs (List.rev fields @ env) body
      | Pcons (c, ps)
        when GlobRef.CanOrd.equal c head
             && List.length ps = List.length ids
             && List.for_all2 (fun p k -> p = Prel k) ps
                  (List.rev (List.init (List.length ps) (fun k -> k + 1))) ->
        run b defs (List.rev fields @ env) body
      | Pwild when ids = [] -> run b defs env body
      | _ -> pick (i + 1)
  in
  pick 0

(* The literal for [v], at type [ty], when it is one a definition can be
   rewritten to: a natural of a declared type, or a constant constructor. *)
let quote ty v =
  match (v, ty) with
  | Nat (n, _), Tglob (GlobRef.IndRef (mind, i), _, _) when Z.leq n (Z.of_int size_limit) ->
    let zero = GlobRef.ConstructRef ((mind, i), 1)
    and succ = GlobRef.ConstructRef ((mind, i), 2) in
    let rec chain k acc =
      if k = 0 then acc else chain (k - 1) (MLcons (ty, succ, [acc]))
    in
    Some (chain (Z.to_int n) (MLcons (ty, zero, [])))
  | Con (c, []), Tglob (GlobRef.IndRef _, [], _) -> Some (MLcons (ty, c, []))
  | _ -> None

(* A definition worth evaluating: a value, not a function, not already a
   literal, of a type a literal can be written at. *)
let candidate ty body =
  ( match body with MLlam _ | MLcons (_, _, []) -> false | _ -> true )
  &&
  match ty with
  | Tglob (GlobRef.IndRef ind, [], _) -> MS.nat_width ind <> None || Table.is_enum_inductive (GlobRef.IndRef ind)
  | _ -> false

let evaluate defs ty body =
  if not (candidate ty body) then None
  else
    let b = {steps = step_limit; size = size_limit} in
    match run b defs [] body with
    | v -> quote ty v
    | exception Stop _ -> None

let structure struc =
  let defs = Ml_declared.definitions struc in
  Ml_declared.map_decls
    (function
      | Dterm (r, body, ty) as d -> (
        match evaluate defs ty body with
        | Some lit -> Dterm (r, lit, ty)
        | None -> d )
      | d -> d)
    struc
