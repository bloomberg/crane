(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter access requirements settled across calls.  See [access.mli]. *)

open Base.Mapping_descriptor

type access = Unused | Read_access | Write_access | Replace_access

type representation = Preferred | Canonical

type requirement = {
  access : access;
  representation : representation;
  invalidates : bool;
}

let least = {access = Unused; representation = Preferred; invalidates = false}

let rank = function Unused -> 0 | Read_access -> 1 | Write_access -> 2 | Replace_access -> 3

let join a b =
  { access = (if rank a.access >= rank b.access then a.access else b.access);
    representation = (if a.representation = Canonical || b.representation = Canonical then Canonical else Preferred);
    invalidates = a.invalidates || b.invalidates }

let equal (a : requirement) b = a = b

let canonical_read = {least with access = Read_access; representation = Canonical}

let rank_cap r = if rank r.access > rank Read_access then {r with access = Read_access} else r

let of_use ?(facts = []) ?name use =
  let names p = Some p.path_argument = name in
  let invalidated = List.exists (function Invalidates_views p -> names p | _ -> false) facts in
  let r =
    match use with
    | Ignore -> least
    | Read -> {least with access = Read_access}
    | Read_canonical -> canonical_read
    | Write -> {least with access = Write_access}
    | Write_canonical -> {least with access = Write_access; representation = Canonical}
    | Take ->
      let written = List.exists (function Writes_component (p, _) -> names p | _ -> false) facts in
      {least with access = (if written then Write_access else Read_access); representation = Canonical}
    | Replace | Opaque_use -> {access = Replace_access; representation = Canonical; invalidates = true}
  in
  if invalidated then {r with invalidates = true} else r

(* The variable [a] is, through the wrappers that do not change the value. *)
let rec direct = function
  | Core.Expr.Bound_variable {index = i; _} -> Some i
  | Core.Expr.Coerce {value = a; _} | Core.Expr.Boxed_value {value = a; _} | Core.Expr.Lambda_group_barrier {value = a; _}
    ->
    direct a
  | _ -> None

let read_off ?(sequential = false) ~settled n body =
  let reqs = Array.make n least in
  (* Under a closure -- a lambda, a local fixpoint -- a parameter is a copy
     the closure holds, which a write or a replacement there does not
     reach: the closure's use of it is at most a read.  A closure may
     outlive the call, so what it holds is canonical: a view would not keep
     its owner alive. *)
  let closure = ref false in
  let note p r =
    let r = if !closure then {(rank_cap r) with representation = Canonical} else r in
    match p with Some k when k >= 1 && k <= n -> reqs.(k - 1) <- join reqs.(k - 1) r | _ -> ()
  in
  let under_closure f =
    let saved = !closure in
    closure := true;
    f ();
    closure := saved
  in
  (* [env]: the parameter each binder introduced inside [body] stands for,
     innermost first; an index past them is a parameter itself. *)
  let param_of env i =
    let rec go env i =
      match env with
      | p :: rest -> if i = 1 then p else go rest (i - 1)
      | [] -> Some i
    in
    go env i
  in
  let rec walk env (e : Core.Expr.t) =
    match e with
    | Core.Expr.Bound_variable {index = i; _} -> note (param_of env i) canonical_read
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _}; arguments = args}
      when Base.Table.is_mapped_operation g ->
      let op = Base.Mapping_operation.find g in
      let uses = Base.Mapping_operation.call_argument_uses op in
      let names =
        List.map
          (fun k ->
            Option.map
              (fun (a : Base.Mapping_operation.argument) -> a.name)
              (List.find_opt (fun (a : Base.Mapping_operation.argument) -> a.binder = k) op.arguments) )
          op.call_binders
      in
      List.iteri
        (fun j a ->
          match (direct a, List.nth_opt uses j) with
          | Some i, Some (Some use) ->
            note (param_of env i) (of_use ~facts:op.facts ?name:(Option.bind (List.nth_opt names j) Fun.id) use)
          | _ -> walk env a )
        args
    (* In a sequential monad a bind's continuation is the rest of the
       statements, run in place: no closure holds what it names. *)
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _}; arguments = args}
      when sequential && Base.Table.is_bind g ->
      List.iter
        (function Core.Expr.Lambda {body = b; _} -> walk (None :: env) b | a -> walk env a)
        args
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _} as head; arguments = args}
      when (not (Escape.is_partial_app head args)) && Option.has_some (settled g) ->
      let summary = Option.get (settled g) in
      let m = List.length summary in
      List.iteri
        (fun j a ->
          match direct a with
          | Some i when j < m -> note (param_of env i) (List.nth summary (m - 1 - j))
          | _ -> walk env a )
        args
    | Core.Expr.Apply {callee = head; arguments = args} ->
      walk env head;
      List.iter (walk env) args
    | Core.Expr.Let {value = rhs; body = cont; _} -> (
      match direct rhs with
      | Some i -> walk (param_of env i :: env) cont
      | None ->
        walk env rhs;
        walk (None :: env) cont )
    | Core.Expr.Lambda {body = b; _} -> under_closure (fun () -> walk (None :: env) b)
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      walk env scrut;
      Array.iter
        (fun {Core.Match.Branch.binders = ids; body = b; _} -> walk (List.map (fun _ -> None) ids @ env) b)
        branches
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let k = Array.length (Core.Recursion.Group.functions rec_group) in
      let env' = List.init k (fun _ -> None) @ env in
      under_closure (fun () -> Array.iter (walk env') (Core.Recursion.Group.bodies rec_group))
    | Core.Expr.Construct {arguments = ts; _} | Core.Expr.Tuple ts -> List.iter (walk env) ts
    | Core.Expr.Coerce {value = a; _} | Core.Expr.Boxed_value {value = a; _} | Core.Expr.Lambda_group_barrier {value = a; _}
      ->
      walk env a
    | Core.Expr.Persistent_array {elements; default} ->
      Array.iter (walk env) elements;
      walk env default
    | Core.Expr.Global _ | Core.Expr.Runtime_error _ | Core.Expr.Erased_value _ | Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _ | Core.Expr.Float64 _ | Core.Expr.String _ ->
      ()
  in
  (* A body that is one fixpoint applied to the parameters as they are --
     a [Fixpoint] in a section, whose section variables it reads -- is the
     function itself, its recursive calls calls of it: what it names of
     the enclosing parameters is not held by a closure.  Its own
     parameters stand for the arguments it is applied to. *)
  let rec peel k (e : Core.Expr.t) =
    match e with
    | Core.Expr.Lambda {body = b; _} when k > 0 -> peel (k - 1) b
    | e -> if k = 0 then Some e else None
  in
  ( match body with
  | Core.Expr.Apply {callee = Core.Expr.Fixpoint g; arguments = args}
    when Array.length (Core.Recursion.Group.bodies g) = 1 && List.for_all (fun a -> Option.has_some (direct a)) args
    -> (
      let m = List.length args in
      match peel m (Core.Recursion.Group.bodies g).(0) with
      | Some inner ->
        let own = List.rev_map (fun a -> param_of [] (Option.get (direct a))) args in
        walk (own @ [None]) inner
      | None -> walk [] body )
  | _ -> walk [] body );
  Array.to_list reqs

type t = {
  summaries : (Names.GlobRef.t * requirement list) list;
  pinned : Core.Ref.User.Set.t;
}

let empty = {summaries = []; pinned = Core.Ref.User.Set.empty}

(* The globals [struc] names other than as the head of a saturated call. *)
let named_as_values struc =
  let found = ref Core.Ref.User.Set.empty in
  let rec scan (e : Core.Expr.t) =
    match e with
    | Core.Expr.Global {callee = g; _} -> found := Core.Ref.User.Set.add g !found
    | Core.Expr.Apply {callee = Core.Expr.Global _ as head; arguments = args} when not (Escape.is_partial_app head args)
      ->
      List.iter scan args
    | e -> Base.Core_util.ast_iter scan e
  in
  Core_passes.Modutil.struct_iter
    (fun d -> List.iter (fun (fd : Core.Recursion.Definition.t) -> scan fd.body) (Base.Core_util.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  !found

let exported ~pinned g reqs =
  if Core.Ref.User.Set.mem g pinned then List.map (fun r -> {(rank_cap r) with representation = Canonical}) reqs
  else reqs

let summarize ?(receiver = fun _ -> None) struc =
  let fns = Ownership.functions struc in
  let pinned =
    List.fold_left
      (fun s (r, _, _, _) -> if Option.has_some (receiver r) then Core.Ref.User.Set.add r s else s)
      (named_as_values struc) fns
  in
  (* Every summary starts at the least requirement, so that a call met
     before its callee is summarized -- a recursive one -- reads that, not
     the canonical read of an unknown callee: the least fixed point. *)
  let summaries =
    ref
      (List.fold_left
         (fun m (r, b, ty, _) ->
           let params, _ = Base.Type_util.declared_parameters ty b in
           Core.Ref.User.Map.add r (List.map (fun _ -> least) params) m)
         Core.Ref.User.Map.empty fns)
  in
  let settled g = Option.map (exported ~pinned g) (Core.Ref.User.Map.find_opt g !summaries) in
  (* Each round can only raise requirements in a finite lattice, so it
     stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b, ty, _) ->
        let params, body = Base.Type_util.declared_parameters ty b in
        let sequential = Effects.declaration_mode ty = Effects.Sequential in
        let reqs = Base.Table.with_decl_ref r (fun () -> read_off ~sequential ~settled (List.length params) body) in
        if not (Option.equal (List.equal equal) (Core.Ref.User.Map.find_opt r !summaries) (Some reqs)) then (
          changed := true;
          summaries := Core.Ref.User.Map.add r reqs !summaries ) )
      fns;
    if !changed then round ()
  in
  round ();
  if Option.has_some (Sys.getenv_opt "CRANE_TRACE_ACCESS") then
    Core.Ref.User.Map.iter
      (fun r reqs ->
        let access = function
          | Unused -> "unused"
          | Read_access -> "read"
          | Write_access -> "write"
          | Replace_access -> "replace"
        in
        let show q =
          access q.access ^ (if q.representation = Canonical then "!" else "") ^ if q.invalidates then "~" else ""
        in
        Printf.eprintf "access %s%s: %s\n%!"
          (Pp.string_of_ppcmds (Base.Table.safe_pr_global r))
          (if Core.Ref.User.Set.mem r pinned then " (pinned)" else "")
          (String.concat " " (List.rev_map show reqs)) )
      !summaries;
  {summaries = Core.Ref.User.Map.bindings !summaries; pinned}

let physical ~reference_allowed ?(view_allowed = false) (p : Base.Mapping_plan.t) r =
  let view k = view_allowed && r.representation = Preferred && Base.Mapping_plan.has_view p k in
  let form =
    match r.access with
    | Replace_access -> Base.Mapping_plan.replace_form p
    | Write_access when view Base.Mapping_plan.Write_view -> Base.Mapping_plan.Physical_view Write_view
    | Write_access -> Base.Mapping_plan.write_through p
    | Read_access when view Base.Mapping_plan.Read_view -> Base.Mapping_plan.Physical_view Read_view
    | Read_access | Unused -> Base.Mapping_plan.As_read
  in
  match form with
  | Base.Mapping_plan.Physical_mutable_reference when not reference_allowed -> Base.Mapping_plan.Physical_value
  | form -> form
