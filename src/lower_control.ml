(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml
open Control_ir
open Control_ir.Term

type t = (Loop.t * Term.t) list

let empty = []

let rec strip = function MLmagic (_, e) -> strip e | e -> e

(* The occurrence of the call headed by [f]: the global's use, or the read
   of the member. *)
let occurrence f =
  match strip f with
  | MLglob use -> Some (Global_use.occurrence use)
  | MLrel (_, read) -> Some read
  | _ -> None

(* [body], under the parameters of the loop [target], as that loop:
   [callee ~depth f] is the number of parameters of the loop's function
   where [f], under [depth] binders inside them, names it, and [inlined use]
   the parameters, innermost first, and body of the partner whose call
   [use] heads, where Loopify continues in the partner's body
   ({!Recursion_plan.inlinings}). *)
let tail_loop ?(inlined = fun _ -> None) ?(modulo_cons = false) ~effects ~target ~callee body =
  let effect_ = Recursion_plan.sequential effects in
  let call ~depth = function
    | MLapp (f, args) when callee ~depth f = Some (List.length args) -> Option.map (fun o -> (o, args)) (occurrence f)
    | _ -> None
  in
  (* The constructors [e] builds around one call of the loop's function,
     outermost first, as {!Recursion_plan.strategy} reads a chain: each
     holds the next in the one argument that calls the function, the
     innermost holding the call itself, and none calls it elsewhere. *)
  let rec chain depth e =
    match e with
    | MLcons (_, constructor, args) -> (
      let calling = List.filteri (fun _ (_, a) -> calls ~depth a > 0) (List.mapi (fun i a -> (i, a)) args) in
      match calling with
      | [(hole, a)] when calls ~depth a = 1 -> (
        let cell = {constructor; hole; arguments = List.filteri (fun i _ -> i <> hole) args} in
        match call ~depth a with
        | Some (occurrence, arguments) -> Some {cells = [cell]; next = {target; occurrence; arguments}}
        | None -> Option.map (fun c -> {c with cells = cell :: c.cells}) (chain depth a) )
      | _ -> None )
    | _ -> None
  (* The calls of the loop's function in [e], under [depth] binders. *)
  and calls ~depth e =
    let n = ref 0 in
    let rec walk depth e =
      if Option.has_some (callee ~depth e) then incr n
      else
        match e with
        | MLapp (f, args) ->
          walk depth f;
          List.iter (walk depth) args
        | MLlam (_, _, b) -> walk (depth + 1) b
        | MLletin (_, _, a, b, _) ->
          walk depth a;
          walk (depth + 1) b
        | MLcase (_, s, branches) ->
          walk depth s;
          Array.iter (fun (ids, _, _, b) -> walk (depth + List.length ids) b) branches
        | MLfix (_, ids, funs, _, _) -> Array.iter (walk (depth + Array.length ids)) funs
        | e -> Mlutil.ast_iter (walk depth) e
    in
    walk depth e;
    !n
  in
  let rec lower depth e =
    match recognise depth e with
    | t when continues t = [] -> Return e
    | t -> t
  and recognise depth e =
    let continue_ f arguments =
      match occurrence f with
      | Some occurrence -> Continue {target; occurrence; arguments}
      | None -> Return e
    in
    match e with
    | f when callee ~depth f = Some 0 -> continue_ f []
    | MLapp (f, args) when callee ~depth f = Some (List.length args) -> continue_ f args
    | MLapp (MLglob use, args) when Option.has_some (inlined use) -> (
      let params, partner = Option.get (inlined use) in
      (* The partner's parameters bound to the arguments, its body under
         them, which names nothing else of the scope it is inlined in. *)
      let rec bind depth lift params args =
        match (params, args) with
        | (x, ty) :: params, a :: args ->
          Let
            { binder = x;
              binder_type = ty;
              value = Mlutil.ast_lift lift a;
              body = bind (depth + 1) (lift + 1) params args }
        | [], [] -> lower depth partner
        | _ -> Return e
      in
      match bind depth 0 (List.rev params) args with
      | Return _ -> Return e
      | t -> t )
    | MLcons (_, c, [a]) when Recursion_plan.identity c -> lower depth a
    | MLapp (MLglob use, [a]) when Recursion_plan.identity use.callee && Table.to_inline use.callee ->
      lower depth a
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match List.rev args with
      | MLlam (x, ty, k) :: action :: _ ->
        Let {binder = x; binder_type = ty; value = action; body = lower (depth + 1) k}
      | _ -> Return e )
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Return -> (
      match List.rev args with value :: _ -> lower depth value | [] -> Return e )
    | MLapp ((MLlam _ as f), args) ->
      let rec enter depth f args =
        match (f, args) with
        | MLlam (x, ty, b), a :: rest ->
          Let {binder = x; binder_type = ty; value = a; body = enter (depth + 1) b rest}
        | MLlam _, [] -> Return e
        | b, [] -> lower depth b
        | _, _ :: _ -> Return e
      in
      enter depth f args
    | MLletin (x, ty, a, b, _) -> Let {binder = x; binder_type = ty; value = a; body = lower (depth + 1) b}
    | MLcase (ty, s, branches) ->
      Match
        { scrutinee_type = ty;
          scrutinee = s;
          branches =
            Array.to_list
              (Array.map
                 (fun (ids, result_type, pattern, b) ->
                   {binders = ids; result_type; pattern; body = lower (depth + List.length ids) b} )
                 branches ) }
    | MLmagic (m, a) -> map_returns (fun v -> MLmagic (m, v)) (lower depth a)
    | MLcons _ when modulo_cons -> (
      match chain depth e with Some c -> Continue_into c | None -> Return e )
    | e -> Return e
  in
  lower 0 body

(* The fixpoints in [e] whose occurrence [wanted] holds. *)
let rec fixpoints wanted acc e =
  let acc =
    match e with
    | MLfix (_, _, funs, _, occ) when List.exists (Occurrence.equal occ) wanted -> (occ, funs) :: acc
    | _ -> acc
  in
  let acc = ref acc in
  Mlutil.ast_iter (fun e -> acc := fixpoints wanted !acc e) e;
  !acc

let lower plan program =
  let struc = Core.structure program in
  let effects = Core_effects.analyze struc in
  let functions, locals = Recursion_plan.tail_loops plan in
  let modulo_cons, local_modulo_cons = Recursion_plan.modulo_cons_loops plan in
  let defs = ref Names.GlobRef.Map_env.empty in
  Modutil.struct_iter
    (fun d ->
      List.iter
        (fun (fd : ml_fix_def) -> defs := Names.GlobRef.Map_env.add fd.fd_ref fd !defs)
        (Mlutil.term_defs d) )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let generated (fd : ml_fix_def) =
    Ml_type_util.declared_parameters (Mlutil.type_simpl fd.fd_type) (Mlutil.read_spines fd.fd_body)
  in
  (* The body of a function lowered tail modulo cons, its partners' as they
     are inlined into it, are read with Normalize's temporaries put back, as
     the plan reads its chains. *)
  let read ~builds fd =
    let parameters, inner = generated fd in
    (parameters, if builds then Recursion_plan.restore_temporaries inner else inner)
  in
  let inlined ~builds r (use : global_use) =
    let occurrence = Global_use.occurrence use in
    List.find_map
      (fun (i : Recursion_plan.inlining) ->
        if List.exists (Occurrence.equal occurrence) i.continued then
          Option.map (read ~builds) (Names.GlobRef.Map_env.find_opt i.partner !defs)
        else None )
      (Recursion_plan.inlinings_in plan r)
  in
  let loops = ref [] in
  let add target parameters body =
    if not (List.exists (fun (l, _) -> Loop.equal l target) !loops) then
      loops := (target, Loop {loop = target; parameters = List.rev parameters; body}) :: !loops
  in
  Modutil.struct_iter
    (fun d ->
      List.iter
        (fun (fd : ml_fix_def) ->
          let body = Mlutil.read_spines fd.fd_body in
          let builds = List.exists (Names.GlobRef.UserOrd.equal fd.fd_ref) modulo_cons in
          if builds || List.exists (Names.GlobRef.UserOrd.equal fd.fd_ref) functions then begin
            let parameters, inner = read ~builds fd in
            let arity = List.length parameters in
            let callee ~depth:_ = function
              | MLglob use when Names.GlobRef.UserOrd.equal use.callee fd.fd_ref -> Some arity
              | _ -> None
            in
            let target = Loop.Function fd.fd_ref in
            add target parameters
              (tail_loop ~inlined:(inlined ~builds fd.fd_ref) ~modulo_cons:builds ~effects ~target ~callee inner)
          end;
          List.iter
            (fun (occ, funs) ->
              let builds = List.exists (Occurrence.equal occ) local_modulo_cons in
              let parameters, inner = Mlutil.collect_lams funs.(0) in
              let inner = if builds then Recursion_plan.restore_temporaries inner else inner in
              let arity = List.length parameters in
              let callee ~depth f =
                match strip f with
                | MLrel (db, _) when db = arity + 1 + depth -> Some arity
                | _ -> None
              in
              let target = Loop.Member (occ, 0) in
              add target parameters (tail_loop ~modulo_cons:builds ~effects ~target ~callee inner) )
            (List.rev (fixpoints (locals @ local_modulo_cons) [] body)) )
        (Mlutil.term_defs d) )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  List.rev !loops

let installed : t ref = State.cell State.Extraction empty

let install t = installed := t

let loop l = List.find_map (fun (l', t) -> if Loop.equal l l' then Some t else None) !installed
