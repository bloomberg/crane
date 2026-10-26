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

(* What the machine of a loop adopts as a further entry
   ({!Control_ir.Term.entry}): the local fixpoint of one member at an
   occurrence, or a partner's body, its parameters innermost first, run in
   place of its calls [invoked]. *)
type adoption =
  | Fixpoint of Occurrence.t
  | Partner of {
      partner : Names.GlobRef.t;
      invoked : Occurrence.t list;
      parameters : (ml_ident * ml_type) list;
      body : ml_ast;
    }

(* [body], under the parameters of the loop [target], as that loop:
   [callee ~depth f] is the number of parameters of the loop's function
   where [f], under [depth] binders inside them, names it, and [inlined use]
   the parameters, innermost first, and body of the partner whose call
   [use] heads, where Loopify continues in the partner's body
   ({!Recursion_plan.inlinings}).  A machine [adopted] has that entry too. *)
let tail_loop ?(inlined = fun _ -> None) ?(modulo_cons = false) ?(frames = false) ?adopted ~effects ~target ~callee
    body =
  let effect_ = Recursion_plan.sequential effects in
  (* The loops a read names, by the binders it stands under: the loop it
     continues, and its number of parameters. *)
  let own ~depth f = Option.map (fun n -> (target, n)) (callee ~depth f) in
  let adopts o = match adopted with Some (Fixpoint o') -> Occurrence.equal o o' | Some (Partner _) | None -> false in
  let rec lower callee depth e =
    match recognise callee depth e with
    | t when continues t = [] -> Return e
    | t -> t
  (* The loop [f] names, under [depth] binders, where it takes [n]
     arguments. *)
  and named callee ~depth f n =
    match callee ~depth f with Some (l, n') when n = n' -> Some l | Some _ | None -> None
  and call callee ~depth = function
    | MLapp (f, args) ->
      Option.bind (named callee ~depth f (List.length args)) (fun l ->
          Option.map (fun o -> (l, o, args)) (occurrence f) )
    | _ -> None
  (* The constructors [e] builds around one call of the loop's function,
     outermost first, as {!Recursion_plan.strategy} reads a chain: each
     holds the next in the one argument that calls the function, the
     innermost holding the call itself, and none calls it elsewhere. *)
  and chain callee depth e =
    match e with
    | MLcons (_, constructor, args) -> (
      let calling = List.filteri (fun _ (_, a) -> calls callee ~depth a > 0) (List.mapi (fun i a -> (i, a)) args) in
      match calling with
      | [(hole, a)] when calls callee ~depth a = 1 -> (
        let cell = {constructor; hole; arguments = List.filteri (fun i _ -> i <> hole) args} in
        match call callee ~depth a with
        | Some (target, occurrence, arguments) -> Some {cells = [cell]; next = {target; occurrence; arguments}}
        | None -> Option.map (fun c -> {c with cells = cell :: c.cells}) (chain callee depth a) )
      | _ -> None )
    | _ -> None
  (* The calls of the loops [callee] names in [e], under [depth] binders,
     the fixpoint adopted counting as one where it is applied. *)
  and calls callee ~depth e =
    let n = ref 0 in
    let rec walk depth e =
      if Option.has_some (callee ~depth e) then incr n
      else
        match e with
        | MLapp (MLfix (_, _, _, _, o), args) when adopts o ->
          incr n;
          List.iter (walk depth) args
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
  (* The function of the fixpoint [fix] adopted at [occurrence], in the
     scope [callee] reads under [depth] binders, as an entry's loop: its
     body, under the fixpoint's name and its parameters, continuing itself
     and every loop the scope does. *)
  and entered callee depth occurrence fix =
    let parameters, inner = Mlutil.collect_lams fix in
    let arity = List.length parameters in
    let target = Loop.Member (occurrence, 0) in
    let callee ~depth:d f =
      match strip f with
      | MLrel (db, _) when db = arity + 1 + d -> Some (target, arity)
      | _ -> callee ~depth:(depth + 1 + arity + d) f
    in
    {loop = target; parameters = List.rev parameters; body = lower callee 0 inner}
  and recognise callee depth e =
    let continue_ f target arguments =
      match occurrence f with
      | Some occurrence -> Continue {target; occurrence; arguments}
      | None -> Return e
    in
    match e with
    | MLapp (MLfix (0, [|_|], [|fix|], _, o), args) when adopts o ->
      let entered = entered callee depth o fix in
      if List.compare_lengths args entered.parameters <> 0 then Return e
      else Entry {entered; name = None; scope = Continue {target = entered.loop; occurrence = o; arguments = args}}
    | MLletin (x, ty, MLfix (0, [|_|], [|fix|], _, o), b, _) when adopts o ->
      let entered = entered callee depth o fix in
      let arity = List.length entered.parameters in
      (* The let's binder, under [d] binders, names the entry. *)
      let callee ~depth:d f =
        match strip f with
        | MLrel (db, _) when db = d - depth -> Some (entered.loop, arity)
        | _ -> callee ~depth:d f
      in
      Entry {entered; name = Some (x, ty); scope = lower callee (depth + 1) b}
    | f when Option.has_some (named callee ~depth f 0) -> continue_ f (Option.get (named callee ~depth f 0)) []
    | MLapp (f, args) when Option.has_some (named callee ~depth f (List.length args)) ->
      continue_ f (Option.get (named callee ~depth f (List.length args))) args
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
        | [], [] -> lower callee depth partner
        | _ -> Return e
      in
      match bind depth 0 (List.rev params) args with
      | Return _ -> Return e
      | t -> t )
    | MLcons (_, c, [a]) when Recursion_plan.identity c -> lower callee depth a
    | MLapp (MLglob use, [a]) when Recursion_plan.identity use.callee && Table.to_inline use.callee ->
      lower callee depth a
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match List.rev args with
      | MLlam (x, ty, k) :: action :: _ when frames && calls callee ~depth action > 0 ->
        Resume {binder = x; binder_type = ty; value = lower callee depth action; body = lower callee (depth + 1) k}
      | MLlam (x, ty, k) :: action :: _ ->
        Let {binder = x; binder_type = ty; value = action; body = lower callee (depth + 1) k}
      | _ -> Return e )
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Return -> (
      match List.rev args with value :: _ -> lower callee depth value | [] -> Return e )
    | MLapp ((MLlam _ as f), args) ->
      let rec enter depth f args =
        match (f, args) with
        | MLlam (x, ty, b), a :: rest ->
          Let {binder = x; binder_type = ty; value = a; body = enter (depth + 1) b rest}
        | MLlam _, [] -> Return e
        | b, [] -> lower callee depth b
        | _, _ :: _ -> Return e
      in
      enter depth f args
    | MLletin (x, ty, a, b, _) when frames && calls callee ~depth a > 0 ->
      Resume {binder = x; binder_type = ty; value = lower callee depth a; body = lower callee (depth + 1) b}
    | MLletin (x, ty, a, b, _) -> Let {binder = x; binder_type = ty; value = a; body = lower callee (depth + 1) b}
    | MLcase (ty, s, branches) ->
      Match
        { scrutinee_type = ty;
          scrutinee = s;
          branches =
            Array.to_list
              (Array.map
                 (fun (ids, result_type, pattern, b) ->
                   {binders = ids; result_type; pattern; body = lower callee (depth + List.length ids) b} )
                 branches ) }
    | MLmagic (m, a) -> map_returns (fun v -> MLmagic (m, v)) (lower callee depth a)
    | MLcons _ when modulo_cons -> (
      match chain callee depth e with Some c -> Continue_into c | None -> Return e )
    | e -> Return e
  in
  match adopted with
  | Some (Partner p) ->
    (* The partner's calls run in place enter its body, which names nothing
       of the function's scope; and a call of the function's there
       re-enters the function's loop. *)
    let arity = List.length p.parameters in
    let invoking ~depth f =
      match (own ~depth f, strip f) with
      | (Some _ as c), _ -> c
      | None, MLglob use
        when Names.GlobRef.UserOrd.equal use.callee p.partner
             && List.exists (Occurrence.equal (Global_use.occurrence use)) p.invoked ->
        Some (Loop.Function p.partner, arity)
      | None, _ -> None
    in
    let scope = lower invoking 0 body in
    if not (List.exists (fun o -> List.exists (Occurrence.equal o) p.invoked) (continues scope)) then lower own 0 body
    else
      Entry
        { entered = {loop = Loop.Function p.partner; parameters = List.rev p.parameters; body = lower own 0 p.body};
          name = None;
          scope }
  | Some (Fixpoint _) | None -> lower own 0 body

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

let lower ~methods plan program =
  let struc = Core.structure program in
  let effects = Core_effects.analyze struc in
  let functions, locals = Recursion_plan.tail_loops plan in
  let modulo_cons, local_modulo_cons = Recursion_plan.modulo_cons_loops plan in
  let frame_functions, frame_locals = Recursion_plan.frame_loops plan in
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
  (* What the machine of the function [r], whose body is [inner], adopts:
     the first fixpoint of one member the plan has it adopt, and failing
     that the partner run in place of the calls the plan has it adopt,
     read as generated ({!Loopify_frame.find_adopted}), where it returns
     what [r] does: a machine has one result. *)
  let returns fd = Ml_type_util.ml_return_type (Mlutil.type_simpl fd.fd_type) in
  let adoption r inner =
    let single (_, funs) = Array.length funs = 1 in
    match List.find_opt (fun o -> List.exists single (fixpoints [o] [] inner)) (Recursion_plan.adoptable_in plan r) with
    | Some o -> Some (Fixpoint o)
    | None ->
      Option.bind (Recursion_plan.adopted_partner_in plan r) (fun (i : Recursion_plan.inlining) ->
          match (Names.GlobRef.Map_env.find_opt r !defs, Names.GlobRef.Map_env.find_opt i.partner !defs) with
          | Some own, Some fd when Mlutil.eq_ml_type (returns own) (returns fd) ->
            let parameters, body = read ~builds:false fd in
            Some (Partner {partner = i.partner; invoked = i.invoked; parameters; body})
          | _ -> None )
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
          let frames = List.exists (Names.GlobRef.UserOrd.equal fd.fd_ref) frame_functions in
          if builds || frames || List.exists (Names.GlobRef.UserOrd.equal fd.fd_ref) functions then begin
            let parameters, inner = read ~builds fd in
            let arity = List.length parameters in
            let callee ~depth:_ = function
              | MLglob use when Names.GlobRef.UserOrd.equal use.callee fd.fd_ref -> Some arity
              | _ -> None
            in
            let target = Loop.Function fd.fd_ref in
            let adopted = if frames && not (methods fd.fd_ref) then adoption fd.fd_ref inner else None in
            add target parameters
              (tail_loop ~inlined:(inlined ~builds fd.fd_ref) ~modulo_cons:builds ~frames ?adopted ~effects ~target
                 ~callee inner )
          end;
          List.iter
            (fun (occ, funs) ->
              let builds = List.exists (Occurrence.equal occ) local_modulo_cons in
              let frames = List.exists (Occurrence.equal occ) frame_locals in
              let parameters, inner = Mlutil.collect_lams funs.(0) in
              let inner = if builds then Recursion_plan.restore_temporaries inner else inner in
              let arity = List.length parameters in
              let callee ~depth f =
                match strip f with
                | MLrel (db, _) when db = arity + 1 + depth -> Some arity
                | _ -> None
              in
              let target = Loop.Member (occ, 0) in
              add target parameters (tail_loop ~modulo_cons:builds ~frames ~effects ~target ~callee inner) )
            (List.rev (fixpoints (locals @ local_modulo_cons @ frame_locals) [] body)) )
        (Mlutil.term_defs d) )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  List.rev !loops

let installed : t ref = State.cell State.Extraction empty

let install t = installed := t

let loop l = List.find_map (fun (l', t) -> if Loop.equal l l' then Some t else None) !installed

(* The occurrences of the global uses and variable reads in the Core terms
   [t] holds -- what it returns, binds, matches on, and passes a turn or a
   cell -- each once per copy: what stays a call in the code made of [t]
   where it is one. *)
let held_occurrences t =
  let found = ref [] in
  let rec ast = function
    | Miniml.MLrel (_, o) -> found := o :: !found
    | Miniml.MLglob {occurrence; _} -> found := occurrence :: !found
    | e -> Mlutil.ast_iter ast e
  in
  let continue_ (c : Control_ir.Term.continue_) = List.iter ast c.arguments in
  let rec go : Control_ir.Term.t -> unit = function
    | Loop l -> go l.body
    | Let l ->
      ast l.value;
      go l.body
    | Match m ->
      ast m.scrutinee;
      List.iter (fun (b : Control_ir.Term.branch) -> go b.body) m.branches
    | Return v -> ast v
    | Continue c -> continue_ c
    | Continue_into c ->
      List.iter (fun (cell : Control_ir.Term.cell) -> List.iter ast cell.arguments) c.cells;
      continue_ c.next
    | Resume r ->
      go r.value;
      go r.body
    | Entry e ->
      go e.entered.body;
      go e.scope
  in
  go t;
  !found

(* The Continues of [t] no code made of [t] keeps a call of: each made of an
   occurrence no other Continue and no term [t] holds shares
   (held_occurrences).  A copied call shares its occurrence with its
   copies, and only these are told apart from them. *)
let taken_continues t =
  let continues = Control_ir.continues t and held = held_occurrences t in
  let count o l = List.length (List.filter (Miniml.Occurrence.equal o) l) in
  List.filter (fun o -> count o continues = 1 && count o held = 0) continues
