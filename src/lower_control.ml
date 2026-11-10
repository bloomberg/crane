(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** LowerControl: the {!Control_ir} of a normalized program.  See
    [lower_control.mli]. *)

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
   where [f], under [depth] binders inside them, names it.  A machine
   adopting the local fixpoint at [adopted] has that entry too. *)
let tail_loop ?(modulo_cons = false) ?(frames = false) ?adopted ~effects ~target ~callee body =
  let effect_ = Recursion_plan.sequential effects in
  (* The loops a read names, by the binders it stands under: the loop it
     continues, and its number of parameters. *)
  let own ~depth f = Option.map (fun n -> (target, n)) (callee ~depth f) in
  let adopts o = Option.cata (Occurrence.equal o) false adopted in
  let rec lower ?(bound = false) callee depth e =
    match recognise ~bound callee depth e with
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
        | MLcase (_, s, branches, _) ->
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
  (* [bound] says [e] is a let's value, or a bind's action: a match there
     that translation does not generate as statements each assigning the
     binder ({!Recursion_plan.match_bound_in_place}) runs in a lambda
     invoked in place, where no call is a turn. *)
  and recognise ~bound callee depth e =
    let lower ?(bound = bound) = lower ~bound in
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
    | MLletin (x, ty, (MLfix (0, [|_|], [|fix|], _, o) as a), b, _) when adopts o -> (
      let entered = entered callee depth o fix in
      let arity = List.length entered.parameters in
      (* The let's binder, under [d] binders, names the entry. *)
      let entering ~depth:d f =
        match strip f with
        | MLrel (db, _) when db = d - depth -> Some (entered.loop, arity)
        | _ -> callee ~depth:d f
      in
      (* A fixpoint the scope enters by no turn -- applied only in a
         closure, or named as a value -- is no way into the machine. *)
      match lower entering (depth + 1) b with
      | scope when Control_ir.Term.continues_of entered.loop scope <> [] -> Entry {entered; name = Some (x, ty); scope}
      | _ -> Let {binder = x; binder_type = ty; value = a; body = lower callee (depth + 1) b} )
    | f when Option.has_some (named callee ~depth f 0) -> continue_ f (Option.get (named callee ~depth f 0)) []
    | MLapp (f, args) when Option.has_some (named callee ~depth f (List.length args)) ->
      continue_ f (Option.get (named callee ~depth f (List.length args))) args
    | MLcons (_, c, [a]) when Recursion_plan.identity c -> lower callee depth a
    | MLapp (MLglob use, [a]) when Recursion_plan.identity use.callee && Table.to_inline use.callee ->
      lower callee depth a
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match List.rev args with
      | MLlam (x, ty, k) :: action :: _ when frames && calls callee ~depth action > 0 ->
        Resume {binder = x; binder_type = ty; value = lower ~bound:true callee depth action; body = lower callee (depth + 1) k}
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
      Resume {binder = x; binder_type = ty; value = lower ~bound:true callee depth a; body = lower callee (depth + 1) b}
    | MLletin (x, ty, a, b, _) -> Let {binder = x; binder_type = ty; value = a; body = lower callee (depth + 1) b}
    | MLcase (ty, _, branches, _) when bound && not (Recursion_plan.match_bound_in_place ty branches) -> Return e
    | MLcase (ty, s, branches, _) ->
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
  lower own 0 body

(* The fixpoints in [e] whose occurrence [wanted] holds, with the types of
   their functions. *)
let rec fixpoints wanted acc e =
  let acc =
    match e with
    | MLfix (_, ids, funs, _, occ) when List.exists (Occurrence.equal occ) wanted -> (occ, Array.map snd ids, funs) :: acc
    | _ -> acc
  in
  let acc = ref acc in
  Mlutil.ast_iter (fun e -> acc := fixpoints wanted !acc e) e;
  !acc

let lower ~methods plan program =
  let struc = Core_phase.structure program in
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
  (* The body of a function lowered tail modulo cons is read with
     Normalize's temporaries put back, as the plan reads its chains. *)
  let read ~builds fd =
    let parameters, inner = generated fd in
    (parameters, if builds then Recursion_plan.restore_temporaries inner else inner)
  in
  (* What the machine of the function [r], whose body is [inner], adopts:
     the first fixpoint of one member the plan has it adopt
     ({!Loopify_frame.find_adopted}), where it returns what [r] does: a
     machine has one result. *)
  let adoption r inner =
    let single (_, _, funs) = Array.length funs = 1 in
    let first o = List.find_opt single (fixpoints [o] [] inner) in
    let yields_own ty =
      match Names.GlobRef.Map_env.find_opt r !defs with
      | Some own -> Recursion_plan.yields_alike own.fd_type ty
      | None -> false
    in
    match List.find_map first (Recursion_plan.adoptable_in plan r) with
    | Some (o, types, _) when yields_own types.(0) -> Some o
    | Some _ | None -> None
  in
  (* A partner's copy spliced into the body of [r] is entered by the
     machine [lowered] lowers it as ({!Splices.entered_copy}). *)
  let check_entered r lowered =
    match Splices.entered_copy (Core_phase.splices program) r with
    | Some o when Probe.checking () ->
      let enters t = List.exists (fun (e : loop) -> Loop.equal e.loop (Loop.Member (o, 0))) (Control_ir.Term.entries t) in
      if not (Option.cata enters false lowered) then
        Probe.violation "entered partner"
          Pp.(str "the machine of " ++ str (Table.kername_of_global r) ++ str " does not enter the partner spliced into its body")
    | Some _ | None -> ()
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
            let lowered = tail_loop ~modulo_cons:builds ~frames ?adopted ~effects ~target ~callee inner in
            add target parameters lowered;
            check_entered fd.fd_ref (Some lowered)
          end
          else check_entered fd.fd_ref None;
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
            (List.rev_map
               (fun (occ, _, funs) -> (occ, funs))
               (fixpoints (locals @ local_modulo_cons @ frame_locals) [] body) ) )
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
  let continues = Control_ir.Term.continues t and held = held_occurrences t in
  let count o l = List.length (List.filter (Miniml.Occurrence.equal o) l) in
  List.filter (fun o -> count o continues = 1 && count o held = 0) continues
