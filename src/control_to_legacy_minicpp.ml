(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Minicpp

(* How a loop is lowered: a tail loop, one built tail modulo cons, or a
   machine with a stack of frames. *)
type lowering =
  | Tail
  | Modulo_cons
  | Frames

(* How the recursion plan's [strategy] lowers a loop. *)
let lowering_of (strategy : Recursion_plan.strategy option) =
  match strategy with
  | Some Tail_loop -> Some Tail
  | Some (Modulo_cons _) -> Some Modulo_cons
  | Some Frame_stack -> Some Frames
  | Some (No_loop | Suspended _) | None -> None

(* The loop [target] of the definition [r], lowered as [planned], where
   that is one of the ways [lowerings]: a tail loop's turns build nothing
   and one tail modulo cons builds in some turn; a machine's ControlIR may
   be either, for a function whose chains its constructors' fields do not
   allow is a machine too, and a machine alone has entries. *)
let shaped_loop ~lowerings r planned target =
  match planned with
  | Some lowering when List.mem lowering lowerings -> (
    match Lower_control.loop target with
    | Some (Loop l) when Control_ir.continues l.body <> [] && (Control_ir.entries l.body = [] || lowering = Frames) ->
      let builds = Control_ir.continues_into l.body <> [] in
      let shaped = match lowering with Tail -> not builds | Modulo_cons -> builds | Frames -> true in
      if shaped then Some (l, lowering)
      else begin
        Probe.violation "control IR"
          Pp.(
            str "the ControlIR of " ++ str (Table.kername_of_global r)
            ++ str (if builds then " builds what a tail loop does not" else " builds no constructor the plan's chains do") );
        None
      end
    | Some _ | None -> None )
  | Some _ | None -> None

(* The loop the recursion plan lowers the function [r] to, and how, where
   it lowers it in one of the ways [lowerings]. *)
let loop_of ~lowerings r =
  if Option.has_some (Lifted.of_ref r) then None
  else
    shaped_loop ~lowerings r
      (lowering_of (Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r))
      (Control_ir.Loop.Function r)

(* The loop of the function [r], and how it is lowered, where it is one
   this module lowers. *)
let planned_loop r = if Table.should_loopify r then loop_of ~lowerings:[Tail; Modulo_cons; Frames] r else None

(* Whether each of the C++ parameters [params] of the function [r] is one
   its loop [l] varies: one standing for a parameter of [l] some Continue
   changes.  [None] where a parameter stands for none of [l]'s. *)
let varying r (l : Control_ir.Term.loop) binders params =
  let invariant = Control_ir.invariant_parameters l in
  let of_param (id, _) =
    match List.find_map (fun (x, b) -> if Id.equal x id then Some b else None) binders with
    | Some (b : Core_binder.t) when GlobRef.UserOrd.equal b.origin r ->
      Option.map not (List.nth_opt invariant b.level)
    | Some _ | None -> None
  in
  List.fold_right
    (fun p acc -> match (of_param p, acc) with Some v, Some vs -> Some (v :: vs) | _ -> None)
    params (Some [])

(* The loop the function [f] is lowered to, and the parameters it varies,
   where it is one this module lowers. *)
let planned (f : dfun) =
  match (f.df_shape, f.df_path.dp_inner) with
  | Ddef (params, _), [] ->
    let r = fst f.df_path.dp_outer in
    Option.bind (planned_loop r) (fun (l, lowering) ->
        Option.map (fun v -> (l, lowering, v)) (varying r l f.df_binders params) )
  | (Ddef _ | Ddecl _), _ -> None

(* The jump a C++ call is, where it is made of one of the Continues
   [continues]: the arguments it passes the loop's parameters. *)
let jump continues : Loopify_analysis.call_checker = function
  | CPPfun_call ({cs_occurrence = Some o; _}, _, args) when List.exists (Miniml.Occurrence.equal o) continues ->
    Some (Loopify_analysis.mk_call_site (to_reversed args))
  | _ -> None

(* Under [CRANE_CHECK_IR]: the loop [loop] of the function [f], whose
   generated body is [body], lowered from [exposed], its partners inlined
   and its tail calls exposed, jumping at the calls [jumped]; against the
   loop's Continues [continues] and the loop Loopify's own transform makes. *)
let check ~partner ~tparams (f : dfun) params body exposed ~varying ~continues ~jumped loop =
  let what = Pp.str (Table.kername_of_global (fst f.df_path.dp_outer)) in
  if not (Loopify_analysis.made_as_planned continues jumped) then
    Probe.violation "control IR"
      Pp.(str "the calls the tail loop of " ++ what ++ str " jumps at are not its Continues");
  if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
    Probe.violation "control lowering"
      Pp.(str "the calls of " ++ what ++ str " change other parameters than its ControlIR's Continues");
  if compare (Loopify.checker_tail_loop ~partner ~tparams f params body) loop <> 0 then
    Probe.violation "control lowering"
      Pp.(str "the tail loop of " ++ what ++ str " lowered from its ControlIR is not the loop Loopify makes")

(* The function [f], generated under the template parameters [tparams],
   lowered to the loop [l] varying the parameters [varying], each partner it
   inlines read as [partner] has it; [Error why] where Loopify makes no
   loop of it -- a call passing the loop other arguments than it has
   parameters, say -- for the reason [why] ({!Loopify.unlowered}). *)
let rec lower_function ~partner ~tparams (f : dfun) ((l : Control_ir.Term.loop), lowering, varying) =
  match (f.df_shape, lowering) with
  | Ddecl _, _ -> Error (Loopify.Left None)
  | Ddef (params, body), Modulo_cons ->
    lower_modulo_cons ~partner ~tparams f params body l varying (Control_ir.continues_into l.body)
  | Ddef (params, body), Frames -> lower_frames ~partner ~tparams f params body l
  | Ddef (params, body), Tail -> (
    let continues = Control_ir.continues l.body in
    let jumps = ref [] in
    let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
    let r = fst f.df_path.dp_outer in
    let exposed =
      Loopify_analysis.expose_tail_calls (jump continues) (Loopify.try_inline_mutual_into ~partner r body)
    in
    match Loopify_tail.transform_tail ~jumped ~varying tparams (jump continues) params f.df_ret exposed with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | loop -> (
      if Probe.checking () then
        check ~partner ~tparams f params body exposed ~varying ~continues ~jumped:(List.rev !jumps) loop;
      match Loopify.after_tail_loop ~tparams f params loop with
      | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
      | body -> Ok {f with df_shape = Ddef (params, body); df_loop = Some l.loop} ) )

(* Under [CRANE_CHECK_IR]: as {!check}, for a loop built tail modulo cons. *)
and check_modulo_cons ~partner ~tparams (f : dfun) params body exposed ~varying ~continues ~jumped loop =
  let what = Pp.str (Table.kername_of_global (fst f.df_path.dp_outer)) in
  if not (Loopify_analysis.made_as_planned continues jumped) then
    Probe.violation "control IR"
      Pp.(str "the calls the loop of " ++ what ++ str " takes are not its Continues and Continue_intos");
  if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
    Probe.violation "control lowering"
      Pp.(str "the calls of " ++ what ++ str " change other parameters than its ControlIR's Continues");
  if compare (Loopify.checker_modulo_cons ~partner ~tparams f params body) loop <> 0 then
    Probe.violation "control lowering"
      Pp.(str "the tail-modulo-cons loop of " ++ what ++ str " lowered from its ControlIR is not the loop Loopify makes")

(* The function [f] lowered to the loop [l] tail modulo cons, building the
   cells of its turns [into] around the calls they continue by. *)
and lower_modulo_cons ~partner ~tparams (f : dfun) params body l varying into =
  let continues = Control_ir.continues l.body in
  let shapes = Loopify_tmc.control_shapes into in
  let jumps = ref [] in
  let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
  let r = fst f.df_path.dp_outer in
  let exposed =
    Loopify_analysis.expose_tail_calls (jump continues) (Loopify.try_inline_mutual_into ~partner r body)
  in
  match Loopify.modulo_cons_loop ~jumped ~varying ~shapes ~tparams (jump continues) f params exposed with
  | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
  | None -> Error (Loopify.Left None)
  | Some loop -> (
    if Probe.checking () then
      check_modulo_cons ~partner ~tparams f params body exposed ~varying ~continues ~jumped:(List.rev !jumps) loop;
    match Loopify.after_tail_loop ~strategy:Lp_tmc ~tparams f params loop with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | body -> Ok {f with df_shape = Ddef (params, body); df_loop = Some l.loop} )

(* The function [f] lowered to the machine with a stack of frames of its
   loop [l], entered by the calls made of [l]'s Continues of it, and by
   those of the entry it adopts, if it has one: the body Loopify finds of
   it ({!Loopify.frame_machine}). *)
and lower_frames ~partner ~tparams (f : dfun) params body (l : Control_ir.Term.loop) =
  let own = Control_ir.continues_of l.loop l.body in
  let r = fst f.df_path.dp_outer in
  let exposed = Loopify_analysis.expose_tail_calls (jump own) (Loopify.try_inline_mutual_into ~partner r body) in
  let machine () =
    match Control_ir.entries l.body with
    | [] -> Loopify.frame_machine ~loop:l.loop ~tparams (jump own) f params exposed
    | [entry] -> Loopify.frame_machine ~loop:l.loop ~entry:entry.loop ~tparams (jump own) f params exposed
    | _ :: _ :: _ -> Error (Loopify.Left None)
  in
  match machine () with
  | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
  | Error why -> Error why
  | Ok (machine, survived) -> (
    if Probe.checking () && compare (Loopify.checker_frame_machine ~partner ~tparams f params body) machine <> 0 then
      Probe.violation "control lowering"
        Pp.(
          str "the machine of " ++ str (Table.kername_of_global r)
          ++ str " lowered from its ControlIR is not the machine Loopify makes" );
    match Loopify.after_tail_loop ~strategy:Lp_frame ?survived ~tparams f params machine with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | body -> Ok {f with df_shape = Ddef (params, body); df_loop = Some l.loop} )

(* The function a generated declaration is, with the template parameters
   it is generated under. *)
let rec function_of ?(tparams = []) = function
  | Dtemplate (tparams, _, d) -> function_of ~tparams d
  | Dfun f -> Some (tparams, f)
  | _ -> None

let rec with_function f = function
  | Dtemplate (tparams, c, d) -> Dtemplate (tparams, c, with_function f d)
  | Dfun _ -> Dfun f
  | d -> d

(* A member inlined into another is read as Loopify reads one it registered
   ({!Loopify.register_decl}). *)
let registered (f : dfun) =
  match f.df_shape with
  | Ddef (params, body) -> Some {Loopify_analysis.rf_ret_ty = f.df_ret; rf_params = params; rf_body = body}
  | Ddecl _ -> None

(* The parameters of the loop [l] the C++ parameters of a local fixpoint's
   lambda stand for, by position, in the order a lambda stores its
   parameters, the last first ({!Minicpp.to_reversed}): those not void,
   which the lambda does not take ({!Ml_type_util.void_binder}). *)
let kept_positions (l : Control_ir.Term.loop) =
  List.filteri (fun _ (_, ty) -> not (Ml_type_util.void_binder ty)) (List.mapi (fun i (_, ty) -> (i, ty)) l.parameters)
  |> List.rev_map fst

(* Under [CRANE_CHECK_IR]: the statement [loop] a local fixpoint is generated
   as, against the one Loopify makes of the Y-combinator [self_passing] it
   was generated as before, [lower] lowering its local fixpoints. *)
let check_local ~lower ~name ~self_passing loop =
  if compare (lower (self_passing ())) [loop] <> 0 then
    Probe.violation "control lowering"
      Pp.(
        str "the local fixpoint " ++ Id.print name
        ++ str " lowered from its ControlIR is not the loop Loopify makes of its Y-combinator" )

(* Whether Loopify loopifies the definition [r]: a method as its struct's
   methods are loopified. *)
let loopified r =
  match Cpp_state.is_registered_method r with
  | Some (inductive, _) -> Table.loopifies_methods_of inductive && Table.loopifies_method r
  | None -> Table.should_loopify r

(* Whether Loopify makes a machine with a stack of its own of the definition
   [r] and lowers the local fixpoints in its body only around that
   machine. *)
let machine r =
  loopified r
  &&
  match Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r with
  | Some (Modulo_cons _ | Frame_stack) -> true
  | Some (No_loop | Tail_loop | Suspended _) | None -> false

(* Whether Loopify lowers every local fixpoint in the body of the
   definition [r], machines included, [function_] saying whether that body
   is a function's: a function it loopifies, as it finishes it or as the
   bridge lowers its loop ({!Loopify.after_tail_loop}), not a helper lifted
   out of another definition.  Of any other body it lowers the local tail
   loops alone. *)
let lowers_local_machines ~function_ r = function_ && Table.should_loopify r && not (Option.has_some (Lifted.of_ref r))

let local_loop ~owner ~function_ ~lifted ~member:((occurrence, _) as member) ~tparams ~name ~self_passing
    (lam : cpp_lambda) =
  (* The function a fixpoint is in the flow of adopts it only where it is
     a machine itself, which a local tail loop is never lowered inside. *)
  let lowering =
    match Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member with
    | Some Tail_loop ->
      if Recursion_plan.adoptable_by_fixpoint ~lifted occurrence || Option.cata machine false owner then None
      else Some Tail
    | Some (Modulo_cons _ | Frame_stack)
      when (not (Recursion_plan.adoptable_somewhere ~lifted occurrence))
           && Option.cata (lowers_local_machines ~function_) false owner ->
      Some Frames
    | Some (No_loop | Modulo_cons _ | Frame_stack | Suspended _) | None -> None
  in
  (* A loop or machine leaving a call behind is a decline, as Loopify
     records it of the Y-combinator then left. *)
  let declined () =
    Loopify_analysis.record_outcome (Id.to_string name) (Lp_declined Loopify_analysis.survived_generically);
    None
  in
  match (Lower_control.loop (Control_ir.Loop.Member (fst member, snd member)), lowering) with
  | Some (Loop l), Some lowering when Control_ir.continues l.body <> [] -> (
    let params = List.filter_map (fun (ty, x) -> Option.map (fun x -> (x, ty)) x) (to_reversed lam.cl_params) in
    let invariant = Control_ir.invariant_parameters l in
    let kept = kept_positions l in
    if List.compare_lengths kept params <> 0 then None
    else
      let varying = List.map (fun i -> not (List.nth invariant i)) kept in
      let continues = Control_ir.continues l.body in
      let jumps = ref [] in
      let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
      let exposed = Loopify_analysis.expose_tail_calls (jump continues) lam.cl_body in
      let ret_ty = Option.default Tvoid lam.cl_ret in
      let body () =
        match lowering with
        | Tail | Modulo_cons -> Some (Loopify_tail.transform_tail ~jumped ~varying tparams (jump continues) params ret_ty exposed)
        | Frames ->
          let binders = Option.cata (fun (f : local_fixpoint) -> f.lf_binders) [] lam.cl_fixpoint in
          Loopify.local_frame_machine ~member ~name ~binders ~tparams (jump continues) params ret_ty exposed
      in
      match body () with
      | exception Loopify_analysis.Not_linearisable _ -> None
      | None -> declined ()
      | Some body ->
        (* A call of the fixpoint the loop does not take -- one in a closure
           it builds -- or the fixpoint named as a value calls a lambda that
           is no longer there: it stays the Y-combinator Loopify declines. *)
        let calls = Recursion_plan.member_calls member in
        let left = function
          | CPPvar x -> Id.equal x name
          | e -> ( match Loopify_analysis.made_of e with Some o -> List.exists (Miniml.Occurrence.equal o) calls | None -> false )
        in
        if Loopify_analysis.body_exists left body then declined ()
        else begin
          if Probe.checking () && lowering = Tail then begin
            if not (Loopify_analysis.made_as_planned continues (List.rev !jumps)) then
              Probe.violation "control IR"
                Pp.(str "the calls the tail loop of the local fixpoint " ++ Id.print name ++ str " jumps at are not its Continues");
            if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
              Probe.violation "control lowering"
                Pp.(str "the calls of the local fixpoint " ++ Id.print name ++ str " change other parameters than its ControlIR's Continues")
          end;
          if lowering = Tail then Loopify_analysis.record_outcome (Id.to_string name) Lp_tail;
          let loop = {lam with cl_body = body; cl_moved = []} in
          let moved = List.filter (fun x -> List.mem x (free_vars_expr (CPPlambda loop))) lam.cl_moved in
          let stmt = Sasgn (name, Declare (Tauto, None), CPPlambda {loop with cl_moved = moved}) in
          if Probe.checking () then begin
            let lower = match lowering with Tail | Modulo_cons -> Loopify.lower_local_tail_loops | Frames -> Loopify.lower_local_loops in
            check_local ~lower:(lower ~tparams) ~name ~self_passing stmt
          end;
          Some stmt
        end )
  (* A loop no call continues is none: every call is where no loop takes
     it, and declines it, where Loopify reaches the fixpoint -- in a body it
     loopifies. *)
  | Some _, Some _ when Option.cata loopified false owner -> declined ()
  | (Some _ | None), _ -> None

(* Whether each of the receiver and the parameters of the method [m], made
   of the function [r], is one its loop [l] varies, as {!varying} reads a
   function's. *)
let method_varying r (l : Control_ir.Term.loop) (m : method_field) =
  let invariant = Control_ir.invariant_parameters l in
  let at (b : Core_binder.t) =
    if GlobRef.UserOrd.equal b.origin r then Option.map not (List.nth_opt invariant b.level) else None
  in
  let param (id, _) =
    Option.bind (List.find_map (fun (x, b) -> if Id.equal x id then Some b else None) m.mf_binders) at
  in
  List.fold_right
    (fun v acc -> match (v, acc) with Some v, Some vs -> Some (v :: vs) | _ -> None)
    (Option.bind m.mf_receiver_binder at :: List.map param m.mf_params)
    (Some [])

(* The method [m] lowered to its loop, where it is one: the struct it is a
   member of declared under [tparams], its receiver a [self_ty].  It is
   Loopify's method transform: a tail loop varying the receiver and the
   parameters its ControlIR varies, a loop tail modulo cons or a machine
   taking the calls its ControlIR continues by
   ({!Loopify.transform_method_own}).  A method the transform leaves as it
   was is declined -- a receiver a frame cannot point at -- and left to
   Loopify, which declines it. *)
let lower_method ~tparams ~self_ty (m : method_field) =
  match m.mf_globref with
  | Some r when Recursion_plan.inlinings r = [] && not (Recursion_plan.inlined r) -> (
    let lowering =
      match loop_of ~lowerings:[Tail; Modulo_cons; Frames] r with
      | Some (l, Tail) ->
        Option.map
          (fun varying -> (l, fun () -> Loopify.transform_method_own ~varying ~tparams ~self_ty m))
          (method_varying r l m)
      | Some (l, (Modulo_cons | Frames)) ->
        Some (l, fun () -> Loopify.transform_method_own ~controlled:true ~tparams ~self_ty m)
      | None -> None
    in
    match lowering with
    | None ->
      Loopify.record_unlowered_method m;
      None
    | Some (l, transform) -> (
      match transform () with
      | exception Loopify_analysis.Not_linearisable _ -> None
      | Fmethod m' when compare m' m <> 0 ->
        if Probe.checking () && compare (Loopify.transform_method_own ~tparams ~self_ty m) (Fmethod m') <> 0 then
          Probe.violation "control lowering"
            Pp.(
              str "the method " ++ str (Table.kername_of_global r)
              ++ str " lowered from its ControlIR is not the method Loopify makes" );
        Some
          { m' with
            mf_body = Loopify.lower_local_tail_loops ~tparams:(tparams @ m.mf_tparams) m'.mf_body;
            mf_loop = Some l.loop }
      | _ -> None ) )
  | Some _ | None ->
    Loopify.record_unlowered_method m;
    None

let lower_methods ~merged inductive vars fields =
  let tparams = List.map (fun v -> (TTtypename, v)) vars in
  let self_ty = Tconst (Tptr (Tglob (inductive, List.map named_tvar vars, []))) in
  let loopified r =
    (if merged then Table.loopify () else Table.loopifies_methods_of inductive) && Table.loopifies_method r
  in
  List.map
    (fun ((f, vis, tag) as field) ->
      match f with
      | Fmethod ({mf_globref = Some r; _} as m) when loopified r -> (
        match lower_method ~tparams ~self_ty m with Some m -> (Fmethod m, vis, tag) | None -> field )
      | _ -> field )
    fields

(* Whether each of the C++ parameters [params] of a helper lifted out for
   the function of a local fixpoint, whose loop is [l], is one [l] varies:
   the variables the helper captures, its first parameters, which every
   call passes on as they are, then the parameters of [l] that are not void
   ({!Ml_type_util.void_binder}), in order.  [None] where they are not so
   many. *)
let lifted_varying (l : Control_ir.Term.loop) params =
  let invariant = Control_ir.invariant_parameters l in
  let kept =
    List.filter_map
      (fun (i, (_, ty)) -> if Ml_type_util.void_binder ty then None else Some i)
      (List.mapi (fun i p -> (i, p)) l.parameters)
  in
  let captured = List.length params - List.length kept in
  if captured < 0 then None
  else Some (List.init captured (fun _ -> false) @ List.map (fun i -> not (List.nth invariant i)) kept)

(* The definition [d], a function Loopify loopifies of which no loop of
   its own is made here, for the reason [unlowered], with the local
   fixpoints in its body lowered as Loopify lowers those of such a function
   -- the ones translation left for the function's machine to adopt, which
   there is none of to adopt them -- and the outcome Loopify records of it
   recorded. *)
let lower_locals ?unlowered d =
  match function_of d with
  | Some (tparams, ({df_shape = Ddef (params, body); _} as f)) when Table.should_loopify (fst f.df_path.dp_outer) ->
    let body = Loopify.lower_function_locals ~tparams params body in
    Loopify.record_unlowered ?unlowered f body;
    with_function {f with df_shape = Ddef (params, body)} d
  | Some _ | None -> d

(* [lower] applied to the loop [planned] a function is lowered to, where
   it has one; a function with none is left, no loop made of it. *)
let lowered_or_left lower planned = Option.cata lower (Error (Loopify.Left None)) planned

let lower_lifted d =
  let lowered =
    match function_of d with
    | None -> Error (Loopify.Left None)
    | Some (tparams, f) -> (
      let r = fst f.df_path.dp_outer in
      match (f.df_shape, Option.bind (Lifted.of_ref r) Lifted.fixpoint) with
      | Ddef (params, _), Some member when Table.should_loopify r ->
        let planned =
          lowering_of (Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member)
        in
        lowered_or_left
          (fun (l, lowering, varying) -> lower_function ~partner:(fun _ -> None) ~tparams f (l, lowering, varying))
          (Option.bind
             (shaped_loop ~lowerings:[Tail; Modulo_cons; Frames] r planned
                (Control_ir.Loop.Member (fst member, snd member)) )
             (fun (l, lowering) -> Option.map (fun varying -> (l, lowering, varying)) (lifted_varying l params)) )
      | (Ddef _ | Ddecl _), _ -> Error (Loopify.Left None) )
  in
  match lowered with Ok f' -> with_function f' d | Error unlowered -> lower_locals ~unlowered d

let lower_group decls =
  let functions = List.filter_map function_of decls in
  let partner g =
    List.find_map
      (fun (_, (f : dfun)) ->
        if List.exists (fun (r, _) -> GlobRef.UserOrd.equal r g) (dfun_path_list f.df_path) then registered f
        else None )
      functions
  in
  let plans = List.map (fun d -> (d, Option.bind (function_of d) (fun (_, f) -> planned f))) decls in
  let involved d =
    match decl_globref d with
    | Some r -> Recursion_plan.inlinings r <> [] || Recursion_plan.inlined r
    | None -> false
  in
  (* Loopify inlines a member's partners when the unit is finished, as they
     were registered then: as generated, not lowered.  So the members that
     inline one another, those Loopify makes a loop of, are lowered here all
     of them or none.  A member it makes no loop of, its ControlIR's loop
     continued by no call, it inlines nothing into, and leaves as it was
     generated, as this does. *)
  let loopified d = match decl_globref d with Some r -> Option.has_some (planned_loop r) | None -> false in
  let all_planned = List.for_all (fun (d, p) -> Option.has_some p || not (involved d && loopified d)) plans in
  let lowered =
    List.map
      (fun (d, p) ->
        let lowered =
          match function_of d with
          | Some (tparams, f) when not (involved d && not all_planned) ->
            lowered_or_left (lower_function ~partner ~tparams f) p
          | Some _ | None -> Error (Loopify.Left None)
        in
        (d, lowered) )
      plans
  in
  let all_lowered = List.for_all (fun (d, l) -> Result.is_ok l || not (involved d && loopified d)) lowered in
  List.map
    (fun (d, l) ->
      match l with
      | Ok f when all_lowered || not (involved d) -> with_function f d
      | Ok _ -> lower_locals d
      | Error unlowered -> lower_locals ~unlowered d )
    lowered
