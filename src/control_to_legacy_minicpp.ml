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

(* The loop of the method made of [r], and how it is lowered, where it is
   one this module lowers: a method inlines no partner, nor is one
   inlined. *)
let method_loop r =
  if Recursion_plan.inlinings r = [] && not (Recursion_plan.inlined r) then
    loop_of ~lowerings:[Tail; Modulo_cons; Frames] r
  else None

(* Why a loop the plan commits to was left as it was generated. *)
let reason = function
  | Loopify.Declined why | Left (Some why) -> why
  | Left None -> "left as generated"

(* Whether a coercion from [from] into [into] keeps the value's
   representation: two instances of one inductive agreeing on the
   arguments its C++ type takes, those of its parameters
   ({!Table.get_ind_num_param_vars_opt}); its indices it does not take. *)
let in_place from into =
  match (Mlutil.type_simpl from, Mlutil.type_simpl into) with
  | Miniml.Tglob ((GlobRef.IndRef (kn, _) as r), args, _), Miniml.Tglob (r', args', _)
    when GlobRef.UserOrd.equal r r' -> (
    match Table.get_ind_num_param_vars_opt kn with
    | Some n when List.length args >= n && List.length args' >= n ->
      List.for_all2 Mlutil.eq_ml_type (CList.firstn n args) (CList.firstn n args')
    | Some _ | None -> false )
  | _ -> false

(* What each parameter of the loop [l] is passed by its Continues
   ({!Control_ir.parts_passed}), read with the planned representation. *)
let parts_passed l =
  Control_ir.parts_passed ~pointer_fields:Loopify_analysis.constructor_pointer_fields ~in_place l

(* A loop as it is lowered, and for each C++ parameter of what it is
   lowered from, whether the loop varies it -- some Continue changes the
   parameter of the loop it stands for -- and whether every Continue passes
   it a value stored in what the caller passed for it
   ({!Control_ir.parts_passed}).  A parameter standing for none of the
   loop's is neither. *)
type planned = {
  loop : Control_ir.Term.loop;
  lowering : lowering;
  varying : bool list;
  parts : bool list;
}

(* [l] lowered as [lowering] from what takes C++ parameters standing, in
   order, for the parameters of [l] at [positions], or for none of them. *)
let planned_at (l : Control_ir.Term.loop) lowering positions =
  let at flags = List.map (function Some i -> List.nth flags i | None -> false) positions in
  { loop = l;
    lowering;
    varying = at (List.map not (Control_ir.invariant_parameters l));
    parts = at (parts_passed l) }

(* The position among the parameters of the loop [l] of the parameter of
   the function [r] the Core binder [b] is, where it is one. *)
let position r (l : Control_ir.Term.loop) (b : Core_binder.t option) =
  match b with
  | Some b when GlobRef.UserOrd.equal b.origin r && b.level < List.length l.parameters -> Some b.level
  | Some _ | None -> None

let binder_of binders (id, _) = List.find_map (fun (x, b) -> if Id.equal x id then Some b else None) binders

(* The loop the function [f] is lowered to, where it is one this module
   lowers, each of its C++ parameters standing for one of the loop's. *)
let planned (f : dfun) =
  match (f.df_shape, f.df_path.dp_inner) with
  | Ddef (params, _), [] ->
    let r = fst f.df_path.dp_outer in
    Option.bind (planned_loop r) (fun (l, lowering) ->
        let positions = List.map (fun p -> position r l (binder_of f.df_binders p)) params in
        if List.for_all Option.has_some positions then Some (planned_at l lowering positions) else None )
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
let check ~partner ~parts ~tparams (f : dfun) params body exposed ~varying ~continues ~jumped loop =
  let what = Pp.str (Table.kername_of_global (fst f.df_path.dp_outer)) in
  if not (Loopify_analysis.made_as_planned continues jumped) then
    Probe.violation "control IR"
      Pp.(str "the calls the tail loop of " ++ what ++ str " jumps at are not its Continues");
  if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
    Probe.violation "control lowering"
      Pp.(str "the calls of " ++ what ++ str " change other parameters than its ControlIR's Continues");
  if compare (Loopify.checker_tail_loop ~partner ~parts ~tparams f params body) loop <> 0 then
    Probe.violation "control lowering"
      Pp.(str "the tail loop of " ++ what ++ str " lowered from its ControlIR is not the loop Loopify makes")

(* The function [f], generated under the template parameters [tparams],
   lowered to the loop [l] varying the parameters [varying], each partner it
   inlines read as [partner] has it; [Error why] where Loopify makes no
   loop of it -- a call passing the loop other arguments than it has
   parameters, say -- for the reason [why] ({!Loopify.unlowered}). *)
let rec lower_function ~partner ~tparams (f : dfun) {loop = l; lowering; varying; parts} =
  match (f.df_shape, lowering) with
  | Ddecl _, _ -> Error (Loopify.Left None)
  | Ddef (params, body), Modulo_cons ->
    lower_modulo_cons ~partner ~tparams f params body l ~varying ~parts (Control_ir.continues_into l.body)
  | Ddef (params, body), Frames -> lower_frames ~partner ~tparams f params body l ~parts
  | Ddef (params, body), Tail -> (
    let continues = Control_ir.continues l.body in
    let jumps = ref [] in
    let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
    let r = fst f.df_path.dp_outer in
    let exposed =
      Loopify_analysis.expose_tail_calls (jump continues) (Loopify.try_inline_mutual_into ~partner r body)
    in
    match Loopify_tail.transform_tail ~jumped ~varying ~parts tparams (jump continues) params f.df_ret exposed with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | loop -> (
      if Probe.checking () then
        check ~partner ~parts ~tparams f params body exposed ~varying ~continues ~jumped:(List.rev !jumps) loop;
      match Loopify.after_tail_loop ~tparams f params loop with
      | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
      | body -> Ok {f with df_shape = Ddef (params, body); df_loop = Some l.loop} ) )

(* Under [CRANE_CHECK_IR]: as {!check}, for a loop built tail modulo cons. *)
and check_modulo_cons ~partner ~parts ~tparams (f : dfun) params body exposed ~varying ~continues ~jumped loop =
  let what = Pp.str (Table.kername_of_global (fst f.df_path.dp_outer)) in
  if not (Loopify_analysis.made_as_planned continues jumped) then
    Probe.violation "control IR"
      Pp.(str "the calls the loop of " ++ what ++ str " takes are not its Continues and Continue_intos");
  if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
    Probe.violation "control lowering"
      Pp.(str "the calls of " ++ what ++ str " change other parameters than its ControlIR's Continues");
  if compare (Loopify.checker_modulo_cons ~partner ~parts ~tparams f params body) loop <> 0 then
    Probe.violation "control lowering"
      Pp.(str "the tail-modulo-cons loop of " ++ what ++ str " lowered from its ControlIR is not the loop Loopify makes")

(* The function [f] lowered to the loop [l] tail modulo cons, building the
   cells of its turns [into] around the calls they continue by. *)
and lower_modulo_cons ~partner ~tparams (f : dfun) params body l ~varying ~parts into =
  let continues = Control_ir.continues l.body in
  let shapes = Loopify_tmc.control_shapes into in
  let jumps = ref [] in
  let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
  let r = fst f.df_path.dp_outer in
  let exposed =
    Loopify_analysis.expose_tail_calls (jump continues) (Loopify.try_inline_mutual_into ~partner r body)
  in
  match Loopify.modulo_cons_loop ~jumped ~varying ~parts ~shapes ~tparams (jump continues) f params exposed with
  | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
  | None -> Error (Loopify.Left None)
  | Some loop -> (
    if Probe.checking () then
      check_modulo_cons ~partner ~parts ~tparams f params body exposed ~varying ~continues ~jumped:(List.rev !jumps) loop;
    match Loopify.after_tail_loop ~strategy:Lp_tmc ~tparams f params loop with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | body -> Ok {f with df_shape = Ddef (params, body); df_loop = Some l.loop} )

(* The function [f] lowered to the machine with a stack of frames of its
   loop [l], entered by the calls made of [l]'s Continues of it, and by
   those of the entry it adopts, if it has one: the body Loopify finds of
   it ({!Loopify.frame_machine}). *)
and lower_frames ~partner ~tparams (f : dfun) params body (l : Control_ir.Term.loop) ~parts =
  let own = Control_ir.continues_of l.loop l.body in
  let r = fst f.df_path.dp_outer in
  let exposed = Loopify_analysis.expose_tail_calls (jump own) (Loopify.try_inline_mutual_into ~partner r body) in
  let machine () =
    match Control_ir.entries l.body with
    | [] -> Loopify.frame_machine ~loop:l.loop ~parts ~tparams (jump own) f params exposed
    | [entry] -> Loopify.frame_machine ~loop:l.loop ~entry:entry.loop ~parts ~tparams (jump own) f params exposed
    | _ :: _ :: _ -> Error (Loopify.Left None)
  in
  match machine () with
  | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
  | Error why -> Error why
  | Ok (machine, survived) -> (
    (* A machine leaving a call behind lays its frames out for the calls it
       takes, where Loopify's lays them out for every call. *)
    if Probe.checking () && (not (Loopify.leaves_calls f machine))
       && compare (Loopify.checker_frame_machine ~partner ~parts ~tparams f params body) machine <> 0
    then
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
  let member_loop = Control_ir.Loop.Member (fst member, snd member) in
  let unlowered why =
    Loop_verdicts.record member_loop (Unlowered why);
    None
  in
  (* A loop or machine leaving a call behind is a decline, as Loopify
     records it of the Y-combinator then left. *)
  let declined () =
    Loopify_analysis.record_outcome (Id.to_string name) (Lp_declined Loopify_analysis.survived_generically);
    unlowered Loopify_analysis.survived_generically
  in
  match (Lower_control.loop member_loop, lowering) with
  | Some (Loop l), Some lowering when Control_ir.continues l.body <> [] -> (
    let params = List.filter_map (fun (ty, x) -> Option.map (fun x -> (x, ty)) x) (to_reversed lam.cl_params) in
    let invariant = Control_ir.invariant_parameters l in
    let kept = kept_positions l in
    if List.compare_lengths kept params <> 0 then unlowered "its lambda takes other parameters than its loop"
    else
      let varying = List.map (fun i -> not (List.nth invariant i)) kept in
      let parts = List.map (List.nth (parts_passed l)) kept in
      let continues = Control_ir.continues l.body in
      let jumps = ref [] in
      let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
      let exposed = Loopify_analysis.expose_tail_calls (jump continues) lam.cl_body in
      let ret_ty = Option.default Tvoid lam.cl_ret in
      let body () =
        match lowering with
        | Tail | Modulo_cons ->
          Some (Loopify_tail.transform_tail ~jumped ~varying ~parts tparams (jump continues) params ret_ty exposed)
        | Frames ->
          Loopify.local_frame_machine ~member ~name ~binders:(lambda_binders lam) ~parts ~tparams (jump continues) params ret_ty exposed
      in
      match body () with
      | exception Loopify_analysis.Not_linearisable why -> unlowered why
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
            check_local ~lower:(lower ~parts:(member, parts) ~tparams) ~name ~self_passing stmt
          end;
          Loop_verdicts.record member_loop Lowered;
          Some stmt
        end )
  (* A loop no call continues is none: every call is where no loop takes
     it, and declines it, where Loopify reaches the fixpoint -- in a body it
     loopifies. *)
  | Some _, Some _ when Option.cata loopified false owner ->
    Loopify_analysis.record_outcome (Id.to_string name) (Lp_declined Loopify_analysis.survived_generically);
    Loop_verdicts.record member_loop Kept;
    None
  | (Some _ | None), _ ->
    Loop_verdicts.record member_loop Kept;
    None

(* The positions among the parameters of the loop [l] of those the
   receiver and the parameters of the method [m], made of the function
   [r], stand for, as {!planned} reads a function's: [None] where one
   stands for none of [l]'s. *)
let method_positions r (l : Control_ir.Term.loop) (m : method_field) =
  let positions =
    position r l m.mf_receiver_binder :: List.map (fun p -> position r l (binder_of m.mf_binders p)) m.mf_params
  in
  if List.for_all Option.has_some positions then Some positions else None

(* The method [m] lowered to its loop, where it is one: the struct it is a
   member of declared under [tparams], its receiver a [self_ty].  It is
   Loopify's method transform: a tail loop varying the receiver and the
   parameters its ControlIR varies, a loop tail modulo cons or a machine
   taking the calls its ControlIR continues by
   ({!Loopify.transform_method_own}), pointing where every call passes a
   value stored in what the caller passed ({!parts_passed}) wherever its
   receiver and parameters each stand for a parameter of the loop.  A
   method the transform leaves as it was is declined -- a receiver a frame
   cannot point at -- and left to Loopify, which declines it. *)
let lower_method ~tparams ~self_ty (m : method_field) =
  match Option.bind m.mf_globref (fun r -> Option.map (fun planned -> (r, planned)) (method_loop r)) with
  | None ->
    Loopify.record_unlowered_method m;
    None
  | Some (r, (l, lowering)) -> (
    let unlowered why =
      Loop_verdicts.record l.loop (Unlowered why);
      None
    in
    let planned = Option.map (planned_at l lowering) (method_positions r l m) in
    let parts = Option.map (fun p -> p.parts) planned in
    let transform =
      match (lowering, planned) with
      | Tail, Some {varying; _} -> Some (fun () -> Loopify.transform_method_own ~varying ?parts ~tparams ~self_ty m)
      | Tail, None -> None
      | (Modulo_cons | Frames), _ ->
        Some (fun () -> Loopify.transform_method_own ~controlled:true ?parts ~tparams ~self_ty m)
    in
    match transform with
    | None ->
      Loopify.record_unlowered_method m;
      unlowered "its receiver and parameters stand for none of its loop's"
    | Some transform -> (
      match transform () with
      | exception Loopify_analysis.Not_linearisable why -> unlowered why
      | Fmethod m' when compare m' m <> 0 ->
        if Probe.checking () && compare (Loopify.transform_method_own ?parts ~tparams ~self_ty m) (Fmethod m') <> 0
        then
          Probe.violation "control lowering"
            Pp.(
              str "the method " ++ str (Table.kername_of_global r)
              ++ str " lowered from its ControlIR is not the method Loopify makes" );
        Loop_verdicts.record l.loop Lowered;
        Some
          { m' with
            mf_body = Loopify.lower_local_tail_loops ~tparams:(tparams @ m.mf_tparams) m'.mf_body;
            mf_loop = Some l.loop }
      | _ -> unlowered "Loopify's method transform left it" ) )

let lower_methods ~merged inductive vars fields =
  let tparams = List.map (fun v -> (TTtypename, v)) vars in
  let self_ty = Tconst (Tptr (Tglob (inductive, List.map named_tvar vars, []))) in
  let loopified r =
    (if merged then Table.loopify () else Table.loopifies_methods_of inductive) && Table.loopifies_method r
  in
  List.map
    (fun ((f, vis, tag) as field) ->
      match f with
      | Fmethod ({mf_globref = Some r; _} as m) ->
        if loopified r then
          match lower_method ~tparams ~self_ty m with Some m -> (Fmethod m, vis, tag) | None -> field
        else begin
          Loop_verdicts.record (Control_ir.Loop.Function r) Kept;
          field
        end
      | _ -> field )
    fields

(* The positions among the parameters of the loop [l] of those the C++
   parameters [params] of a helper lifted out for the function of a local
   fixpoint stand for: the variables the helper captures, its first
   parameters, stand for none, every call passing them on as they are; the
   rest for the parameters of [l] that are not void
   ({!Ml_type_util.void_binder}), in order.  [None] where they are not so
   many. *)
let lifted_positions (l : Control_ir.Term.loop) params =
  let kept =
    List.filter_map
      (fun (i, (_, ty)) -> if Ml_type_util.void_binder ty then None else Some i)
      (List.mapi (fun i p -> (i, p)) l.parameters)
  in
  let captured = List.length params - List.length kept in
  if captured < 0 then None else Some (List.init captured (fun _ -> None) @ List.map (fun i -> Some i) kept)

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

(* The loop of the helper [r] lifted for the function of a local fixpoint,
   and how it is lowered, where it is one this module lowers: that
   member's. *)
let lifted_loop r =
  match Option.bind (Lifted.of_ref r) Lifted.fixpoint with
  | Some member when Table.should_loopify r ->
    shaped_loop ~lowerings:[Tail; Modulo_cons; Frames] r
      (lowering_of (Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member))
      (Control_ir.Loop.Member (fst member, snd member))
  | Some _ | None -> None

let lower_lifted d =
  (* The loop the plan commits the helper to, and what came of it. *)
  let decided =
    match function_of d with
    | None -> None
    | Some (tparams, f) -> (
      match f.df_shape with
      | Ddef (params, _) ->
        Option.map
          (fun ((l : Control_ir.Term.loop), lowering) ->
            ( l.loop,
              lowered_or_left
                (lower_function ~partner:(fun _ -> None) ~tparams f)
                (Option.map (planned_at l lowering) (lifted_positions l params)) ) )
          (lifted_loop (fst f.df_path.dp_outer))
      | Ddecl _ -> None )
  in
  match decided with
  | Some (loop, Ok f') ->
    Loop_verdicts.record loop Lowered;
    with_function f' d
  | Some (loop, Error unlowered) ->
    Loop_verdicts.record loop (Unlowered (reason unlowered));
    lower_locals ~unlowered d
  | None -> lower_locals d

let lower_group decls =
  let functions = List.filter_map function_of decls in
  let partner g =
    List.find_map
      (fun (_, (f : dfun)) ->
        if List.exists (fun (r, _) -> GlobRef.UserOrd.equal r g) (dfun_path_list f.df_path) then Loopify_analysis.registered f
        else None )
      functions
  in
  let plans = List.map (fun d -> (d, Option.bind (function_of d) (fun (_, f) -> planned f))) decls in
  let involved d =
    match decl_globref d with
    | Some r -> Recursion_plan.inlinings r <> [] || Recursion_plan.inlined r
    | None -> false
  in
  (* A member's partners are inlined into it as they were generated, not
     lowered.  So the members that inline one another, those a loop is made
     of, are lowered here all of them or none.  A member no loop is made of,
     its ControlIR's loop continued by no call, has nothing inlined into it,
     and is left as it was generated. *)
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
      let verdict v =
        match decl_globref d with
        | Some r when loopified d -> Loop_verdicts.record (Control_ir.Loop.Function r) v
        | Some _ | None -> ()
      in
      match l with
      | Ok f when all_lowered || not (involved d) ->
        verdict Lowered;
        with_function f d
      | Ok _ ->
        verdict (Unlowered "a member it inlines into, or one inlined into it, is left");
        lower_locals d
      | Error unlowered ->
        verdict (Unlowered (reason unlowered));
        lower_locals ~unlowered d )
    lowered

(* Whether [stmts], closures' bodies included, make a call of one of the
   occurrences [taken]. *)
let keeps_call taken stmts =
  let exception Found in
  let rec fe e =
    ( match e with
    | CPPfun_call ({cs_occurrence = Some o; _}, _, _) when List.exists (Miniml.Occurrence.equal o) taken ->
      raise_notrace Found
    | _ -> () );
    map_expr fe fs Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  match List.iter (fun s -> ignore (fs s)) stmts with () -> false | exception Found -> true

let check_lowered decl =
  let violation (l : Control_ir.Loop.t) what =
    Probe.violation "control lowering"
      Pp.(
        str what ++ str ": "
        ++ match l with Function r -> str (Table.kername_of_global r) | Member _ -> str "a local fixpoint" )
  in
  (* The loop [l], emitted as [body]: a lowering recorded as [recorded]
     allows, and no call left of the turns it takes. *)
  let emitted l ~recorded body =
    if not (recorded (Loop_verdicts.find l)) then violation l "a loop was emitted that control lowering did not lower";
    match Lower_control.loop l with
    | Some t ->
      if keeps_call (Lower_control.taken_continues t) body then violation l "a lowered loop still makes a call it takes"
    | None -> violation l "a lowered loop has no ControlIR"
  in
  (* The definition of the loop [l], emitted as generated: not lowered, and
     decided on where the plan [committed] it to a loop. *)
  let unlowered l ~committed =
    match Loop_verdicts.find l with
    | Some Lowered -> violation l "a loop control lowering lowered was not emitted"
    | Some (Unlowered _ | Kept) -> ()
    | None -> if committed then violation l "the plan commits to a loop control lowering never decided on"
  in
  let lowered = function Some Loop_verdicts.Lowered -> true | Some (Unlowered _ | Kept) | None -> false in
  let function_ (f : dfun) =
    match (f.df_shape, f.df_path.dp_inner) with
    | Ddef (_, body), [] -> (
      let r = fst f.df_path.dp_outer in
      match (f.df_loop, Option.bind (Lifted.of_ref r) Lifted.fixpoint) with
      | Some l, _ -> emitted l ~recorded:lowered body
      | None, Some (o, m) -> unlowered (Member (o, m)) ~committed:(Option.has_some (lifted_loop r))
      | None, None -> unlowered (Function r) ~committed:(Option.has_some (planned_loop r)) )
    | (Ddef _ | Ddecl _), _ -> ()
  in
  let method_ (m : method_field) =
    match (m.mf_loop, m.mf_globref) with
    | Some l, _ -> emitted l ~recorded:lowered m.mf_body
    | None, Some r -> unlowered (Function r) ~committed:(Option.has_some (method_loop r))
    | None, None -> ()
  in
  (* A local fixpoint lowered with the machine it is in is one control
     lowering kept for that machine. *)
  let fixpoint (l : cpp_lambda) =
    match l.cl_fixpoint with
    | Some {lf_member = o, m; lf_encoding = Lowered; _} ->
      emitted (Member (o, m)) l.cl_body ~recorded:(function
        | Some (Loop_verdicts.Lowered | Kept) -> true
        | Some (Unlowered _) | None -> false )
    | Some {lf_member = (o, m) as member; lf_encoding = Self_passing [_]; _} ->
      let committed =
        match Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member with
        | Some (Tail_loop | Modulo_cons _ | Frame_stack) -> true
        | Some (No_loop | Suspended _) | None -> false
      in
      unlowered (Member (o, m)) ~committed
    | Some {lf_encoding = Self_passing _ | Knot; _} | None -> ()
  in
  let rec fields fs =
    List.iter
      (fun (f, _, _) ->
        match f with
        | Fmethod m | Fmember_decl (OLmethod m) -> method_ m
        | Fnested_struct (_, fs) -> fields fs
        | _ -> () )
      fs
  in
  let rec decls = function
    | Dtemplate (_, _, d) -> decls d
    | Dnspace (_, ds) -> List.iter decls ds
    | Dfun f -> function_ f
    | Dstruct ds | Dfields ds ->
      Loopify.check_pointer_fields ds;
      fields ds.ds_fields
    | Dmember_def {dm_field = OLmethod m; _} -> method_ m
    | _ -> ()
  in
  decls decl;
  let rec fe e =
    (match e with CPPlambda l -> fixpoint l | _ -> ());
    map_expr fe fs Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  ignore (map_decl fe fs Fun.id decl)
