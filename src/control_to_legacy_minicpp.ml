(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Minicpp

(* The tail loop of the function [r], where it is one this module lowers. *)
let planned_loop r =
  let tail_loop () =
    match Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r with
    | Some Tail_loop -> true
    | Some (No_loop | Modulo_cons _ | Frame_stack | Suspended _) | None -> false
  in
  if Table.should_loopify r && (not (Option.has_some (Lifted.of_ref r))) && tail_loop () then
    match Lower_control.loop (Control_ir.Loop.Function r) with
    | Some (Loop l) when Control_ir.continues l.body <> [] -> Some l
    | Some _ | None -> None
  else None

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
    Option.bind (planned_loop r) (fun l -> Option.map (fun v -> (l, v)) (varying r l f.df_binders params))
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
   inlines read as [partner] has it; [None] where Loopify declines it
   whole -- a call passing the loop other arguments than it has
   parameters, say -- and is left to, to decline it as before. *)
let lower_function ~partner ~tparams (f : dfun) ((l : Control_ir.Term.loop), varying) =
  match f.df_shape with
  | Ddecl _ -> None
  | Ddef (params, body) -> (
    let continues = Control_ir.continues l.body in
    let jumps = ref [] in
    let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
    let r = fst f.df_path.dp_outer in
    let exposed =
      Loopify_analysis.expose_tail_calls (jump continues) (Loopify.try_inline_mutual_into ~partner r body)
    in
    match Loopify_tail.transform_tail ~jumped ~varying tparams (jump continues) params f.df_ret exposed with
    | exception Loopify_analysis.Not_linearisable _ -> None
    | loop -> (
      if Probe.checking () then
        check ~partner ~tparams f params body exposed ~varying ~continues ~jumped:(List.rev !jumps) loop;
      match Loopify.after_tail_loop ~tparams f params loop with
      | exception Loopify_analysis.Not_linearisable _ -> None
      | body -> Some {f with df_shape = Ddef (params, body); df_loop = Some l.loop} ) )

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
   was generated as before. *)
let check_local ~tparams ~name ~self_passing loop =
  if compare (Loopify.lower_local_tail_loops ~tparams (self_passing ())) [loop] <> 0 then
    Probe.violation "control lowering"
      Pp.(
        str "the local fixpoint " ++ Id.print name
        ++ str " lowered from its ControlIR is not the loop Loopify makes of its Y-combinator" )

(* Whether Loopify makes a machine with a stack of its own of the definition
   [r] -- a method as its struct's methods are loopified -- and lowers the
   local fixpoints in its body only around that machine. *)
let machine r =
  let loopified =
    match Cpp_state.is_registered_method r with
    | Some (inductive, _) -> Table.loopifies_methods_of inductive && Table.loopifies_method r
    | None -> Table.should_loopify r
  in
  loopified
  &&
  match Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r with
  | Some (Modulo_cons _ | Frame_stack) -> true
  | Some (No_loop | Tail_loop | Suspended _) | None -> false

let local_loop ~owner ~member:((occurrence, _) as member) ~tparams ~name ~self_passing (lam : cpp_lambda) =
  let tail_loop =
    match Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member with
    | Some Tail_loop ->
      (not (Recursion_plan.adoptable_somewhere occurrence)) && not (Option.cata machine false owner)
    | Some (No_loop | Modulo_cons _ | Frame_stack | Suspended _) | None -> false
  in
  match Lower_control.loop (Control_ir.Loop.Member (fst member, snd member)) with
  | Some (Loop l) when tail_loop && Control_ir.continues l.body <> [] -> (
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
      match Loopify_tail.transform_tail ~jumped ~varying tparams (jump continues) params ret_ty exposed with
      | exception Loopify_analysis.Not_linearisable _ -> None
      | body ->
        (* A call of the fixpoint the loop does not take -- one in a closure
           it builds -- or the fixpoint named as a value calls a lambda that
           is no longer there: it stays the Y-combinator Loopify declines. *)
        let calls = Recursion_plan.member_calls member in
        let left = function
          | CPPvar x -> Id.equal x name
          | e -> ( match Loopify_analysis.made_of e with Some o -> List.exists (Miniml.Occurrence.equal o) calls | None -> false )
        in
        if Loopify_analysis.body_exists left body then None
        else begin
          if Probe.checking () then begin
            if not (Loopify_analysis.made_as_planned continues (List.rev !jumps)) then
              Probe.violation "control IR"
                Pp.(str "the calls the tail loop of the local fixpoint " ++ Id.print name ++ str " jumps at are not its Continues");
            if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
              Probe.violation "control lowering"
                Pp.(str "the calls of the local fixpoint " ++ Id.print name ++ str " change other parameters than its ControlIR's Continues")
          end;
          Loopify_analysis.record_outcome (Id.to_string name) Lp_tail;
          let loop = {lam with cl_body = body; cl_moved = []} in
          let moved = List.filter (fun x -> List.mem x (free_vars_expr (CPPlambda loop))) lam.cl_moved in
          let stmt = Sasgn (name, Declare (Tauto, None), CPPlambda {loop with cl_moved = moved}) in
          if Probe.checking () then check_local ~tparams ~name ~self_passing stmt;
          Some stmt
        end )
  | Some _ | None -> None

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
     inline one another, those Loopify would loopify, are lowered here all
     of them or none. *)
  let loopified d = match decl_globref d with Some r -> Table.should_loopify r | None -> false in
  let all_planned = List.for_all (fun (d, p) -> Option.has_some p || not (involved d && loopified d)) plans in
  let lowered =
    List.map
      (fun (d, p) ->
        let lowered =
          if involved d && not all_planned then None
          else
            match (function_of d, p) with
            | Some (tparams, f), Some plan -> lower_function ~partner ~tparams f plan
            | _ -> None
        in
        (d, lowered) )
      plans
  in
  let all_lowered = List.for_all (fun (d, l) -> Option.has_some l || not (involved d && loopified d)) lowered in
  List.map
    (fun (d, l) ->
      match l with
      | Some f when all_lowered || not (involved d) -> with_function f d
      | Some _ | None -> d )
    lowered
