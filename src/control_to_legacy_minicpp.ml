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
  if
    Table.should_loopify r
    && not (Option.has_some (Lifted.of_ref r))
    && tail_loop ()
    && Recursion_plan.inlinings r = []
    && not (Recursion_plan.inlined r)
  then
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

(* The jump a C++ call is, where it is made of one of the Continues
   [continues]: the arguments it passes the loop's parameters. *)
let jump continues : Loopify_analysis.call_checker = function
  | CPPfun_call ({cs_occurrence = Some o; _}, _, args) when List.exists (Miniml.Occurrence.equal o) continues ->
    Some (Loopify_analysis.mk_call_site (to_reversed args))
  | _ -> None

(* Under [CRANE_CHECK_IR]: the loop [loop] of the function [f], lowered from
   [body] jumping at the calls [jumped], against the loop's Continues
   [continues] and the loop Loopify's own transform makes. *)
let check ~tparams (f : dfun) params body ~varying ~continues ~jumped loop =
  let what = Pp.str (Table.kername_of_global (fst f.df_path.dp_outer)) in
  if not (Loopify_analysis.made_as_planned continues jumped) then
    Probe.violation "control IR"
      Pp.(str "the calls the tail loop of " ++ what ++ str " jumps at are not its Continues");
  let exposed = Loopify_analysis.expose_tail_calls (jump continues) body in
  if Loopify_analysis.find_varying_params (jump continues) params exposed <> varying then
    Probe.violation "control lowering"
      Pp.(str "the calls of " ++ what ++ str " change other parameters than its ControlIR's Continues");
  if compare (Loopify.checker_tail_loop ~tparams f params body) loop <> 0 then
    Probe.violation "control lowering"
      Pp.(str "the tail loop of " ++ what ++ str " lowered from its ControlIR is not the loop Loopify makes")

let lower_function ~tparams (f : dfun) =
  match (f.df_shape, f.df_path.dp_inner) with
  | Ddef (params, body), [] -> (
    let r = fst f.df_path.dp_outer in
    match Option.bind (planned_loop r) (fun l -> Option.map (fun v -> (l, v)) (varying r l f.df_binders params)) with
    | None -> None
    | Some (l, varying) -> (
      let continues = Control_ir.continues l.body in
      let jumps = ref [] in
      let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
      let exposed = Loopify_analysis.expose_tail_calls (jump continues) body in
      match Loopify_tail.transform_tail ~jumped ~varying tparams (jump continues) params f.df_ret exposed with
      (* A function Loopify declines whole -- a call passing the loop other
         arguments than it has parameters, say -- is left to it, and is
         declined as before. *)
      | exception Loopify_analysis.Not_linearisable _ -> None
      | loop -> (
        if Probe.checking () then
          check ~tparams f params body ~varying ~continues ~jumped:(List.rev !jumps) loop;
        match Loopify.after_tail_loop ~tparams f params loop with
        | exception Loopify_analysis.Not_linearisable _ -> None
        | body -> Some {f with df_shape = Ddef (params, body); df_loop = Some l.loop} ) ) )
  | (Ddef _ | Ddecl _), _ -> None

let lower_decl d =
  let rec lower ~tparams = function
    | Dtemplate (tparams, c, inner) -> Dtemplate (tparams, c, lower ~tparams inner)
    | Dfun f as d -> ( match lower_function ~tparams f with Some f -> Dfun f | None -> d )
    | d -> d
  in
  lower ~tparams:[] d
