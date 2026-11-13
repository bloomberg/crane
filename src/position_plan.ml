(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ type each coercion's position is generated against, planned
    from Core.  See [position_plan.mli]. *)

open Miniml
open Minicpp
open Translation_state
open Ml_type_util
open Translation_support
open Translation_types

let push ids lex =
  Lexenv.push
    (List.map (fun (x, ty) -> {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = Lexenv.Value}) ids)
    lex

(* The return type a let's right-hand side is generated under
   ({!Translation.gen_stmts}' [MLletin]): the binder's own type where it
   says one, else the one in force. *)
let let_result env ~ret t =
  let c = cpp_of_ml env t in
  if prints_as_any c then Some c
  else if ml_type_contains_erased t then ret
  else match spell_in_scope c with Some _ as t -> t | None -> ret

(* An environment naming the binders of [lex] as they are bound, for the
   conversions that look a binder's name up (an instance passed as a
   template argument); a position's type names none. *)
let named_env (lex : Lexenv.t) : Common.env = (List.map (fun (b : Lexenv.binder) -> b.eb_id) (lex :> Lexenv.binder list), Names.Id.Set.empty)

let region ~outer body =
  let found = ref [] in
  let env = Common.empty_env () in
  (* [expr ~pos ~ret lex e]: [e] generated as an expression against [pos],
     with [ret] the return type in force. *)
  let rec expr ~pos ~ret lex e =
    match e with
    | MLmagic (_, t, occ) ->
      found := (occ, At pos) :: !found;
      expr ~pos:(match t with MLlam _ -> pos | _ -> None) ~ret lex t
    (* A coercion stored in a field is lowered against the field's type. *)
    | MLcons (_, _, args, _) ->
      List.iter
        (function
          | MLmagic (_, t, occ) ->
            found := (occ, Stored) :: !found;
            expr ~pos:None ~ret lex t
          | a -> expr ~pos:None ~ret lex a )
        args
    (* Only the returned value is generated, at no position. *)
    | MLapp (MLglob use, (_ :: _ as args)) when is_effect Core_effects.Return use ->
      expr ~pos:None ~ret lex (Common.last args)
    (* A sequential bind in an expression is the statements it desugars to. *)
    | MLapp (MLglob use, _ :: _ :: _) when is_sequential_effect Core_effects.Bind use -> stmts ~ret lex e
    | MLapp (MLglob use, args) -> call ~pos ~ret lex use args
    | MLapp ((MLfix _ as f), args) ->
      stmts ~ret lex f;
      List.iter (expr ~pos:None ~ret lex) args
    | MLletin _ -> stmts ~ret:pos lex e
    | MLfix _ -> stmts ~ret lex e
    | MLcase (typ, scrut, branches, occ) -> (
      expr ~pos:None ~ret lex scrut;
      match Core_elaborate.match_kind typ branches occ with
      | Match_kind.Record _ -> Array.iter (branch ~ret:pos lex) branches
      | Match_kind.Custom ->
        let rty = match Array.to_list branches with (_, rty, _, _) :: _ -> rty | [] -> typ in
        let r = cpp_of_ml env rty in
        let ret = if is_cpp_unit_type r || ml_type_is_void_call rty then Some Tvoid else ret in
        Array.iter (branch ~ret lex) branches
      | Match_kind.Variant ->
        let is_enum =
          match typ with Tglob ((Names.GlobRef.IndRef _ as r), _, _) -> Table.is_enum_inductive r | _ -> false
        in
        let ret = if is_enum && iife_void_return env typ branches = Some Tvoid then Some Tvoid else ret in
        Array.iter (branch ~ret lex) branches )
    (* A lambda's body is a region of its own, planned where it begins. *)
    | MLlam _ -> ()
    | e -> Mlutil.ast_iter (expr ~pos:None ~ret lex) e
  and branch ~ret lex (ids, _, _, body) = stmts ~ret (push (List.rev ids) lex) body
  (* [stmts ~ret lex e]: [e] generated as statements whose tail is the
     result, under the return type [ret]. *)
  and stmts ~ret lex e =
    match e with
    | MLletin (x, t, a, b, _) ->
      ( match x with
      | Dummy -> ()
      | _ -> if ml_type_is_unit t then stmts ~ret lex a else stmts ~ret:(let_result env ~ret t) lex a );
      stmts ~ret (push [(x, t)] lex) b
    | MLcase (_, scrut, branches, _) ->
      expr ~pos:None ~ret lex scrut;
      Array.iter (branch ~ret lex) branches
    | MLfix (_, fs, defs, _, _) ->
      let lex = push (List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs)) lex in
      Array.iter (expr ~pos:None ~ret lex) defs
    (* A sequential bind is its action, generated at no position, then its
       continuation's body as statements under the same return type. *)
    | MLapp (MLglob use, (_ :: _ :: _ as args)) when is_effect Core_effects.Bind use ->
      if is_sequential_effect Core_effects.Bind use then (
        let a, f = Common.last_two args in
        expr ~pos:None ~ret lex a;
        let ids, body = Mlutil.collect_lams f in
        stmts ~ret (push ids lex) body )
      else expr ~pos:None ~ret lex e
    | MLapp (MLglob use, (_ :: _ as args)) when is_effect Core_effects.Return use ->
      if is_sequential_effect Core_effects.Return use then (
        if ret <> Some Tvoid then expr ~pos:ret ~ret lex (Common.last args) )
      else expr ~pos:None ~ret lex e
    | e -> expr ~pos:ret ~ret lex e
  (* A global call's arguments, each against the parameter it is passed at
     ({!Translation_calls.argument_position}). *)
  and call ~pos ~ret lex use args =
    match Core_elaborate.planned_instantiation use args with
    | None -> List.iter (expr ~pos:None ~ret lex) args
    | Some inst ->
      let plan =
        with_cpp_return_type ret (fun () -> Translation_calls.plan_call ~lex ?expected_ty:pos (named_env lex) inst)
      in
      let regular_index a =
        let rec go i = function [] -> None | r :: rest -> if r == a then Some i else go (i + 1) rest in
        go 0 inst.call.regular
      in
      List.iter
        (fun a ->
          match regular_index a with
          | Some i when (match strip_magic a with MLdummy _ -> false | _ -> true) ->
            (* Whether a local read is a callable decides only the position
               of that read, which holds no coercion. *)
            let ap =
              with_cpp_return_type ret (fun () ->
                  with_promoted_var_map (plan.cp_instance_promoted @ (!tctx).promoted_var_map) (fun () ->
                      Translation_calls.argument_position ~local_callable:(fun _ -> false) (named_env lex) use.callee plan i a ) )
            in
            expr ~pos:ap.ap_expected ~ret:ap.ap_ret lex a
          | _ -> expr ~pos:None ~ret lex a )
        args
  in
  (* A walk that fails leaves the coercions it did not reach unplanned,
     which lowering reports. *)
  (try stmts ~ret:(!tctx).current_cpp_return_type outer body
   with e when CErrors.noncritical e -> Probe.hit "magic-pos-walk" (fun () -> Printexc.to_string e));
  !found
