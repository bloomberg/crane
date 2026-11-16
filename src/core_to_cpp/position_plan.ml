(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ type each coercion's position is generated against, planned
    from Core.  See [position_plan.mli]. *)

open Lowering_state
open Base.Type_util
open Core_plan.Query
open Cpp_ir.Type

let push ids lex =
  Core.Lexenv.push
    (List.map (fun (x, ty) -> {Core.Lexenv.id = Base.Core_util.id_of_binder_name x; type_ = ty; role = Core.Lexenv.Value}) ids)
    lex

(* The return type a let's right-hand side is generated under
   ({!Stmts.gen_stmts}' [Core.Expr.Let]): the binder's own type where it
   says one, else the one in force. *)
let let_result cx env ~(ret : Cpp_ir.Lowered.Type.t option) t =
  let c = Types.cpp_of_core cx env t in
  if Cpp_ir.Types.prints_as_any c then Some c
  else if core_type_contains_erased t then ret
  else match Types.spell_in_scope cx c with Some _ as t -> t | None -> ret

(* An environment naming the binders of [lex] as they are bound, for the
   conversions that look a binder's name up (an instance passed as a
   template argument); a position's type names none. *)
let named_env (lex : Core.Lexenv.t) : Base.Common.env =
  (List.map (fun (b : Core.Lexenv.binder) -> b.id) (lex :> Core.Lexenv.binder list), Names.Id.Set.empty)

(* The slot a coercion's inner term is generated in
   ({!Expr.gen_crossing}): boxed where it crosses from a
   type that is not a box into one that is, unless the position states a
   type that is not one. *)
let coerced_slot cx env ~(pos : Cpp_ir.Lowered.Type.t option) slot ~from ~into =
  if
    (match pos with Some t -> Cpp_ir.Types.prints_as_any t | None -> true)
    && Cpp_ir.Types.prints_as_any (Types.cpp_of_core cx env into)
    && not (Cpp_ir.Types.prints_as_any (Types.cpp_of_core cx env from))
  then Slot.into_box (Types.box_kind_of_cpp_type (Types.cpp_of_core cx env
    into)) slot
  else slot

let region cx ~outer ~reads body =
  let found = ref [] in
  let env = Base.Common.empty_env () in
  let is_boxed _ occ =
    match List.assq_opt occ reads with Some r -> r.Lowering_state.Planned_read.boxed | None -> false
  in
  (* [expr ~pos ~ret ~slot lex e]: [e] generated as an expression against
     [pos], into [slot], with [ret] the return type in force. *)
  let rec expr ~(pos : Cpp_ir.Lowered.Type.t option) ~(ret : Cpp_ir.Lowered.Type.t option)
      ?(slot = Slot.empty_slot) lex e =
    match e with
    | Core.Expr.Coerce {source_type = from; target_type = into; value = t; occurrence = occ} ->
      found := (occ, pos) :: !found;
      let env = named_env lex in
      expr ~pos:(match t with Core.Expr.Lambda _ -> pos | _ -> None) ~ret
        ~slot:(coerced_slot cx env ~pos slot ~from ~into) lex t
    | Core.Expr.Boxed_value {value = t;
                             occurrence = occ} | Core.Expr.Lambda_group_barrier {value = t; occurrence = occ} ->
      found := (occ, pos) :: !found;
      expr ~pos:(match t with Core.Expr.Lambda _ -> pos | _ -> None) ~ret ~slot lex t
    | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _} when Base.Table.is_custom r ->
      with_cpp_return_type cx ret (fun () -> custom ~pos ~slot lex ty r ts)
    | Core.Expr.Construct {arguments = []; _} -> ()
    | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _} ->
      with_cpp_return_type cx ret (fun () -> construction ~pos ~ret ~slot lex ty r ts)
    (* Only the returned value is generated, at no position. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = (_ :: _ as args)} when Monadic.is_effect cx Core_plan.Effects.Return use ->
      expr ~pos:None ~ret lex (Base.Common.last args)
    (* A sequential bind in an expression is the statements it desugars to. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = _ :: _ :: _} when Monadic.is_sequential_effect cx
                         Core_plan.Effects.Bind use ->
      stmts ~ret lex e
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} -> call ~pos ~ret ~slot lex use args
    | Core.Expr.Apply {callee = (Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ as f); arguments = args} ->
      stmts ~ret lex f;
      List.iter (expr ~pos:None ~ret lex) args
    | Core.Expr.Let _ -> stmts ~ret:pos lex e
    | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> stmts ~ret lex e
    | Core.Expr.Match {scrutinee_type = typ; scrutinee = scrut; branches; occurrence = occ} -> (
      expr ~pos:None ~ret lex scrut;
      match Core_plan.Elaborate.match_kind ~walk:(elaborations cx) typ branches occ with
      | Core_plan.Match_kind.Record _ -> Array.iter (branch ~ret:pos lex) branches
      | Core_plan.Match_kind.Custom ->
        let rty = match Array.to_list branches with {Core.Match.Branch.result_type = rty; _} :: _ -> rty | [] -> typ in
        let r = Types.cpp_of_core cx env rty in
        let ret = if is_cpp_unit_type r || Monadic.core_type_is_void_call rty then Some Void else ret in
        Array.iter (branch ~ret lex) branches
      | Core_plan.Match_kind.Variant ->
        let is_enum =
          match typ with Core.Type.Global_app {head = (Names.GlobRef.IndRef _ as r); _} ->
            Base.Table.is_enum_inductive r | _ -> false
        in
        let ret =
          if is_enum && Match_types.iife_void_return cx env typ branches = Some Void then Some Void else ret
        in
        Array.iter (branch ~ret lex) branches )
    (* A lambda's body is a region of its own, planned where it begins. *)
    | Core.Expr.Lambda _ -> ()
    | e -> Base.Core_util.ast_iter (expr ~pos:None ~ret lex) e
  (* A value a constructor stores ({!Construction.gen_stored_value}). *)
  and stored ~pos ~ret ~slot lex e =
    match e with
    | Core.Expr.Erased_value _ -> ()
    | e when Monadic.core_value_is_void_call cx e -> expr ~pos:None ~ret ~slot lex e
    | e -> expr ~pos ~ret ~slot lex e
  (* A constructor of Crane's own, each argument at the field it fills
     ({!Constructors}). *)
  and construction ~pos ~ret ~slot lex ty r ts =
    let env = named_env lex in
    let slot = Constructors.into_erased_return cx slot in
    let ty = Constructors.refined_by_slot slot ty in
    with_in_constructor_expr cx true @@ fun () ->
    match Base.Table.record_fields_of_type ty with
    | [] ->
      let c = Constructors.regular cx env ~expected_ty:pos ty r ts in
      List.iteri
        (fun i e ->
          let p, s =
            with_cpp_return_type cx None (fun () -> Constructors.regular_field cx env ~is_boxed c ~slot i e)
          in
          stored ~pos:p ~ret:None ~slot:s lex e )
        c.args
    | _ ->
      with_promoted_var_map cx (Constructors.record_promoted_map cx ty) @@ fun () ->
      List.iteri
        (fun i e ->
          let p, s = Constructors.record_field cx env ~is_boxed ty r ~slot i e in
          stored ~pos:p ~ret ~slot:s lex e )
        ts
  (* A custom constructor, each argument where its mapping stores it
     ({!Constructors.custom_field}). *)
  and custom ~pos ~slot lex ty r ts =
    let env = named_env lex in
    let var i occ = (is_boxed i occ, Core.Lexenv.type_opt lex i) in
    let slot = Constructors.into_erased_return cx slot in
    let ty = Constructors.custom_refined_annotation cx env ~expected_ty:pos ~slot ty r ts in
    with_in_constructor_expr cx true @@ fun () ->
    let c = Constructors.custom cx env ~expected_ty:pos ~slot ty r in
    List.iteri
      (fun i e ->
        let a = Constructors.custom_field cx ~var env c ~slot r i e in
        with_cpp_return_type cx a.ret
          (fun () -> stored ~pos:a.expected ~ret:a.ret ~slot:a.slot lex a.term) )
      ts
  and branch ~ret ?slot lex {Core.Match.Branch.binders = ids; body = body; _} =
    stmts ~ret ?slot (push (List.rev ids) lex) body
  (* [stmts ~ret ~slot lex e]: [e] generated as statements whose tail is
     the result, under the return type [ret], into [slot]. *)
  and stmts ~ret ?(slot = Slot.empty_slot) lex e =
    match e with
    | Core.Expr.Let {binder = x; binder_type = t; value = a; body = b; _} ->
      ( match x with
      | Core.Binder_name.Anonymous -> ()
      | _ ->
        let slot = {slot with Slot.repr = Native; expected_core_ty = Some t} in
        if core_type_is_unit t then stmts ~ret ~slot lex a else stmts ~ret:(let_result cx env ~ret t) ~slot lex a );
      stmts ~ret ~slot (push [(x, t)] lex) b
    | Core.Expr.Match {scrutinee_type = typ; scrutinee = scrut; branches; occurrence = occ} ->
      expr ~pos:None ~ret lex scrut;
      let slot =
        match Core_plan.Elaborate.match_kind ~walk:(elaborations cx) typ branches occ with Core_plan.Match_kind.Record _ ->
          slot | _ -> Slot.empty_slot in
      Array.iter (branch ~ret ~slot lex) branches
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let fs = Core.Recursion.Group.functions rec_group and defs = Core.Recursion.Group.bodies rec_group in
      let lex = push (List.rev_map (fun (f, ty) -> (Core.Binder_name.Source f, ty)) (Array.to_list fs)) lex in
      Array.iter (expr ~pos:None ~ret lex) defs
    (* A sequential bind is its action, generated at no position, then its
       continuation's body as statements under the same return type. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = (_ :: _ :: _ as args)} when Monadic.is_effect cx Core_plan.Effects.Bind use ->
      if Monadic.is_sequential_effect cx Core_plan.Effects.Bind use then (
        let a, f = Base.Common.last_two args in
        expr ~pos:None ~ret lex a;
        let ids, body = Base.Core_util.collect_lams f in
        stmts ~ret ~slot (push ids lex) body )
      else expr ~pos:None ~ret lex e
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = (_ :: _ as args)} when Monadic.is_effect cx Core_plan.Effects.Return use ->
      if Monadic.is_sequential_effect cx Core_plan.Effects.Return use then (
        if ret <> Some Void then expr ~pos:ret ~ret lex (Base.Common.last args) )
      else expr ~pos:None ~ret lex e
    | e -> expr ~pos:ret ~ret ~slot lex e
  (* A global call's arguments, each against the parameter it is passed at
     ({!Calls.argument_position}), into the call's slot at the
     parameter's Core type. *)
  and call ~pos ~ret ~slot lex (use : Core.Global_use.t) args =
    match Core_plan.Elaborate.planned_instantiation ~walk:(elaborations cx) use args with
    | None -> List.iter (expr ~pos:None ~ret lex) args
    | Some inst ->
      let plan =
        with_cpp_return_type cx ret (fun () ->
            Calls.plan_call cx ~lex ?expected_ty:pos (named_env lex) inst )
      in
      let regular_index a =
        let rec go i = function [] -> None | r :: rest -> if r == a then Some i else go (i + 1) rest in
        go 0 inst.call.regular
      in
      with_promoted_var_map cx (plan.Calls.instance_promoted @ cx.ctx.lexical.promoted_var_map)
      @@ fun () ->
      List.iter
        (fun a ->
          match regular_index a with
          | Some i when (match strip_magic a with Core.Expr.Erased_value _ -> false | _ -> true) ->
            (* Whether a local read is a callable decides only the position
               of that read, which holds no coercion. *)
            let ap =
              with_cpp_return_type cx ret (fun () ->
                  Calls.argument_position cx ~local_callable:(fun _ _ -> false) (named_env lex)
                    use.callee plan i a )
            in
            let slot =
              { slot with
                Slot.expected_core_ty =
                  (match ap.Calls.param with Some t when not (core_type_contains_erased t) -> Some t
                    | _ -> slot.Slot.expected_core_ty);
                stated_core_ty = ap.Calls.param }
            in
            expr ~pos:ap.Calls.expected ~ret:ap.Calls.ret ~slot lex a
          | _ -> expr ~pos:None ~ret lex a )
        args
  in
  (* A walk that fails leaves the coercions it did not reach unplanned,
     which lowering reports. *)
  (try stmts ~ret:(current_cpp_return_type cx ()) outer body
   with e when CErrors.noncritical e -> Base.Probe.hit "magic-pos-walk" (fun () -> Printexc.to_string e));
  !found
