(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Lowering of local functions to CppIR: a local fixpoint declared in
    place as a loop ({!local_fix_stmts}), a Y-combinator closure
    ({!gen_local_fix_ycomb}) or a by-reference group
    ({!gen_local_fix_by_ref}), each member's body lowered by {!gen_fix};
    and a let-bound lambda or fixpoint lifted out of the body as a helper
    declaration ({!gen_let_lambda}, {!gen_let_fix}, {!gen_applied_fix}).

    Sits between {!Effects} and {!Stmts} in the
    chain of lowering modules; its entry points are called from
    {!Stmts.gen_stmts}, and it lowers the bodies it declares by
    calling back up through {!Knot}. *)

open Base.Common
open Names
open Base.Core_util
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query
open Knot
open Lambda
open Application

module IntSet = Core_plan.Escape.IntSet

(** Whether the local fixpoint group [occ] stands in the tail of a body
    suspended whole ([suspended_tail] in {!Lowering_state}). *)
let in_suspended_tail cx occ = List.exists (Core.Occurrence.equal occ) cx.ctx.input.suspended_tail

(** How the local fixpoint group [occ] standing where generation is, let-bound
    in [continuation] or else applied, is generated ({!Core_plan.Closures.group}):
    its constructors suspended as {!Suspension.suspends_constructor} says,
    and in the value a body suspended whole returns where the body says so
    ([suspended_tail] in {!Lowering_state}). *)
let closures_group cx ~n_outer ~occ ?continuation ~cofix ids funs =
  Core_plan.Closures.group ~effects:cx.ctx.input.unit.effects ~n_outer
    ~suspends:(Suspension.suspends_constructor cx ~self:cx.ctx.input.body_owner)
    ~lex:(current_lexenv cx ()) ~suspended:(in_suspended_tail cx occ) ?continuation ~cofix ids funs

(** The binders of the local fixpoint [occ], as the source has them, each
   with the member of the fixpoint it binds and the Core binders of that
   member's parameters, as [compiled], what {!gen_fix} made of each member,
   has them, and with them the Core binders of the locals of [env] the fixpoint
   [fix], generated under [env], reads, by name. *)
let local_fix_binders cx env fix occ ids compiled =
  let read = ref [] in
  Base.Core_util.ast_iter_rel_applied (fun n i _ -> if i > n then read := (i - n) :: !read) fix;
  let captured =
    List.filter_map
      (fun db ->
        match (get_db_name_opt db env, core_binder cx env db) with
        | Some x, Some b -> Some (x, b)
        | _ -> None )
      (List.sort_uniq Int.compare !read)
  in
  List.mapi (fun j ((x, _), (_, _, _, params)) -> (x, (occ, j), params, captured))
    (List.combine (Array.to_list ids) compiled)

(** The local fixpoint bound to [binder], the function [member] of a Core
   fixpoint whose parameters stand for the Core binders [params] and that
   reads the locals [captured] stand for, in the declaration being
   generated, called [name] and encoded as [encoding]. *)
let local_fixpoint ~name ~encoding (binder, member, _, captured) : Cpp_ir.Expr.Local_fixpoint.t option =
  Some {binder; name; member; captured; encoding}

(** The Core binders of the parameters of a member of
    {!local_fix_binders}. *)
let fixpoint_parameters (_, _, params, _) = params

(** The statements a local fixpoint is declared by: for a fixpoint of one
   member, its loop, lowered from its ControlIR, where it is one
   ({!Control_to_cpp.Lower.local_loop}), and otherwise the Y-combinator
   [self_passing ()] -- the impl lambdas [impl_stmts], taking their
   self-parameters [selves], and the wrappers.  The loop is the impl lambda
   without the self-parameter, its body, the one of [funs_with_params],
   calling the fixpoint by its own name ({!Lifting.self_call_rewriter}). *)
let local_fix_stmts cx selves ~binders ~self_passing (impl_stmts : Cpp_ir.Lowered.Stmt.t list) funs_with_params =
  match (selves, binders, impl_stmts, funs_with_params) with
  | [{Lifting.fix_id; _}], [((_, member, _, _) as binder)], [Bind_variable (_, _, Lambda impl)], [(_, body)]
    -> (
    let self_ids = List.map (fun s -> Some s.Lifting.self_id) selves in
    let _, flat = Lifting.self_call_rewriter ~passing:false selves in
    let lam : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t =
      { impl with
        params = List.filter (fun (_, x) -> not (List.mem x self_ids)) impl.params;
        fixpoint = local_fixpoint ~name:fix_id ~encoding:Lowered binder;
        body = List.map flat body }
    in
    match
      Control_to_cpp.Lower.local_loop ~unit:(Lowering_state.unit_context cx) ~owner:cx.ctx.input.body_owner
        ~all_locals:cx.ctx.input.body_all_locals
        ~lifted:cx.ctx.lexical.lifted_fixpoints ~member
        ~tparams:(get_current_template_head cx) ~name:fix_id lam
    with
    | Some loop -> [loop]
    | None -> self_passing () )
  | _ -> self_passing ()

(** How each function of the local fixpoint group whose bodies are [funs]
    passes its parameters ({!Ownership_ir.Region.Local_passing}): a group of
    [closures] takes each by value; one generated in place lends each its
    body does not own ({!Core_plan.Escape.infer_owned_params}).  A parameter of no
    runtime value is taken by no lambda, but is a binder of the body all the
    same: the flag of the parameter [i]th innermost is that of the body's
    binder [i + 1], whatever binders inside it lack a runtime value. *)
let local_passing cx ~closures funs =
  let n_fix = Array.length funs in
  let member f =
    let lam_ids, inner = Base.Core_util.collect_lams f in
    let flags =
      if closures then [] else
        Core_plan.Escape.infer_owned_params ~callee_flags:(settled_ownership cx) (List.length lam_ids + n_fix) inner in
    (* [lam_ids] is innermost first, and the plan outermost first. *)
    List.rev
      (List.mapi
         (fun i (_, ty) ->
           if void_binder ty then None
           else Some (if closures || List.nth flags i then Cpp_ir.Param_mode.Owned else Cpp_ir.Param_mode.Borrowed) )
         lam_ids )
  in
  Array.to_list (Array.map member funs)

(** Record that the functions [binders] name pass their parameters as
   [passing] says, each the plan of the one at its position. *)
let record_local_passing ~binders passing =
  List.iter2 (fun (_, member, _, _) t -> Ownership_ir.Region.Local_passing.record member t) binders passing

(** Record that the functions [binders] name hold their captures as
   [captures] says, each the modes of the one at its position: what
   {!Ownership_ir.Move_check} holds their lambdas to. *)
let record_local_captures ~binders captures =
  List.iter2
    (fun (_, member, _, _) modes -> Ownership_ir.Region.Local_captures.record member (List.map snd modes))
    binders captures

(** Generate local fixpoint declarations using the Y-combinator pattern
    for escaping fixpoints.

    Uses a generic-lambda self-passing pattern rather than a
    [shared_ptr<std::function>]:
    {v
      auto go_impl = [=](auto &_self, A... args) mutable -> R {
        ... _self(_self, args) ...
      };
      auto go = [=](A... args) mutable -> R {
        return go_impl(go_impl, args...);
      };
    v}

    No heap allocation, no [std::function] type erasure.  The [auto &_self]
    parameter uses C++14 generic lambdas.

    For mutual recursion with N functions, each impl takes N self parameters:
    {v
      auto f_impl = [=](auto &_sf, auto &_sg, A...) { ... _sg(_sf, _sg, ...) ... };
      auto g_impl = [=](auto &_sf, auto &_sg, A...) { ... _sf(_sf, _sg, ...) ... };
      auto f = [=](A...) { return f_impl(f_impl, g_impl, ...); };
      auto g = [=](A...) { return g_impl(f_impl, g_impl, ...); };
    v}

    @return [(decls, defs, deref_subst)] where [defs] is empty and
    [deref_subst] is the identity function (no dereferencing needed).
    @see gen_local_fix_by_ref for the non-escaping alternative. *)
let gen_local_fix_ycomb cx env ~binders ~passing ~captures renamed_ids funs_with_params =
  (* The lambdas take every parameter by value, as [passing], a group of
     closures', says. *)
  record_local_passing ~binders passing;
  record_local_captures ~binders captures;
  let moved = List.map (moved_names env) captures in
  let ret_ty ty : Cpp_ir.Lowered.Type.t option =
    match Types.cpp_of_core cx env ty with
    | Function (_, t) ->
      ( match t with
      | Variable (Index (_, None)) -> None
      | _ -> Some t )
    | _ -> None
  in
  (* Create self-parameter IDs and impl IDs for each fixpoint. *)
  let selves = Lifting.local_fix_selves (Types.cpp_of_core cx env) renamed_ids
    funs_with_params in
  let self_ids = List.map (fun s -> s.Lifting.self_id) selves in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  let _, rewrite_stmt = Lifting.self_call_rewriter selves in
  (* Generate impl lambdas: each takes all self params (auto &) + original params. *)
  let impl_stmts =
    List.map2
      (fun (((fix_id, fty), impl_id), binder) (args, body) : Cpp_ir.Lowered.Stmt.t ->
        let self_params : (Cpp_ir.Lowered.Type.t * Id.t option) list =
          List.rev_map (fun sid -> ((Reference (Lvalue, Auto) : Cpp_ir.Lowered.Type.t), Some sid)) self_ids
        in
        let orig_params =
          List.map
            (fun (id, ty) ->
              (Types.cpp_of_core cx env ty, Some id))
            args
        in
        Bind_variable
          ( impl_id,
            Declare (Auto, None),
            Lambda
              { type_params = [];
                fixpoint = local_fixpoint ~name:fix_id ~encoding:(Self_passing self_ids) binder;
                binders = fixpoint_parameters binder;
                modes = List.map (fun (id, _) -> (id, Cpp_ir.Param_mode.owned)) args;
                moved = [];
                params = List.rev (orig_params @ self_params);
                return_type = ret_ty fty;
                body = List.map rewrite_stmt body;
                capture = Stored } ))
      (List.combine (List.combine renamed_ids impl_ids) binders)
      funs_with_params
  in
  (* Each impl takes by move what the plan has its function's closure take
     ([moved]): each variable the group takes so, the last impl capturing it
     takes; the impls before it still copy it.  Under [CRANE_CHECK_IR], the
     impls' C++ captures must agree. *)
  let impl_stmts =
    if Base.Probe.checking () then begin
      let captures : Cpp_ir.Lowered.Stmt.t -> Id.t list = function
        | Bind_variable (_, _, (Lambda _ as l)) -> Cpp_ir.Variables.free_in_expr l
        | _ -> []
      in
      let everything = List.sort_uniq Id.compare (List.concat moved) in
      let rec given = function
        | [] -> []
        | s :: rest ->
          let taken_later = List.concat_map captures rest in
          List.sort Id.compare
            (List.filter (fun x -> List.mem x (captures s) && not (List.mem x taken_later)) everything)
          :: given rest
      in
      if not (List.equal (List.equal Id.equal) (given impl_stmts) moved) then
        Base.Probe.violation "closure captures"
          (Pp.str "a local fixpoint's closures take by move other variables than their C++ captures give them")
    end;
    List.map2
      (fun (s : Cpp_ir.Lowered.Stmt.t) ts : Cpp_ir.Lowered.Stmt.t ->
        match s with
        | Bind_variable (id, d, Lambda l) when ts <> [] -> Bind_variable (id, d, Lambda {l with moved = ts})
        | _ -> s )
      impl_stmts moved
  in
  (* Generate wrapper lambdas: forward to impl with all impl_ids prepended. *)
  let impl_vars_rev = List.rev_map (fun id : Cpp_ir.Lowered.Expr.t -> Local id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun (((fix_id, fty), impl_id), binder) (args, _body) : Cpp_ir.Lowered.Stmt.t ->
        let orig_params =
          List.map
            (fun (id, ty) ->
              (Types.cpp_of_core cx env ty, Some id))
            args
        in
        (* The wrapper reads each parameter once, to forward it. *)
        let fwd_args =
          List.map (fun (id, ty) -> forwarded ~by_value:true ty (Local id)) args @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call : Cpp_ir.Lowered.Expr.t =
          Call (Cpp_ir.Build.signature ~nargs:0 (), Local impl_id, List.rev fwd_args) in
        let wrapper_body : Cpp_ir.Lowered.Stmt.t list =
          match rty with
          | None -> [Expression call]
          | _ -> [Return (Some call)]
        in
        Bind_variable
          ( fix_id,
            Declare (Auto, None),
            Lambda
              { params = List.rev orig_params;
              type_params = [];
              fixpoint = local_fixpoint ~name:fix_id ~encoding:Knot binder;
              binders = fixpoint_parameters binder;
              modes = List.map (fun (id, _) -> (id, Cpp_ir.Param_mode.owned)) args;
              moved = [];
                return_type = rty;
                body = wrapper_body;
                capture = Stored } ))
      (List.combine (List.combine renamed_ids impl_ids) binders)
      funs_with_params
  in
  (* The wrappers are the impls' only readers, and each captures them all:
     the last one made takes them. *)
  let wrapper_stmts =
    match List.rev (wrapper_stmts : Cpp_ir.Lowered.Stmt.t list) with
    | Bind_variable (id, d, Lambda l) :: rest ->
      List.rev
        ((Bind_variable (id, d, Lambda {l with moved = List.sort Id.compare impl_ids}) : Cpp_ir.Lowered.Stmt.t) :: rest)
    | _ -> wrapper_stmts
  in
  let deref_subst stmts = stmts in
  let self_passing () = impl_stmts @ wrapper_stmts in
  (local_fix_stmts cx selves ~binders ~self_passing impl_stmts funs_with_params, [], deref_subst)

(** Generate local fixpoint declarations using the [\[&\]]-capture pattern.

    Used for a group Core generates {!Core_plan.Closures.In_place}: no member
    is used other than in direct call position or escapes into a closure or
    data structure.  The [\[&\]] capture is
    lightweight (no heap allocation, no indirection) but creates dangling
    references if the closure outlives the enclosing scope.

    Uses a Y-combinator pattern to avoid [std::function] type erasure
    overhead (heap allocation, virtual dispatch).  Parameters are passed
    by value to preserve move/mutation semantics.

    Generated C++:
    {v
      auto f_impl = [&](auto& _self_f, A a, B b) -> R {
        ... _self_f(_self_f, a', b') ...
      };
      auto f = [&](A a, B b) -> R {
        return f_impl(f_impl, a, b);
      };
    v}

    @return [(decls, defs)], declaration and definition statement lists;
    [defs] is empty.
    @see gen_local_fix_ycomb for the escaping-fixpoint alternative. *)
let gen_local_fix_by_ref cx env ~binders ~passing ~captures renamed_ids funs_with_params =
  record_local_passing ~binders passing;
  record_local_captures ~binders captures;
  let owned_flags_per_fun = List.map owned_flags passing in
  let ret_ty ty : Cpp_ir.Lowered.Type.t option =
    match Types.cpp_of_core cx env ty with
    | Function (_, t) ->
      ( match t with
      | Variable (Index (_, None)) -> None
      | _ -> Some t )
    | _ -> None
  in
  let selves = Lifting.local_fix_selves (Types.cpp_of_core cx env) renamed_ids
    funs_with_params in
  let self_ids = List.map (fun s -> s.Lifting.self_id) selves in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  let _, rewrite_stmt = Lifting.self_call_rewriter selves in
  let impl_stmts =
    List.map2
      (fun ((((fix_id, fty), impl_id), binder), owned_flags) (args, body) : Cpp_ir.Lowered.Stmt.t ->
        let self_params : (Cpp_ir.Lowered.Type.t * Id.t option) list =
          List.rev_map (fun sid -> ((Reference (Lvalue, Auto) : Cpp_ir.Lowered.Type.t), Some sid)) self_ids
        in
        let orig_params, modes =
          List.split
            (List.map2
               (fun (id, ty) owned ->
                 let cpp_ty, mode = Ownership.wrap_param_by_ownership cx ~is_owned:owned (Types.cpp_of_core cx env ty) in
                 ((cpp_ty, Some id), (id, mode)) )
               args owned_flags )
        in
        Bind_variable
          ( impl_id,
            Declare (Auto, None),
            Lambda
              { params = List.rev (orig_params @ self_params);
              type_params = [];
              fixpoint = local_fixpoint ~name:fix_id ~encoding:(Self_passing self_ids) binder;
              binders = fixpoint_parameters binder;
              modes;
              moved = [];
                return_type = ret_ty fty;
                body = List.map rewrite_stmt body;
                capture = Runs_in_place } ))
      (List.combine (List.combine (List.combine renamed_ids impl_ids) binders) owned_flags_per_fun)
      funs_with_params
  in
  let impl_vars_rev = List.rev_map (fun id : Cpp_ir.Lowered.Expr.t -> Local id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun ((((fix_id, fty), _impl_id), binder), owned_flags) (args, _body) : Cpp_ir.Lowered.Stmt.t ->
        let orig_params, modes =
          List.split
            (List.map2
               (fun (id, ty) owned ->
                 let cpp_ty, mode = Ownership.wrap_param_by_ownership cx ~is_owned:owned (Types.cpp_of_core cx env ty) in
                 ((cpp_ty, Some id), (id, mode)) )
               args owned_flags )
        in
        let fwd_args =
          List.map2
            (fun (id, ty) (_, mode) -> forwarded ~by_value:(Cpp_ir.Param_mode.holds_own_value mode) ty (Local id))
            args modes
          @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call : Cpp_ir.Lowered.Expr.t =
          Call (Cpp_ir.Build.signature ~nargs:0 (), Local _impl_id, List.rev fwd_args) in
        let wrapper_body : Cpp_ir.Lowered.Stmt.t list =
          match rty with
          | None -> [Expression call]
          | _ -> [Return (Some call)]
        in
        Bind_variable
          ( fix_id,
            Declare (Auto, None),
            Lambda
              { params = List.rev orig_params;
              type_params = [];
              fixpoint = local_fixpoint ~name:fix_id ~encoding:Knot binder;
              binders = fixpoint_parameters binder;
              modes;
              moved = [];
                return_type = rty;
                body = wrapper_body;
                capture = Runs_in_place } ))
      (List.combine (List.combine (List.combine renamed_ids impl_ids) binders) owned_flags_per_fun)
      funs_with_params
  in
  let self_passing () = impl_stmts @ wrapper_stmts in
  (local_fix_stmts cx selves ~binders ~self_passing impl_stmts funs_with_params, [])

(** How the lambda of each function of the local fixpoint [fix] holds each
   variable it captures, generated as closures or else [in_place]
   ({!Ownership_ir.Region.captures_by_member}). *)
let fix_captures cx ~in_place fix = Ownership_ir.Region.captures_by_member ~in_place cx.ctx.lexical.move_plan fix

(** Report, under [CRANE_CHECK_IR], a let-bound lambda [what] that reached
    translation other than as it is generated: Core puts every one so
    before ({!Core_plan.Normalize.let_lambdas}), and translation only binds or lifts
    them. *)
let ungenerated_let_lambda what =
  if Base.Probe.checking () then
    Base.Probe.violation "let-bound lambda" Pp.(str "Core_passes.Phase.normalize left " ++ str what ++ str " to translation")

(** Under [CRANE_CHECK_IR], the region's plan must have decided as translation
    does whether [let _ : ty := a] binds the closure [a] to a local
    ([local]), which the plan owns and moves; a violation otherwise. *)
let check_closure_local cx ty a ~local =
  if Base.Probe.checking () then
    match Ownership_ir.Region.closure_local cx.ctx.lexical.move_plan ty a with
    | Some planned when planned <> local ->
      Base.Probe.violation "ownership plan"
        (Pp.str
           (Printf.sprintf "a let-bound closure the plan takes for %s is generated as %s"
              (if planned then "a local" else "no local")
              (if local then "a local" else "no local") ) )
    | _ -> ()

(** Under [CRANE_CHECK_IR], the local fixpoint [name], whose group Core takes
   to hold copies where [closures] says so ({!Core_plan.Closures}), must be
   one its generated code lets escape just as much: named, after its binding
   or in its own bodies, other than as the function a call applies, or
   inside a closure. *)
let check_fixpoint_escape name ~closures generated_escapes =
  if Base.Probe.checking () && closures <> generated_escapes () then
    Base.Probe.violation "closure escape"
      Pp.(
        str "the local fixpoint " ++ Id.print name
        ++ str
             ( if closures then " escapes in Core but nowhere in its generated code"
               else " escapes in its generated code but nowhere in Core" ) )

(** The helper [r] lifted out of a body: the function returning [ret] that

   takes [params], last first as {!Lifting.build_lifted_cpp_params} gives them,
   passed as [modes] says,
   standing for the Core binders [binders], with body [body], under the
   template parameters [tparams]. *)
let lifted_definition ~binders ~modes ~ret r params body tparams : Cpp_ir.Lowered.Decl.t =
  Template
    ( tparams,
      None,
      Function
        { path = {outer = (r, []); inner = []};
          return_type = ret;
          no_pure = false;
          constexpr = Undecided;
          shape = Definition (List.rev params, body);
          binders;
          modes;
          loop = None } )

(** Lower the body of member [fix_idx] of a fixpoint group, the member
    [(n, ty)] with lambda [f], under the group's names [all_fix_ids] (array
    order; empty for a single fixpoint, which is then [(n, ty)] alone).
    Returns the member's renamed name and type, its runtime parameters, its
    lowered body statements and its parameters' Core binders.  [by_value]:
    every parameter is owned (the group holds copies); [local] or [lifted]
    names the occurrence or the helper whose machine plans the frames the
    body saves. *)
let gen_fix cx ~ret env ?(all_fix_ids = []) ?(by_value = false) ?local ?lifted ~fix_idx (n, ty) f =
  let ids, f = collect_lams f in
  let ids = List.map (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty)) ids in
  (* Push all mutual fixpoint names (or just (n,ty) for single fixpoints). For
     mutual fixpoints, all_fix_ids contains all fixpoint names in array order.
     For single fixpoints, all_fix_ids is empty and we use [(n,ty)].

     IMPORTANT: Rocq's extraction pushes fix bindings so that the LAST function
     is at db 1 and the FIRST is at db n (standard de Bruijn convention with
     fold_left over the array). We must reverse fix_names to match. *)
  let fix_names = if all_fix_ids = [] then [(n, ty)] else all_fix_ids in
  let n_fix_funs = List.length fix_names in
  let fix_names_db_order = List.rev fix_names in
  let renamed_fix_ids, env = push_vars' (ids @ fix_names_db_order) env in
  let saved_env_types = cx.ctx.lexical.env_types in
  Binders.push_binders cx env renamed_fix_ids;
  (* Extract the renamed name for THIS fixpoint function. fix_names_db_order
     is reversed from the array order, so fix array index i corresponds to
     position (n_fix_funs - 1 - i) in the reversed list. *)
  let n_lam_params = List.length ids in
  (* The parameters as the body names them: renamed together with the
     fixpoints, which may take a parameter's name first. *)
  let binders = safe_firstn n_lam_params renamed_fix_ids in
  let renamed_n =
    fst (List.nth renamed_fix_ids
           (n_lam_params + (n_fix_funs - 1 - fix_idx))) in
  let ids = List.filter (fun (_, ty) -> not (void_binder ty)) binders in
  (* The parameters the body owns, passed by value in the generated lambda.
     After push_vars'(binders @ fix_names), binders[0] is db 1, ...,
     binders[k-1] db k -- a binder of no runtime value, which the lambda
     does not take, among them -- and the fixpoints follow; only parameters
     of a runtime value are owned.  A function whose lambda takes every
     parameter by value ([by_value]: its group's plan owns each,
     {!local_passing}) owns each: it holds its own copy. *)
  let n_total = n_lam_params + n_fix_funs in
  let fix_owned_base = Core_plan.Escape.infer_owned_params ~callee_flags:(settled_ownership cx) n_total f in
  let fix_sub_esc = Core_plan.Escape.infer_sub_bindings_escape_params n_total f in
  let owned_params =
    Ownership.owned_parameters n_lam_params
      ~owned:(fun i ->
        let flag l = Option.default false (List.nth_opt l i) in
        let ty = snd (List.nth binders i) in
        (not (void_binder ty)) && (by_value || flag fix_owned_base || (flag fix_sub_esc && is_prod_core_type ty)) )
      ~ty:(fun i -> snd (List.nth binders i))
  in
  (* The body returns the fixpoint's own codomain, not the enclosing
     function's: a result recovered from a box inside it is recovered at
     the [T1] a [fix F (m : list A) : P A m] returns, not at the pair the
     function around it builds from two calls.  A unit codomain is [void],
     as the lambda's signature, read off the fixpoint's function type,
     declares it ({!Types.result_is_void}), so the body's [return]s agree
     with it. *)
  let fix_return_type =
    let n_values = List.length (List.filter (fun (_, t) -> not (erased_by_extraction t)) ids) in
    match core_codomain_after n_values ty with
    | Some cod ->
      let t = Types.cpp_of_core cx env cod in
      let returns_nothing =
        n_values > 0 && (match t with Function _ -> false | _ -> Types.result_is_void cod t)
      in
      if returns_nothing then Some Cpp_ir.Type.Void
      else if not (Cpp_ir.Types.exists Cpp_ir.Types.prints_as_any t) then Some t
      else ret
    | None -> ret
  in
  (* The local fixpoint at [local], of one member, lowered as a machine with
     a stack of frames ({!local_fix_stmts}, or as the entry of the machine
     adopting it), or the helper [lifted] for it, lowered so, has the frames
     it saves planned with its body. *)
  let resumes, certain =
    match (local, lifted) with
    | Some occ, _ when n_fix_funs = 1 -> (
      match
        Control_to_cpp.Lower.local_resumes ~unit:(Lowering_state.unit_context cx) ~owner:cx.ctx.input.body_owner
          ~all_locals:cx.ctx.input.body_all_locals
          ~lifted:cx.ctx.lexical.lifted_fixpoints ~member:(occ, fix_idx)
            ~depth:(List.length (fst env)) ~arity:n_lam_params
      with
      | Some (resumes, certain) -> (Some resumes, Some certain)
      | None -> (None, None) )
    | _, Some r when n_fix_funs = 1 ->
      ( Control_to_cpp.Lower.lifted_resumes ~unit:(Lowering_state.unit_context cx) r ~owner:cx.ctx.input.body_owner
          ~depth:(List.length (fst env))
          ~arity:n_lam_params,
        None )
    | _ -> (None, None)
  in
  let return_ = Destination.return_at fix_return_type in
  let result =
    ( (renamed_n, ty),
      ids,
      with_region cx ~ret:fix_return_type ~owned:owned_params ?resumes ?certain f
        (fun () -> gen_stmts cx (Slot.at ~ret:fix_return_type ()) env return_ f),
      parameter_binders cx env ids )
  in
  restore_env_types cx saved_env_types;
  result

(** [let] bound to a local fixpoint [fix_term], then [b], ending in [k]:
    the fixpoint lifted as template helpers where it has type variables of
    its own, otherwise declared in place, as a loop, a by-reference group or
    a Y-combinator closure. *)
let gen_let_fix cx ~ret ~slot env (k : Destination.t) ~let_ty ~x ~ids ~funs ~occ
  ~fix_term ~b
  ~let_occ : Cpp_ir.Lowered.Stmt.t list =
  (* Special case for let-fix: the let binding name is the fix function name *)
  Core_passes.Local_types.check_minted ids;
  let ids, funs = Core_passes.Local_types.recover_fix_codomains (Calls.local_types_lowering cx) ids funs in
  register_erased_members ~let_ty occ ids;
  (* Collect all Core.Type.Variable indices from the fixpoint types *)
  let fix_tvar_indices =
    Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
  in
  let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
  let outer_tvars = get_current_type_vars cx in
  let n_outer = List.length outer_tvars in
  let has_extra_tvars = Base.Type_util.own_type_variables ~n_outer (List.map snd (Array.to_list ids)) in
  check_closure_local cx let_ty fix_term ~local:(not has_extra_tvars);
  if has_extra_tvars then (
    (* Lift the polymorphic inner fixpoint to a top-level function. Build tvar
       names for all Tvars used in the fixpoint type: - Tvars 1..n_outer reuse
       the outer function's template param names - Tvars beyond n_outer get
       fresh names T<i> *)
    let fix_tvar_indices = Lifting.lifted_indices ~n_outer fix_tvar_indices in
    let all_tvar_names = Lifting.build_tvar_names ~outer_tvars fix_tvar_indices in
    let all_temps = Cpp_ir.Build.typenames all_tvar_names in
    (* The body being lifted was written against the enclosing declaration's
       class instances -- it spells [typename _tcI0::PTR::ptr] -- and a
       concept-constrained parameter is not a Core type variable, so
       [fix_tvar_indices] cannot mention one.  Carry the head's own
       instances over, ahead of the type variables and explicit at every
       reference: nothing deduces a class instance from an argument. *)
    let class_temps = current_class_temps cx in
    let class_args = List.map (fun (_, id) -> Cpp_ir.Build.named_variable id) class_temps in
    (* A lifted fix no longer sits inside the scope that bound its free
       variables, so each one becomes a trailing parameter and each call
       grows an argument -- the same closure conversion the lifted-lambda
       path below does.  The names are the outer scope's, so the compiled
       body needs no substitution: only the head and the call sites do. *)
    let free_vars =
      Lifting.lifted_free_vars cx ~class_temps env (Lifting.collect_free_rels 0 fix_term)
    in
    let free_args = List.map (fun (name, _, _) : Cpp_ir.Lowered.Expr.t -> Local name) free_vars in
    (* Generate the lifted function name *)
    let fix_name = fst ids.(x) in
    let member_refs = Lifting.lifted_member_refs occ ids in
    let lifted_ref = member_refs.(x) in
    (* Generate the fixpoint body using gen_fix, under the lifted function's
       own tvar scope, passing all mutual fixpoint names *)
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled =
      with_lifted_fixpoint cx occ @@ fun () ->
      with_type_vars cx all_tvar_names (fun () ->
          Array.to_list
            (Array.mapi
               (fun i f ->
                 gen_fix cx ~ret env ~all_fix_ids:all_fix_ids_list ~lifted:member_refs.(i) ~fix_idx:i ids.(i)
                   f )
               funs ) )
    in
    let renamed = List.map (fun ((id, _), _, _, _) -> id) funs_compiled in
    (* The helpers return their codomains as their templates spell them; only
       an erased one is a box. *)
    let concrete = Lifting.concrete_results (Types.cpp_ir_of_core_type cx env all_tvar_names) ids in
    (* Build a lifted definition for each fixpoint function (usually just one) *)
    let ungeneralised = Callable_params.lifted_fix_ungeneralised_params funs in
    List.iteri
      (fun i ((_, fix_ty), params, body, param_binders) ->
        let cpp_ty = Types.cpp_ir_of_core_type cx env all_tvar_names fix_ty in
        let cod = match cpp_ty with Function (_, cod) -> cod | _ -> cpp_ty in
        (* The callables a recursive call would instantiate the helper at
           without end take a [crane::fn]. *)
        let non_fwd_source_indices = ungeneralised.(i) in
        let cpp_params, modes, all_temps_with_funs =
          Lifting.build_lifted_cpp_params
            ~non_fwd_source_indices
            (Types.cpp_ir_of_core_type cx env all_tvar_names)
            all_temps
            (List.map (fun (n, t, _) -> (n, t)) free_vars @ params)
        in
        (* Replace references to the group's members with calls to the
           lifted functions *)
        let body =
          Lifting.subst_lifted_members ~extra_args:(List.rev free_args) ~concrete renamed member_refs
            (class_args @ List.map (fun id -> Cpp_ir.Build.named_variable id) all_tvar_names)
            body
        in
        (* The captured variables are the enclosing body's binders. *)
        let binders =
          parameter_binders cx env (List.map (fun (n, t, _) -> (n, t)) free_vars) @ param_binders
        in
        let lifted_decl =
          lifted_definition ~binders ~modes ~ret:cod member_refs.(i) cpp_params body (class_temps @ all_temps_with_funs)
        in
        add_lifted_decl cx (Control_to_cpp.Lower.lower_lifted ~unit:(Lowering_state.unit_context cx) lifted_decl) )
      funs_compiled;
    (* In the continuation body b, the fixpoint name should resolve to a call
       to the lifted function with appropriate type arguments. We push the fix
       name into the env so that Core.Expr.Bound_variable references in b resolve correctly. *)
    let projected_fix_id = (fst ids.(x), snd ids.(x)) in
    let _, env_with_fix = push_vars' [projected_fix_id] env in
    Binders.push_binders cx env [projected_fix_id];
    (* Generate b, then replace references to the fixpoint var with calls to
       the lifted function. Build explicit type args: outer tvars stay as Core.Type.Variable
       references, extra tvars are resolved to concrete types from the
       enclosing function's return type. *)
    let call_type_args =
      Calls.lifted_call_type_args cx ~ret ~class_args ~env ~outer_tvars
           ~head:(List.map snd all_temps) ~all_tvar_names ~binder_ty:(snd ids.(0))
           ~param_core_tys:
             ( match List.nth_opt funs_compiled x with
             | Some (_, params, _, _) -> List.map snd params
             | None -> [] )
    in
    let lifted_call = mk_cppglob lifted_ref call_type_args in
    let result = gen_stmts cx (Slot.at ~ret ~slot ()) env_with_fix k b in
    let extra_args = List.rev free_args in
    (* The helper returns its codomain as the template spells it; only an
       erased one is a box. *)
    List.map (fun st -> Lifting.local_var_subst_stmt ~concrete_result:concrete.(x) ~extra_args fix_name lifted_call st)
      result )
  else
    (* No extra type variables: proceed with local fixpoint approach.

       Three sub-steps:
       1. Compile all mutual fixpoint bodies via {!gen_fix}.
       2. Push only the PROJECTED fixpoint (the one this [Core.Expr.Let]
          binds) into the continuation environment — not all mutual
          fix names, which would shift de Bruijn indices by [n]
          instead of the correct [1].
       3. Generate the group by reference ({!gen_local_fix_by_ref}) or as
          closures holding copies ({!gen_local_fix_ycomb}), as Core decides
          whether a member escapes ({!Core_plan.Closures}).

       The variables the fixpoint bodies capture are not moved in the
       continuation while a [\[&\]] lambda may still refer to them: the
       plan pins them ({!Ownership_ir.Region}). *)
    let all_fix_ids_list = Array.to_list ids in
    (* A group a frame keeps across a resume is stored in the frame and
       called once the frame resumes, after the scope it would read by
       reference has ended: one capturing anything holds copies, though
       Core never lets it escape. *)
    let kept_by_frame =
      List.exists (( <> ) []) (fix_captures cx ~in_place:true fix_term)
      &&
      match core_binder cx ~site:(Binding let_occ) env 0 with
      | Some b -> Ownership_ir.Region.kept_by_frame cx.ctx.lexical.move_plan b
      | None -> false
    in
    let cofix = match fix_term with Core.Expr.Cofixpoint _ -> true | _ -> false in
    let closures =
      kept_by_frame
      || closures_group cx ~n_outer ~occ
           ~continuation:(x, (Core.Binder_name.Source (fst ids.(x)), let_ty), b)
           ~cofix ids funs
         = Closures
    in
    let funs_compiled =
      Array.to_list
        (Array.mapi
           (fun i f ->
             gen_fix cx ~ret env ~all_fix_ids:all_fix_ids_list ~by_value:closures ~local:occ ~fix_idx:i ids.(i) f )
           funs )
    in
    let renamed_ids =
      List.map (fun (renamed_id, _, _, _) -> renamed_id) funs_compiled
    in
    let funs_with_params =
      List.map (fun (_, params, body, _) -> (params, body)) funs_compiled
    in
    (* Add only the PROJECTED fixpoint id to the continuation env.
       Core.Expr.Let binds ONE variable (the projected fixpoint), not all mutual
       fix functions.  Pushing all fix names would shift de Bruijn indices
       by n instead of 1, corrupting references in the continuation.
       However, ALL fix names are added to the avoid set to prevent
       name clashes in subsequent fixpoints (e.g., when the same mutual
       block is instantiated again with a different projection). *)
    let projected_id = List.nth renamed_ids x in
    (* Add non-projected fix names to the avoid set so that subsequent
       fixpoints (e.g., a second Core.Expr.Fixpoint with a different projection from
       the same mutual block) will rename conflicting names. *)
    let env_for_cont =
      let (db, avoid) = env in
      let avoid' = List.fold_left
        (fun acc (i, (id, _)) ->
          if i <> x then Id.Set.add id acc else acc)
        avoid (List.mapi (fun i x -> (i, x)) renamed_ids)
      in
      (db, avoid')
    in
    let _, env_with_fix = push_vars' [projected_id] env_for_cont in
    Binders.push_binders cx env [projected_id];
    let declared = declaring (fst projected_id) (core_binder cx ~site:(Binding let_occ) env_with_fix 1) in
    let cont = gen_stmts cx (Slot.at ~ret ~slot ()) env_with_fix k b in
    let suspended = in_suspended_tail cx occ in
    check_fixpoint_escape (fst projected_id) ~closures:(closures && not kept_by_frame) (fun () ->
        (not kept_by_frame)
        && ( List.exists
               (fun (id, _) ->
                 Lifting.fixpoint_escapes_in_stmts id cont
                 || (suspended && Lifting.fixpoint_named_in_returns id cont) )
               renamed_ids
           || Lifting.fix_escapes_in_own_bodies renamed_ids funs_with_params ) );
    let passing = local_passing cx ~closures funs in
    if closures then
      let decls, defs, deref_subst =
        gen_local_fix_ycomb cx env ~binders:(local_fix_binders cx env fix_term occ ids funs_compiled) ~passing
          ~captures:(fix_captures cx ~in_place:false fix_term)
          renamed_ids funs_with_params
      in
      declared (decls @ defs) @ deref_subst cont
    else
      let decls, defs =
        gen_local_fix_by_ref cx env ~binders:(local_fix_binders cx env fix_term occ ids funs_compiled) ~passing
          ~captures:(fix_captures cx ~in_place:true fix_term) renamed_ids funs_with_params
      in
      declared (decls @ defs) @ cont

(** [let x = a in b] with [a] a lambda, ending in [k]: a polymorphic lambda
    lifted out of the body as a helper, the others bound as closures. *)
let gen_let_lambda cx ~ret ~slot env (k : Destination.t) ~x ~t ~a ~b ~let_occ :
  Cpp_ir.Lowered.Stmt.t list =
  (* Check if this is a polymorphic lambda that should be lifted to a
     top-level template function. *)
  let outer_tvars = get_current_type_vars cx in
  let n_outer = List.length outer_tvars in
  (* A type the binding leaves open is the binding's own, minted before
     the program was frozen past the enclosing declaration's variables,
     which [Core.Type.Variable 1] .. [Core.Type.Variable n_outer] already name. *)
  Core_passes.Local_types.check_let_lambda ~outer:n_outer t a;
  (* Collect all Core.Type.Variable indices from the let-binding type *)
  let tvar_indices = collect_tvars [] t in
  (* Also collect Tvars from the lambda body *)
  let body_tvars = Lifting.collect_tvars_ast [] a in
  let all_body_tvars = List.sort_uniq Int.compare body_tvars in
  let tvar_indices = List.sort Int.compare tvar_indices in
  (* The body being lifted was written against the enclosing
     declaration's class instances -- it spells [typename
     _tcI0::PTR::ptr] -- and a concept-constrained parameter is not an
     Core type variable, so [tvar_indices] cannot mention one.  The lifted
     head carries the instances over, ahead of the type variables and
     explicit at every reference: nothing deduces a class instance.  An
     instance constrained over an enclosing variable, [requires Sz<_tcI0,
     T1>], takes that variable along, though the binding's type may not
     mention it. *)
  let class_temps = current_class_temps cx in
  let class_args = List.map (fun (_, id) -> Cpp_ir.Build.named_variable id) class_temps in
  let tvar_indices =
    List.sort_uniq Int.compare (Lifting.class_constraint_tvars ~outer_tvars class_temps @ tvar_indices)
  in
  (* Normal Core.Expr.Let fallback (shared by no-extra-tvars and
     thunk-with-free-vars cases) *)
  let gen_normal_letin () =
    let a =
      let expanded = eta_bound_lambda t a in
      if expanded != a then ungenerated_let_lambda "a lambda bound as a value short of its type's arrows";
      expanded
    in
    let x' = cpp_id_of_id (id_of_binder_name x) in
    let renamed_ids, env' = push_vars' [(x', t)] env in
    let x_renamed = fst (List.hd renamed_ids) in
    if x == Core.Binder_name.Anonymous then (
      Binders.push_binders cx env [(x_renamed, t)];
      gen_stmts cx (Slot.at ~ret ~slot ()) env' k b )
    else if cx.ctx.input.itree_mode = Reified && is_monadic_core_type t then begin
      (* Monadic let-binding (reified mode): wrap RHS in an ITree IIFE so
         the variable has type [shared_ptr<ITree<R>>]. *)
      Binders.push_binders cx env [(x_renamed, t)];
      let r_core = Monadic.extract_itree_result_core t in
      let r_cpp = Types.cpp_of_core cx env r_core in

      let reified_ty = Monadic.mk_itree_type r_cpp in
      let ret_k =
        Destination.Custom
          { build = (fun v -> Return (Some (Monadic.mk_itree_ret_for_value r_cpp r_core v)));
            into = Exactly r_cpp;
            returns = true }
      in
      let body_stmts = gen_stmts cx (Slot.at ~ret ()) env ret_k a in
      let iife = Cpp_ir.Build.iife (Some reified_ty) body_stmts in
      (* Shift owned vars for the continuation *)
      let cont =
        gen_stmts cx (Slot.at ~ret ~slot ()) env' k b
      in
      (* Generate the assignment with reified type *)
      [(Bind_variable (x_renamed, Declare (reified_ty, core_binder cx ~site:(Binding let_occ) env' 1), iife) :
          Cpp_ir.Lowered.Stmt.t)] @ cont
    end else
      (* The lambda's slot is its binder's, not the position the let stands
         in: [cf] in [w := let cf := fun _ : tree => 1 in fun c => cf Leaf]
         takes a [tree], whatever [w] takes.  Only a signature the position
         states is replaced: the result any other position falls back to is
         what a let in the lambda's body falls back to as well
         ({!Destination.bind_let}).  A position stating its signature
         through an alias, [st nat] for [nat -> nat * nat], states one all
         the same: {!Lambda.gen_lambda} unfolds it, and would write the
         binding's lambda to return the pair. *)
      let afun = Destination.bind_let cx env x_renamed t in
      let asgn =
        match Option.map (Types.unfold_cpp_typedef cx env) ret with
        | Some (Function _) -> gen_stmts cx (Slot.at ~ret:(Destination.stated afun) ()) env afun a
        (* [ret] is left for the right-hand side's legacy readers; the
           destination is the binder's. *)
        | _ -> gen_stmts cx (Slot.at ~ret ()) env afun a
      in
      (* When the RHS was a pair accessor on an erased argument (e.g.
         snd vs where vs : std::any), the result is std::any at runtime
         even though the Core type says prod(...).  Override to Core.Type.Erased so
         downstream pair accessor calls (fst tail) detect erasure. *)
      let t_for_env =
        if Erasure.stmts_yield_boxed asgn then Core.Type.Erased Core.Erasure_reason.Type_argument else t
      in
      (* Push env_types AFTER generating the value expression [a]. *)
      Binders.push_binders cx env [(x_renamed, t_for_env)];
      let gen_cont () = gen_stmts cx (Slot.at ~ret ~slot ()) env' k b in
      match asgn with
      | [Bind_variable (_, Existing, e)] ->
        Bind_variable
          ( x_renamed,
            Declare (Types.cpp_of_core cx env t, core_binder cx ~site:(Binding let_occ) env' 1),
            e )
        :: gen_cont ()
      | _ ->
        (Declare (x_renamed, Types.cpp_of_core cx env t, core_binder cx ~site:(Binding let_occ) env' 1)
          : Cpp_ir.Lowered.Stmt.t)
        :: asgn
        @ gen_cont ()
  in
  let decision = let_lambda ~lex:(current_lexenv cx ()) ~n_outer t a b in
  check_closure_local cx t a ~local:(match decision with Bound -> true | _ -> false);
  (match decision with
  | Bound -> gen_normal_letin ()
  | At_instance inst ->
    let subst = Base.Core_util.type_subst_list inst in
    ungenerated_let_lambda "a lambda used at one instance";
    with_plan cx (Ownership_ir.Region.bound_at_instance cx.ctx.lexical.move_plan ~let_:let_occ) (fun () ->
        gen_stmts cx (Slot.at ~ret ~slot ()) env k (Core.Expr.Let {binder = x;
                                              binder_type = subst t;
                                              value = Base.Core_util.ast_map_types subst a;
                                              body = b;
                                              occurrence = let_occ}) )
  | Inlined b ->
    ungenerated_let_lambda "an alias to inline";
    gen_stmts cx (Slot.at ~ret ~slot ()) env k b
  | Lifted ->
    (* Lift the polymorphic lambda to a top-level template function. *)
    let params, body = collect_lams a in
    let n_params = List.length params in
    let x' = cpp_id_of_id (id_of_binder_name x) in

    (* 1. Collect free variables in the lambda body *)
    let free_indices = List.sort Int.compare (Lifting.collect_free_rels n_params body) in

    (* 2. Build tvar names: outer tvars keep their names, extra tvars get
       fresh names.  In the template head, the extras a call cannot
       deduce -- named by the result alone, like [A] in [fun (A : Type) x
       => @Tag A 1] -- go first: explicit type arguments are positional,
       so the deducible ones then form the trailing run a call leaves
       out. *)
    let all_tvar_names = Lifting.build_tvar_names ~outer_tvars tvar_indices in
    let all_temps =
      let deducible =
        List.fold_left
          (fun acc (_, ty) -> if erased_by_extraction ty then acc else collect_tvars_set acc ty)
          IntSet.empty params
      in
      let outer, extra =
        List.partition (fun (i, _) -> i <= n_outer) (List.combine tvar_indices all_tvar_names)
      in
      let fixed, deduced = List.partition (fun (i, _) -> not (IntSet.mem i deducible)) extra in
      Cpp_ir.Build.typenames (List.map snd (outer @ fixed @ deduced))
    in
    let free_vars = Lifting.lifted_free_vars cx ~class_temps env free_indices in

    let extended_tvar_names =
      Lifting.build_extended_tvar_names tvar_indices all_tvar_names all_body_tvars
    in

    (* 3. Generate the lifted function name *)
    let lifted_ref = Lifting.lifted_ref (Base.Lifted.Let let_occ) x' in

    (* 4. Substitution helper for call sites: replace a call [Call (_, Local
       x', args)] with a call of [Entity (lifted_ref, [])] on
       [free_var_cpps @ args]. *)
    (* The lifted function is a template over the binder's type
       arguments, so a parameter declared at one of them is a template
       parameter C++ has to deduce.  A closure has no name to deduce, and
       so cannot agree with the same parameter as settled by another
       argument; {!Coerce.name_fn_arg_plan} names it. *)
    (* {!Base.Core_util.collect_lams} hands the binders back innermost-first, so
       the source order these are read in is the reverse of [params]. *)
    let param_core_tys =
      List.rev
        (List.filter_map
           (fun (_, ty) ->
             if is_runtime_binder_type ty then Some ty else None )
           params )
    in
    let n_actual_params = List.length param_core_tys in
    (* [args] in source order, as [param_core_tys] is. *)
    let name_lifted_args args =
      List.mapi
        (fun i a ->
          match List.nth_opt param_core_tys i with
          | Some ty -> Coerce.into_slot ~origin:(Tvar_name ty) (Cpp_ir.Typed.of_node a) (Template_parameter None)
          | None -> a )
        args
    in
    let opaque () = Cpp_ir.Build.signature ~nargs:0 () in
    (* The lifted function's own type: the lambda's parameters, one group,
       then what its body returns. *)
    let lifted_type : Cpp_ir.Lowered.Type.t =
      Function
        ( List.map (Types.cpp_of_core cx env) param_core_tys,
          Types.codomain_after cx env n_actual_params t )
    in
    let rec subst_lifted_call_expr
        (target : Id.t)
        (lifted : Cpp_ir.Lowered.Expr.t)
        (free_args : Cpp_ir.Lowered.Expr.t list)
        (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
      let sub = subst_lifted_call_expr target lifted free_args in
      match e with
      | Call (_, Local id, args) when Id.equal id target ->
        (* The lifted template's parameters come from the lambda, so its
           arity is the lambda's. *)
        (Cpp_ir.Typed.apply
           ~first:(fun here -> Call (opaque (), lifted, List.rev (free_args @ List.rev (name_lifted_args here))))
           (Cpp_ir.Typed.typed lifted_type lifted)
           (List.map (fun a -> Cpp_ir.Typed.of_node (sub a)) args) )
          .expr
      | Local id when Id.equal id target ->
        (* Bare reference to lifted function: generate a properly-typed
           wrapper lambda with one parameter per non-erased Rocq lambda
           param. Capture by value ([=]) so that free variables don't
           dangle when the wrapper outlives the current stack frame. *)
        if free_args = [] && n_actual_params = 0 then
          lifted
        else
          let fresh_ids =
            List.init n_actual_params (fun i ->
              Id.of_string (Printf.sprintf "_xarg%d" i))
          in
          let wrapper_params =
            List.map (fun id : (Cpp_ir.Lowered.Type.t * Id.t option) -> (Auto, Some id)) fresh_ids
          in
          let wrapper_call_args =
            free_args @ List.map (fun id : Cpp_ir.Lowered.Expr.t -> Local id) fresh_ids
          in
          Lambda
            { params = List.rev wrapper_params;
              type_params = [];
              binders = [];
              modes = [];
              fixpoint = None;
              moved = [];
              return_type = None;
              body =
                [ Return
                    (Some
                       (Call
                          ( opaque (), lifted,
                            List.rev wrapper_call_args ) ) ) ];
              capture = Stored }
      | Coerce _ when (match Cpp_ir.Typed.head e with Any_cast _ -> true | _ -> false) ->
        subst_lifted_call_expr target lifted free_args (Cpp_ir.Typed.head e)
      | Any_cast (_, Call (_, Local id, args))
        when Id.equal id target ->
        (* The any_cast wraps a direct call to the variable being lifted.
           The lifted template function returns a concrete type (not
           std::any), so drop the cast and replace with the lifted call. *)
        Call
          (opaque (),
            lifted,
            List.rev (free_args @ List.map sub (List.rev args)) )
      | Any_cast (ty, e') -> Cpp_passes.Erasure.unbox ty (sub e')
      | _ ->
        (* Every other form is a plain structural descent.  Spelling the
           cases out by hand is what let uses of [target] under an [if] or
           a [switch] escape rewriting. *)
        Cpp_ir.Map.expr (subst_lifted_call_map target lifted free_args) e
    and subst_lifted_call_stmt
        (target : Id.t)
        (lifted : Cpp_ir.Lowered.Expr.t)
        (free_args : Cpp_ir.Lowered.Expr.t list)
        (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
      Cpp_ir.Map.stmt (subst_lifted_call_map target lifted free_args) s
    and subst_lifted_call_map target lifted free_args : Cpp_ir.Lowered.phase Cpp_ir.Map.t =
      Cpp_ir.Map.make
        ~expr:(subst_lifted_call_expr target lifted free_args)
        ~stmt:(subst_lifted_call_stmt target lifted free_args)
        ~type_:Fun.id ()
    in

    (* 6. Compile the lambda body under the extended type-variable
       scope, which numbers the body's Tvars the way the lifted
       function's signature will. *)
    let free_var_params, lam_param_ids, lam_env, compiled_body =
      with_type_vars cx extended_tvar_names (fun () ->
          (* Push lambda params into env for body compilation *)
          let param_ids =
            List.map
              (fun (core_id, ty) -> (cpp_id_of_id (id_of_binder_name core_id), ty))
              params
          in
          (* For free variables, we need to adjust de Bruijn indices in the body.
             The body references free vars as Core.Expr.Bound_variable (n_params + i) where i is the
             outer index. We compile with an env that has: [free_var_params...;
             lambda_params...] So we push free var names first, then lambda param
             names. *)
          let free_var_params =
            List.map (fun (name, ty, _) -> (name, ty)) free_vars
          in
          let body_params_for_env = free_var_params @ param_ids in
          let body_param_ids, body_env = push_vars' body_params_for_env env in
          let saved_env_types = cx.ctx.lexical.env_types in
          Binders.push_binders cx env body_param_ids;

          (* Now compile the body. The body's de Bruijn indices: Core.Expr.Bound_variable 1..n_params
             -> lambda params (at positions n_free+1..n_free+n_params in our env)
             Core.Expr.Bound_variable n_params+i -> free var i (should map to position n_free-i+1 in
             our env, but we actually need to adjust: Core.Expr.Bound_variable (n_params +
             orig_outer_idx) in the body maps to outer env position
             orig_outer_idx. In our extended env, free vars are at positions
             n_params+1..n_params+n_free. So we need to remap. Actually, the body
             already has correct de Bruijn indices: - Core.Expr.Bound_variable 1..n_params are the
             lambda params - Core.Expr.Bound_variable (n_params + i) references outer scope position
             i When we push [free_var_params @ param_ids], the env has: positions
             1..n_params = param_ids (lambda params) positions
             n_params+1..n_params+n_free = free_var_params But the body references
             Core.Expr.Bound_variable(n_params + original_outer_idx), and original_outer_idx may not
             equal the position in free_var_params. We need the body env to map
             Core.Expr.Bound_variable(n_params + i) correctly for each free var. *)

          (* Simpler approach: compile body in a modified env where free vars at
             their original positions are accessible. We push only the lambda
             params on top of the outer env. *)
          let lam_param_ids, lam_env = push_vars' param_ids env in
          restore_env_types cx saved_env_types;
          Binders.push_binders cx env lam_param_ids;
          (* The helper is a function of its own: its return type is not
             the enclosing one's, and nothing in it is owned -- every
             parameter, captured or not, is declared const by
             {!Lifting.build_lifted_cpp_params}.  The enclosing ownership would
             not even name the same variables, being indexed from outside
             the lambda's binders. *)
          let compiled_body =
            with_escape_analysis cx ~ret (fun ret -> with_region cx ~ret body (fun () ->
                gen_stmts cx (Slot.at ~ret ()) lam_env (Destination.Return Join) body ) )
          in
          restore_env_types cx saved_env_types;
          (free_var_params, lam_param_ids, lam_env, compiled_body) )
    in

    (* 7. Now substitute free variable references in compiled body: Free
       vars in the body were compiled as [Local name_from_outer_env]. In the

       lifted function, they become parameters. The names are the same, so
       no substitution of the body is needed — the free var params have the
       same names as the outer scope variables. *)

    (* 8. Build the lifted function parameters: free vars first, then lambda
       params *)
    let all_lifted_params =
      free_var_params
      @ List.filter
          (fun (_, ty) -> is_runtime_binder_type ty)
          lam_param_ids
    in
    let cpp_params, modes, all_temps_with_funs =
      Lifting.build_lifted_cpp_params
        (Types.cpp_ir_of_core_type cx lam_env extended_tvar_names)
        all_temps all_lifted_params
    in

    (* Get return type from the let-binding type *)
    let cpp_ty = Types.cpp_ir_of_core_type cx lam_env extended_tvar_names t in
    let cod =
      (* [collect_lams] stops at the first non-lambda, so a let-bound
         [fix] keeps its own binders: the helper takes fewer parameters
         than its type has domains, and what it returns is the closure
         standing for the rest.  A closure type has no spelling, and
         [auto] is how C++ declines to give it one.

         The comparison has to be against the domains that actually took
         a parameter, not the raw arrow count: a domain extraction erased
         (a quantified [Type], a proof) never became one of [params]
         either, so counting it here made an ordinary, fully-applied
         helper with an erased argument -- [fun {A} (x : A) (_ : True) =>
         x], one real binder, two erased ones -- look exactly like a
         curried leftover, and its return type, which is nameable (the
         same [T1] its parameter already spells), fell back to [auto].
         An [auto]-returning template with more than one instantiation in
         the same translation unit is then used before any of them is
         defined. *)
      let core_dom, _ = Base.Core_util.type_decomp t in
      let value_dom =
        List.filter is_runtime_binder_type core_dom
      in
      if List.length value_dom > n_params then (Auto : Cpp_ir.Lowered.Type.t)
      else
        match cpp_ty with
        | Function (_, cod) -> cod
        | _ -> cpp_ty
    in

    (* 9. Build and register the lifted declaration.  Call sites below
       name the class prefix and nothing else, so a type parameter whose
       only occurrence is a returned lambda's binder can move into that
       lambda instead of sitting undeducible in the head. *)
    let all_temps_with_funs, compiled_body =
      Lifting.generalize_lambda_only_tparams ~class_temps all_temps_with_funs cpp_params cod compiled_body
    in
    let lifted_decl =
      lifted_definition ~binders:[] ~modes ~ret:cod lifted_ref cpp_params compiled_body (class_temps @ all_temps_with_funs)
    in
    add_lifted_decl cx lifted_decl;

    (* 10. Compile the continuation body b, substituting calls to x' with
       calls to the lifted function *)
    let lifted_ids, env' = push_vars' [(x', t)] env in
    let x_lifted = fst (List.hd lifted_ids) in
    Binders.push_binders cx env [(x_lifted, t)];
    let cont = gen_stmts cx (Slot.at ~ret ~slot ()) env' k b in
    (* Build the free variable argument expressions *)
    let free_var_cpps =
      List.map (fun (name, _, _) : Cpp_ir.Lowered.Expr.t -> Local name) free_vars
    in
    (* A lifted lambda's own type variables become template parameters of
       the new top-level function, and one that occurs only in the return
       type is deducible from nothing -- the call has to spell it.  Same
       question, same answer, as the lifted-fix path; but asked of the head
       the declaration ended up with, since generalisation may have moved
       a parameter out of it. *)
    let call_type_args =
      Calls.lifted_call_type_args cx ~ret ~class_args ~env ~outer_tvars
           ~head:(List.map snd all_temps_with_funs)
           ~all_tvar_names ~binder_ty:t ~param_core_tys
    in
    List.map
      (subst_lifted_call_stmt x_lifted
         (mk_cppglob lifted_ref call_type_args)
         free_var_cpps )
      cont )

(** A local fixpoint [fix_term] applied to [args] in place, ending in [k]:
    lifted as template helpers where it has type variables of its own,
    otherwise declared in place and called. *)
let gen_applied_fix cx ~ret ~slot env (k : Destination.t) ~x ~ids ~funs ~occ
  ~fix_term ~args :
  Cpp_ir.Lowered.Stmt.t list =
  Core_passes.Local_types.check_minted ids;
  let ids, funs = Core_passes.Local_types.recover_fix_codomains (Calls.local_types_lowering cx) ids funs in
  register_erased_members occ ids;
  (* Collect Tvars from bodies too *)
  let body_tvars = Array.fold_left Lifting.collect_tvars_ast [] funs in
  let all_body_tvars = List.sort_uniq Int.compare body_tvars in
  (* Collect all Core.Type.Variable indices from the fixpoint types *)
  let fix_tvar_indices =
    Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
  in
  let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
  let outer_tvars = get_current_type_vars cx in
  let n_outer = List.length outer_tvars in
  let has_extra_tvars = Base.Type_util.own_type_variables ~n_outer (List.map snd (Array.to_list ids)) in
  (* What the member called yields given [n] arguments, from its Core type. *)
  let applied_type n =
    Typed_checks.core_value_type cx env (Base.Type_util.strip_arrows_n n (snd ids.(x)))
  in
  let fix_value n (e : Cpp_ir.Lowered.Expr.t) = Cpp_ir.Typed.or_type (applied_type n) (Cpp_ir.Typed.of_node e) in
  (* The arguments the plan reads before the call, its parameters being
     bound to them in order ({!Ownership_ir.Region.evaluated_first}), each
     evaluated into a local of its own ahead of everything the call
     makes. *)
  let first = Ownership_ir.Region.evaluated_first cx.ctx.lexical.move_plan occ in
  let evaluated = ref [] in
  let gen_args args =
    let params = List.rev (fst (collect_lams funs.(x))) in
    List.rev
      (List.mapi
         (fun i a ->
           (* A function value passed for a parameter of a function type is
              written against it: a lambda takes every parameter the type
              does ({!Lambda.gen_lambda}). *)
           let e =
             match List.nth_opt params i with
             | Some (_, (Core.Type.Arrow _ as ty)) when count_core_value_arrows ty >= 2 ->
               gen_expr cx (Slot.at ~ret ~expected_ty:(Types.cpp_of_core cx env ty) ~slot:{Slot.empty_slot with expected_core_ty = Some ty} ()) env a
             | _ -> gen_expr cx (Slot.at ~ret ()) env a
           in
           (* As at a call of the member ({!erased_member_types}). *)
           let e =
             match List.nth_opt params i with
             | Some (_, (Core.Type.Arrow _ as ty))
               when Base.Table.is_erased_fix_group occ && List.exists Base.Core_util.has_unknown (core_domains ty) ->
               adapt_to_erased_param cx env ty a e
             | _ -> e
           in
           match (List.mem i first, List.nth_opt params i) with
           | true, Some (_, ty) ->
             let id = Id.of_string (Printf.sprintf "_arg%d" i) in
             evaluated := !evaluated
               @ [ ( Bind_variable (id, Declare (Types.cpp_of_core cx env ty, None), e)
                     : Cpp_ir.Lowered.Stmt.t ) ];
             if Ownership_ir.Region.worth_moving ty then (Move (Local id) : Cpp_ir.Lowered.Expr.t) else Local id
           | _ -> e )
         args )
  in
  let stmts =
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function *)
      let fix_tvar_indices = Lifting.lifted_indices ~n_outer fix_tvar_indices in
      let all_tvar_names = Lifting.build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = Cpp_ir.Build.typenames all_tvar_names in
      (* The body being lifted was written against the enclosing declaration's
         class instances -- it spells [typename _tcI0::PTR::ptr] -- and a
         concept-constrained parameter is not a Core type variable, so
         [fix_tvar_indices] cannot mention one.  Carry the head's own
         instances over, ahead of the type variables and explicit at every
         reference: nothing deduces a class instance from an argument. *)
      let class_temps = current_class_temps cx in
      let class_args = List.map (fun (_, id) -> Cpp_ir.Build.named_variable id) class_temps in
      let extended_tvar_names =
        Lifting.build_extended_tvar_names fix_tvar_indices all_tvar_names all_body_tvars
      in
      let member_refs = Lifting.lifted_member_refs occ ids in
      let lifted_ref = member_refs.(x) in
      (* Compile under the lifted function's extended tvar scope, which covers
         both signature and body Core.Type.Variable indices. *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        with_lifted_fixpoint cx occ @@ fun () ->
        with_type_vars cx extended_tvar_names (fun () ->
            Array.to_list
              (Array.mapi
                 (fun i f ->
                   gen_fix cx ~ret env ~all_fix_ids:all_fix_ids_list ~lifted:member_refs.(i) ~fix_idx:i ids.(i)
                     f )
                 funs ) )
      in
      let renamed = List.map (fun ((id, _), _, _, _) -> id) funs_compiled in
      (* Build lifted declarations *)
      let ungeneralised = Callable_params.lifted_fix_ungeneralised_params funs in
      List.iteri
        (fun i ((_, fix_ty), params, body, param_binders) ->
          let cpp_ty = Types.cpp_ir_of_core_type cx env extended_tvar_names fix_ty in
          let cod = match cpp_ty with Function (_, cod) -> cod | _ -> cpp_ty in
          let non_fwd_source_indices = ungeneralised.(i) in
          let cpp_params, modes, all_temps_with_funs =
            Lifting.build_lifted_cpp_params
              ~non_fwd_source_indices
              (Types.cpp_ir_of_core_type cx env extended_tvar_names)
              all_temps
              params
          in
          let body =
            Lifting.subst_lifted_members
              ~concrete:(Lifting.concrete_results (Types.cpp_ir_of_core_type cx env extended_tvar_names) ids)
              renamed member_refs
              (class_args @ List.map (fun id -> Cpp_ir.Build.named_variable id) all_tvar_names)
              body
          in
          let lifted_decl =
            lifted_definition ~binders:param_binders ~modes ~ret:cod member_refs.(i) cpp_params body
              (class_temps @ all_temps_with_funs)
          in
          add_lifted_decl cx (Control_to_cpp.Lower.lower_lifted ~unit:(Lowering_state.unit_context cx) lifted_decl) )
        funs_compiled;
      let call_type_args =
        Calls.lifted_call_type_args cx ~ret ~class_args ~env ~outer_tvars
             ~head:(List.map snd all_temps) ~all_tvar_names ~binder_ty:(snd ids.(x))
             ~param_core_tys:
               ( match List.nth_opt funs_compiled x with
               | Some (_, params, _, _) -> List.map snd params
               | None -> [] )
      in
      let cpp_args = gen_args args in
      [ Destination.finish cx k
          (fix_value (List.length cpp_args)
             (made_of occ
                (Call (Cpp_ir.Build.signature ~nargs:0 (), mk_cppglob lifted_ref call_type_args, List.rev cpp_args)) ) ) ] )
    else (* No extra Tvars - proceed with by-ref local fixpoint (immediately applied) *)
      let all_fix_ids_list = Array.to_list ids in
      (* A group escaping in its own bodies is closures, and so is one
         applied to fewer arguments than its function takes parameters of
         a runtime value: their bodies own every parameter. *)
      let cofix = match fix_term with Core.Expr.Cofixpoint _ -> true | _ -> false in
      let escapes = closures_group cx ~n_outer ~occ ~cofix ids funs = Closures in
      let partial =
        List.compare_length_with args
          (List.length (List.filter (fun (_, ty) -> not (void_binder ty)) (fst (collect_lams funs.(x)))))
        < 0
      in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix cx ~ret env ~all_fix_ids:all_fix_ids_list ~by_value:(escapes || partial) ~local:occ
                 ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body, _) -> (params, body)) funs_compiled
      in
      let args = gen_args args in
      let _, fix_params, _, _ = List.nth funs_compiled x in
      let n_provided = List.length args in
      let n_fix_params = List.length fix_params in
      if Base.Probe.checking () && partial <> (n_provided < n_fix_params) then
        Base.Probe.violation "partial application"
          (Pp.str "a local fixpoint is applied to other arguments than Core counts");
      if partial then begin
        (* Partial application: the fixpoint escapes (returned as a lambda).
           Use Y-combinator pattern so the fixpoint body doesn't capture
           a stack-local std::function by reference. *)
        let decls, defs, deref_subst =
          gen_local_fix_ycomb cx env ~binders:(local_fix_binders cx env fix_term occ ids funs_compiled)
            ~passing:(local_passing cx ~closures:true funs)
            ~captures:(fix_captures cx ~in_place:false fix_term)
            renamed_ids funs_with_params
        in
        let member : Cpp_ir.Lowered.Type.t =
          Function
            ( List.rev_map (fun (_, t) -> Types.cpp_of_core cx env t) fix_params,
              Types.codomain_after cx env n_fix_params (snd ids.(x)) )
        in
        let fix_id = Cpp_ir.Expr.Local (fst (List.nth renamed_ids x)) in
        (* [args] is last first ({!gen_args}).  The call takes them, and the
           closure over the parameters still to come ([_pa]) takes those as
           the position it fills takes them: curried where a type variable
           stands for the function type, a fold's accumulator. *)
        let closure =
          Cpp_ir.Typed.apply ~first:(Cpp_ir.Build.call fix_id) ~prefix:"_pa" (Cpp_ir.Typed.typed member fix_id)
            (List.rev_map Cpp_ir.Typed.of_node args)
        in
        let into = ret in
        decls @ defs
        @ deref_subst
            [ Destination.finish cx k
                (Cpp_ir.Typed.or_type (applied_type n_provided)
                   (Typed_checks.adapted_or_node into
                      (Coerce.into_slot ~origin:Pa closure (Coerce.slot_of_expected into)) ) ) ]
      end
      else
        let closures = escapes in
        let declared =
          if closures then
            let decls, defs, deref_subst =
              gen_local_fix_ycomb cx env ~binders:(local_fix_binders cx env fix_term occ ids funs_compiled)
                ~passing:(local_passing cx ~closures:true funs)
                ~captures:(fix_captures cx ~in_place:false fix_term)
                renamed_ids funs_with_params
            in
            fun call -> decls @ defs @ deref_subst [call]
          else
            let decls, defs =
              gen_local_fix_by_ref cx env ~binders:(local_fix_binders cx env fix_term occ ids funs_compiled)
                ~passing:(local_passing cx ~closures:false funs) ~captures:(fix_captures cx ~in_place:true fix_term)
                renamed_ids funs_with_params
            in
            fun call -> decls @ defs @ [call]
        in
        (* The call, handed to [k]: into a thunk where the group stands in
           the value a body suspended whole returns, which it escapes into.
           A match generated as an inlined IIFE hands the call to its own
           [return], which the suspending continuation takes in only once
           the IIFE is inlined ({!Lifting.fixpoint_named_in_returns}). *)
        (* Arguments past the lambda's parameters apply to what it returns
           ({!Cpp_ir.Typed.apply}): a fixpoint whose codomain is a function
           type behind a definition -- [st nat], [nat -> nat * nat] -- takes
           its own parameters only, while the term around it, eta-expanded
           at the unfolded type, hands it the state as well. *)
        let call =
          let member : Cpp_ir.Lowered.Type.t =
            Function
              ( List.rev_map (fun (_, t) -> Types.cpp_of_core cx env t) fix_params,
                Types.codomain_after cx env n_fix_params (snd ids.(x)) )
          in
          let callee = Cpp_ir.Expr.Local (fst (List.nth renamed_ids x)) in
          Destination.finish cx k @@ fix_value n_provided
            (made_of occ
               (Cpp_ir.Typed.apply
                  ~first:(fun a -> Call (Cpp_ir.Build.signature ~nargs:0 (), callee, a))
                  (Cpp_ir.Typed.typed member callee)
                  (List.rev_map Cpp_ir.Typed.of_node args) )
                 .expr )
        in
        let suspended = in_suspended_tail cx occ in
        check_fixpoint_escape (fst (List.nth renamed_ids x)) ~closures (fun () ->
            Lifting.fix_escapes_in_own_bodies renamed_ids funs_with_params
            || List.exists
                 (fun (id, _) ->
                   Lifting.fixpoint_escapes_in_stmts id [call]
                   || (suspended && Lifting.fixpoint_named_in_returns id [call]) )
                 renamed_ids );
        declared call
  in
  !evaluated @ stmts

(** A local fixpoint [fix_term] not applied, ending in [k]: it escapes, so
    it is a Y-combinator closure. *)
let gen_standalone_fix cx ~ret env (k : Destination.t) ~x ~ids ~funs ~occ ~fix_term :
  Cpp_ir.Lowered.Stmt.t list =
  (* Standalone fixpoint (not immediately applied) — e.g., appearing as the
     RHS of a let-binding.  Since the fixpoint value itself is returned (not
     called in place), it will always escape.  Use the Y-combinator pattern:
     the generated wrapper lambda [fix_name] is already a plain callable. *)
  Core_passes.Local_types.check_minted ids;
  let ids, funs = Core_passes.Local_types.recover_fix_codomains (Calls.local_types_lowering cx) ids funs in
  let all_fix_ids_list = Array.to_list ids in
  let funs_compiled =
    Array.to_list
      (Array.mapi
         (fun i f ->
           gen_fix cx ~ret env ~all_fix_ids:all_fix_ids_list ~by_value:true ~local:occ ~fix_idx:i ids.(i) f )
         funs )
  in
  let renamed_ids =
    List.map (fun (renamed_id, _, _, _) -> renamed_id) funs_compiled
  in
  let funs_with_params =
    List.map (fun (_, params, body, _) -> (params, body)) funs_compiled
  in
  let decls, defs, _deref_subst =
    gen_local_fix_ycomb cx env ~binders:(local_fix_binders cx env fix_term occ ids funs_compiled)
          ~passing:(local_passing cx ~closures:true funs)
          ~captures:(fix_captures cx ~in_place:false fix_term)
          renamed_ids funs_with_params
  in
  let fix_id = fst (List.nth renamed_ids x) in
  (* The group's wrapper is a closure taking the member's parameters at
     once. *)
  let closure : Cpp_ir.Lowered.Value_type.t =
    match Typed_checks.core_value_type cx env (Some (snd ids.(x))) with
    | Typed t -> ( match Cpp_ir.Arrows.of_type t with Some a -> Closure a | None -> Typed t )
    | v -> v
  in
  decls @ defs @ [Destination.finish cx k (Cpp_ir.Typed.or_type closure (Cpp_ir.Typed.of_node (Local fix_id)))]
