(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Lifting local functions to helpers of their own: their free variables
    and type-variable names, the C++ parameter list and template parameters
    of the helper, whether a local fixpoint escapes its own bodies, and the
    rewriting of a lifted body's references -- C++ locals substituted, the
    group's members named by their helpers, Y-combinator self calls made
    direct. *)

open Common
open Names
open Core_util
open Util
open Translation_state
open Type_util
open Core_query

module IntSet = Escape.IntSet

(** Collect all Core.Type.Variable indices from a Core term, using collect_tvars on embedded
    types. Used to find all type variables referenced in a function body. *)
let rec collect_tvars_ast acc = function
  | Core.Expr.Lambda {parameter_type = ty; body; _} -> collect_tvars_ast (collect_tvars acc ty) body
  | Core.Expr.Let {binder_type = ty; value = a; body = b; _} ->
    collect_tvars_ast (collect_tvars_ast (collect_tvars acc ty) a) b
  | Core.Expr.Global use ->
    List.fold_left
      (fun acc (_, t) -> collect_tvars acc t)
      acc
      (Core_util.Var_types.bindings (Core_util.written_type_args use))
  | Core.Expr.Construct {result_type = ty; arguments = args; _} ->
    List.fold_left collect_tvars_ast (collect_tvars acc ty) args
  | Core.Expr.Match {scrutinee_type = ty; scrutinee = e; branches = brs; _} ->
    let acc = collect_tvars_ast (collect_tvars acc ty) e in
    Array.fold_left
      (fun acc {Core.Match.Branch.binders = ids; result_type = ty; body = body; _} ->
        let acc =
          List.fold_left (fun acc (_, t) -> collect_tvars acc t) acc ids
        in
        collect_tvars_ast (collect_tvars acc ty) body )
      acc
      brs
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    let acc =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) acc ids
    in
    Array.fold_left collect_tvars_ast acc funs
  | Core.Expr.Apply {callee = f; arguments = args} ->
    List.fold_left collect_tvars_ast (collect_tvars_ast acc f) args
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    collect_tvars_ast acc a
  | Core.Expr.Persistent_array {elements = arr; default = def} ->
    collect_tvars_ast (Array.fold_left collect_tvars_ast acc arr) def
  | Core.Expr.Tuple args -> List.fold_left collect_tvars_ast acc args
  | Core.Expr.Bound_variable _
   |Core.Expr.Runtime_error _
   |Core.Expr.Erased_value _
   |Core.Expr.Axiom_value _
   |Core.Expr.UInt63 _ | Core.Expr.Numeral _
   |Core.Expr.Float64 _
   |Core.Expr.String _ -> acc

(** Substitute [Local target] with [repl] in expressions and statements.

    With [~keep_cast:true], an occurrence that already sits directly under an
    [any_cast] keeps that cast: only the variable underneath is substituted,
    and a top-level [any_cast] on [repl] is dropped.  Callers whose [repl] is
    an [any_cast] of [target] use this -- the cast already there was chosen by
    the code that built that use site and knows its runtime encoding, so
    nesting the two casts would throw [std::bad_any_cast].

    With [~extra_args], an occurrence in callee position also gains those
    arguments.  Lifting a local binding to a top-level function turns its free
    variables into trailing parameters, and every call has to grow to match;
    the list is in source order. *)
let rec local_var_subst_expr ?(keep_cast = false) ?(extra_args = []) (target : Id.t) (repl : Cpp_ir.Lowered.Expr.t)
    (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let sub = local_var_subst_expr ~keep_cast ~extra_args target repl in
  match e with
  | Any_cast (ty, Local id) when keep_cast && Id.equal id target ->
    Cpp_erasure.unbox ty (match repl with Any_cast (_, inner) -> inner | r -> r)
  | Call (o, Local id, args) when extra_args <> [] && Id.equal id target ->
    Call (o, repl, List.map sub args @ extra_args)
  | Local id when Id.equal id target -> repl
  | _ ->
    (* A lambda's body then reads the local [repl] reads in place of
       [target], and so do the Core binders it records by name.  What it
       takes by move it takes from [repl] where that is a local, and
       copies otherwise: a capture moves a local, not an expression. *)
    let e : Cpp_ir.Lowered.Expr.t =
      match e with
      | Lambda l ->
        let l =
          match Cpp_ir.Variables.free_in_expr repl with
          | [v] ->
            let rekey = List.map (fun (z, b) -> ((if Id.equal z target then v else z), b)) in
            { l with
              binders = rekey l.binders;
              fixpoint = Option.map
                (fun (f : Cpp_ir.Expr.Local_fixpoint.t) -> {f with captured = rekey f.captured}) l.fixpoint
            }
          | _ -> l
        in
        let moved x =
          if not (Id.equal x target) then [x]
          else match repl with Local v -> [v] | _ -> []
        in
        Lambda {l with moved = List.concat_map moved l.moved}
      | _ -> e
    in
    Cpp_ir.Map.expr
      (Cpp_ir.Map.make ~expr:sub ~stmt:(local_var_subst_stmt ~keep_cast ~extra_args target repl) ~type_:Fun.id ())
      e

(** Statement-level counterpart of [local_var_subst_expr]: substitute
    [Local target] with [repl] inside a single C++ statement. *)
and local_var_subst_stmt ?(keep_cast = false) ?(extra_args = []) (target : Id.t) (repl : Cpp_ir.Lowered.Expr.t)
    (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
  Cpp_ir.Map.stmt
    (Cpp_ir.Map.make
       ~expr:(local_var_subst_expr ~keep_cast ~extra_args target repl)
       ~stmt:(local_var_subst_stmt ~keep_cast ~extra_args target repl)
       ~type_:Fun.id ())
    s

(** Check whether a variable [target] is referenced in a list of C++ stmts. *)
let stmts_reference_var (target : Id.t) (stmts : Cpp_ir.Lowered.Stmt.t list) : bool =
  let exception Found in
  let rec visit_expr (e : Cpp_ir.Lowered.Expr.t) =
    ( match e with
    | Local id when Id.equal id target -> raise Found
    | _ -> () );
    Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:visit_expr ~stmt:visit_stmt ~type_:Fun.id ()) e
  and visit_stmt s =
    Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:visit_expr ~stmt:visit_stmt ~type_:Fun.id ()) s
  in
  try List.iter (fun s -> ignore (visit_stmt s)) stmts; false
  with Found -> true

(** Build type variable names for a list of Core.Type.Variable indices. Indices within
    [n_outer] reuse names from [outer_tvars]; indices beyond get fresh
    [Common.tvar_id i] names. Converts [outer_tvars] to an array for O(1) lookup. *)
let build_tvar_names ~outer_tvars tvar_indices =
  let n_outer = List.length outer_tvars in
  let outer_arr = Array.of_list outer_tvars in
  List.map
    (fun i ->
      if i <= n_outer then outer_arr.(i - 1) else Common.tvar_id i)
    tvar_indices

(** Build extended tvar names covering both signature and body Core.Type.Variable indices.
    A body index absent from the signature is mapped, by the offset between
    the smallest such index and the smallest signature index, onto a
    signature name where that lands in range, and onto [Common.tvar_id i] otherwise;
    an index neither covers is named by [anon_tvar_id].

    @param sig_indices  sorted Core.Type.Variable indices from the function signature
    @param sig_names    the names of those indices, in the same order
    @param body_tvars   sorted, deduplicated Core.Type.Variable indices found in the body *)
let build_extended_tvar_names sig_indices sig_names body_tvars =
  let n_sig = List.length sig_indices in
  let sig_set = IntSet.of_list sig_indices in
  let body_extra_tvars =
    List.filter (fun i -> not (IntSet.mem i sig_set)) body_tvars
  in
  let max_tvar = List.fold_left max 0 (sig_indices @ body_tvars) in
  let tvar_name_map =
    List.map2 (fun i name -> (i, name)) sig_indices sig_names
  in
  let tvar_name_map =
    if body_extra_tvars <> [] then
      let min_sig = List.hd sig_indices in
      let min_extra = List.fold_left min max_int body_extra_tvars in
      let offset = min_extra - min_sig in
      List.fold_left
        (fun acc i ->
          let mapped_sig_idx = i - offset in
          if mapped_sig_idx >= 1 && mapped_sig_idx <= n_sig then
            let name = List.assoc mapped_sig_idx tvar_name_map in
            (i, name) :: acc
          else
            (i, Common.tvar_id i) :: acc )
        tvar_name_map
        body_extra_tvars
    else
      tvar_name_map
  in
  if max_tvar > 0 then
    List.init max_tvar (fun i ->
      let idx = i + 1 in
      match List.assoc_opt idx tvar_name_map with
      | Some name -> name
      | None -> anon_tvar_id idx )
  else
    sig_names

(** The reference under which a helper bound to [binder] by [site], lifted
    out of the declaration currently being generated, is emitted.

    The identity is minted by {!Lifted.make} rather than assembled here, so that
    two helpers cannot become one by agreeing on a spelling; see [lifted.mli]. *)
let lifted_ref site (binder : Id.t) : GlobRef.t =
  Lifted.ref_of (Lifted.make ~origin:!Table.current_decl_ref ~binder site)

(** The helper each member of the local fixpoint group [ids] at [occ] is
    lifted to: a member of its own per function of the group. *)
let lifted_member_refs occ ids =
  Array.mapi (fun i (n, _) -> lifted_ref (Lifted.Fixpoint (occ, i)) n) ids

(** [body], a lifted member's, with each member of its group, which it names
    by [renamed] (in array order), called as the helper [refs] lifts it to at
    [targs], the group's own type arguments, and passed [extra_args], what the
    group captures.  A member reaches its partners as it reaches itself. *)
let subst_lifted_members ?(extra_args = []) renamed refs targs (body : Cpp_ir.Lowered.Stmt.t list) =
  List.fold_left2
    (fun body id r -> List.map (local_var_subst_stmt ~extra_args id (mk_cppglob r targs)) body)
    body renamed (Array.to_list refs)

(** Convert Core params to C++ types with const/ref wrapping, and create
    forwarding-ref template parameters for function-typed params, except
    those at [non_fwd_source_indices] (source order), which keep their
    function type.  A [std::shared_ptr] parameter is taken by [const &],
    any other by [const] value: ownership is not consulted, unlike
    {!Translation_ownership.wrap_param_by_ownership}, so a lifted helper copies what an owned
    parameter would have moved.

    @param convert_fn  converts an [Core.Type.t] to a [cpp_type] (typically
      [convert_core_type_to_cpp_type env tvar_names])
    @param base_temps  the template parameters the callable params are appended to
    @return [(cpp_params, all_temps_with_funs)] *)
let build_lifted_cpp_params ?(non_fwd_source_indices = []) (convert_fn : _ -> Cpp_ir.Lowered.Type.t)
    (base_temps : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters) params =
  let n_total = List.length params in
  let is_non_fwd_source j = List.mem j non_fwd_source_indices in
  let is_non_fwd_db j = List.mem (n_total - 1 - j) non_fwd_source_indices in
  let cpp_params =
    List.map
      (fun (id, ty) ->
        let cpp_ty = convert_fn ty in
        match cpp_ty with
        | Shared_pointer _ -> (id, (Reference (Lvalue, Const cpp_ty) : Cpp_ir.Lowered.Type.t))
        | _ -> (id, Const cpp_ty) )
      params
  in
  let unwrap_fun_ty : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t option = function
    | Const (Function _ as f) -> Some f
    | Function _ as f -> Some f
    | _ -> None
  in
  let fun_tys =
    List.filter_map
      (fun (x, ty, j) ->
        match unwrap_fun_ty ty with
        | Some (Function (dom, cod_f)) when not (is_non_fwd_source j) ->
          let cod_f : Cpp_ir.Lowered.Type.t = if is_cpp_unit_type cod_f then Void else cod_f in
          Some
            (x,
              (Callable_declared (dom, cod_f) : Cpp_ir.Lowered.phase Cpp_ir.Template.Parameter_kind.t), fun_tparam_id j)
        | _ -> None )
      (List.mapi (fun j (x, ty) -> (x, ty, j)) (List.rev cpp_params))
  in
  let n_params = List.length cpp_params in
  let cpp_params =
    List.mapi
      (fun j (x, ty) ->
        match unwrap_fun_ty ty with
        | Some (Function _) when not (is_non_fwd_db j) ->
          (x,
            (Reference (Forwarding, Cpp_ir.Build.named_variable (fun_tparam_id (n_params - j - 1))) :
              Cpp_ir.Lowered.Type.t))
        | _ -> (x, ty) )
      cpp_params
  in
  let extra_temps = List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let all_temps_with_funs = base_temps @ extra_temps in
  (cpp_params, all_temps_with_funs)

(** [generalize_lambda_only_tparams temps params ret body] moves a lifted
    helper's undeducible type parameters into the lambda that is their only
    occurrence, returning the shortened head and the rewritten body.

    A parameter the helper's own signature does not mention cannot be deduced
    from a call.  When every occurrence it does have is the binder of a lambda
    the helper returns, the polymorphism belongs to that lambda rather than to
    the helper -- C++ spells that [auto], and the head is shorter by one.  A
    parameter occurring anywhere else is left where it is: [auto] is not a
    type one may write as a template argument.

    Sound only where call sites name no type argument of their own beyond a
    leading prefix they always name, since a positional explicit argument list
    would be renumbered by the drop. *)
let generalize_lambda_only_tparams (temps : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters)
    (params : (_ * Cpp_ir.Lowered.Type.t) list) (ret : Cpp_ir.Lowered.Type.t) (body : Cpp_ir.Lowered.Stmt.t list) =
  let tvar_named id ty = Cpp_ir.Types.exists (Cpp_ir.Type.is_variable_named id) ty in
  let candidates =
    List.filter
      (fun ((tt : Cpp_ir.Lowered.phase Cpp_ir.Template.Parameter_kind.t), id) ->
        tt = Typename
        && (not (tvar_named id ret))
        && not (List.exists (fun (_, ty) -> tvar_named id ty) params) )
      temps
  in
  if candidates = [] then (temps, body)
  else
    let pinned = ref [] in
    let note ty =
      List.iter
        (fun (_, id) ->
          if tvar_named id ty && not (List.exists (Id.equal id) !pinned) then
            pinned := id :: !pinned )
        candidates;
      ty
    in
    let rec scan_e (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
      match e with
      | Lambda l ->
        Lambda
          { l with
            return_type = Option.map note l.return_type;
            body = List.map scan_s l.body }
      | _ -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:scan_e ~stmt:scan_s ~type_:note ()) e
    and scan_s s = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:scan_e ~stmt:scan_s ~type_:note ()) s in
    List.iter (fun s -> ignore (scan_s s)) body;
    let movable =
      List.filter (fun (_, id) -> not (List.exists (Id.equal id) !pinned)) candidates
    in
    if movable = [] then (temps, body)
    else
      let to_auto (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
        match ty with
        | Variable v when List.exists (fun (_, id) -> Id.equal id (Cpp_ir.Type.variable_spelled v)) movable -> Auto
        | _ -> ty
      in
      let rec rw_e (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
        match e with
        | Lambda l ->
          Lambda
            { l with
              params = List.map (fun (ty, id) -> (to_auto ty, id)) l.params;
              body = List.map rw_s l.body }
        | _ -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:rw_e ~stmt:rw_s ~type_:Fun.id ()) e
      and rw_s s = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:rw_e ~stmt:rw_s ~type_:Fun.id ()) s in
      ( List.filter
          (fun (_, id) -> not (List.exists (fun (_, m) -> Id.equal id m) movable))
          temps,
        List.map rw_s body )

(** Collect de Bruijn indices of free variables in a Core term. n_bound is the
    number of locally bound variables (lambda params, let bindings, etc.).
    Returns indices relative to the outer scope (i.e., i - n_bound for each free
    Core.Expr.Bound_variable i). *)
let rec collect_free_rels_set n_bound acc = function
  | Core.Expr.Bound_variable {index = i; _} -> if i > n_bound then IntSet.add (i - n_bound) acc else acc
  | Core.Expr.Lambda {body; _} -> collect_free_rels_set (n_bound + 1) acc body
  | Core.Expr.Let {value = a; body = b; _} ->
    collect_free_rels_set n_bound (collect_free_rels_set (n_bound + 1) acc b) a
  | Core.Expr.Apply {callee = f; arguments = args} ->
    List.fold_left
      (collect_free_rels_set n_bound)
      (collect_free_rels_set n_bound acc f)
      args
  | Core.Expr.Match {scrutinee = e; branches = brs; _} ->
    let acc = collect_free_rels_set n_bound acc e in
    Array.fold_left
      (fun acc {Core.Match.Branch.binders = ids; body = body; _} ->
        collect_free_rels_set (n_bound + List.length ids) acc body )
      acc
      brs
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    let n_fix = Array.length ids in
    Array.fold_left
      (fun acc f ->
        let params, body = collect_lams f in
        collect_free_rels_set (n_bound + List.length params + n_fix) acc body )
      acc
      funs
  | Core.Expr.Construct {arguments = args; _} ->
    List.fold_left (collect_free_rels_set n_bound) acc args
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    collect_free_rels_set n_bound acc a
  | Core.Expr.Tuple args -> List.fold_left (collect_free_rels_set n_bound) acc args
  | Core.Expr.Persistent_array {elements = arr; default = def} ->
    collect_free_rels_set
      n_bound
      (Array.fold_left (collect_free_rels_set n_bound) acc arr)
      def
  | Core.Expr.Global _
   |Core.Expr.Runtime_error _
   |Core.Expr.Erased_value _
   |Core.Expr.Axiom_value _
   |Core.Expr.UInt63 _ | Core.Expr.Numeral _
   |Core.Expr.Float64 _
   |Core.Expr.String _ -> acc

(** Collect all free de Bruijn variables (rels) from a Core term, wrapping
    [collect_free_rels_set]. Used to detect which lambda parameters are
    captured. *)
let collect_free_rels n_bound body =
  IntSet.elements (collect_free_rels_set n_bound IntSet.empty body)

(** Which free variables of a body being lifted become trailing parameters.

    Lifting moves a body out of the scope that bound its free variables, so
    each one has to arrive as an argument instead -- but not every free rel is
    a value there is anything to pass.

    - A class instance is already carried by
      {!Translation_state.current_class_temps} as a
      template parameter, explicit at every reference because nothing deduces
      one.  Passing it again emits [const Params _tcI0], which is ill-formed
      (a concept is not a type) and shadows the template parameter it is named
      after, so every use in the body then resolves to the value.
    - An erased or void binder has no value at all.

    Both lift paths ask this, and they ask it of the same [env]: the names are
    the enclosing scope's, so a compiled body needs no substitution and only
    the head and the call sites grow. *)
let lifted_free_vars cx ~class_temps env free_indices =
  List.filter_map
    (fun i ->
      let name = Common.get_db_name i env in
      let ty = get_env_type cx i in
      if
        List.exists (fun (_, id) -> Id.equal id name) class_temps
        || not (is_runtime_binder_type ty)
      then
        None
      else
        Some (name, ty, i) )
    free_indices

(** One function of a local fixpoint block, as its Y-combinator form names
    it: the fixpoint's own name, the self parameter every impl lambda takes
    for it, and its parameters' C++ types, innermost first. *)
type local_fix_self = {
  fix_id : Id.t;
  self_id : Id.t;
  param_tys_rev : Cpp_ir.Lowered.Type.t list;
  param_core_tys_rev : Core.Type.t list;  (** the parameters' Core types, as [param_tys_rev] spells them *)
}

(** The {!local_fix_self} of each function of a block, from the fixpoints'
    renamed names and the parameters [gen_fix] gave them; [cpp_of] spells a
    parameter's type. *)
let local_fix_selves cpp_of renamed_ids funs_with_params =
  List.map2
    (fun (fix_id, _) (args, _) ->
      { fix_id;
        self_id = Id.of_string ("_self_" ^ Id.to_string fix_id);
        param_tys_rev = List.map (fun (_, ty) -> cpp_of ty) args;
        param_core_tys_rev = List.map snd args } )
    renamed_ids funs_with_params

(** Rewrite a local fixpoint's recursive calls to pass the self-parameters.

    Both lowerings of a local fixpoint -- the by-reference one and the
    Y-combinator one -- generate an [f_impl] lambda that takes [_self_f]
    ahead of its own arguments, so both need every call to [f] inside the
    body to grow that argument.  The rewrite is the same one, so it lives
    here rather than in each.

    A recursive call reaches its arguments through however many applications
    Core curried it into: [f a b] can arrive as one call of two arguments
    or as two calls of one.  The lambda takes them all at once, so the
    application spine is flattened before [_self_f] is prefixed -- rewriting
    only the innermost call yields [_self_f(_self_f, a)(b)], which asks a
    three-argument lambda for two.  A unary fixpoint cannot show the
    difference.

    A fixpoint named as a value rather than called -- [H F], [F] handed to
    another function -- is the function its wrapper would be, written where
    the wrapper is not yet declared: a closure over its parameters, of the
    C++ types [param_tys_rev] gives in reverse, calling the self-parameter.
    The closure takes each by value and reads it once, passing it on: it
    moves one a copy of which costs more ({!Ownership_ir.worth_moving}).

    Unless [passing], no self-parameter is passed: each call is flattened and
    still calls the fixpoint by its own name, as a loop lowered from the
    fixpoint's ControlIR takes it ({!Control_to_cpp_ir.local_loop}),
    and a fixpoint named as a value is left as it is.

    @return the expression and statement rewriters, which are mutually
      recursive and must be taken together. *)
let self_call_rewriter ?(passing = true) (selves : local_fix_self list) :
    (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t) * (Cpp_ir.Lowered.Stmt.t -> Cpp_ir.Lowered.Stmt.t) =
  let self_vars : Cpp_ir.Lowered.Expr.t list =
    if passing then List.map (fun s : Cpp_ir.Lowered.Expr.t -> Local s.self_id) selves else [] in
  let find_self id =
    Option.map (fun s -> ((if passing then s.self_id else s.fix_id), s))
      (List.find_opt (fun s -> Id.equal id s.fix_id) selves)
  in
  let find_self_id id = Option.map fst (find_self id) in
  let call occurrence f args : Cpp_ir.Lowered.Expr.t =
    Call ({yields = Untyped; params = Unknown; constructs = None; occurrence}, f, args)
  in
  (* The self id this application spine calls, with every argument along it
     in one source-order list -- an inner application's arguments come
     before an outer one's -- and the Core call the spine is made of, which
     its innermost call records. *)
  let rec self_call_spine : Cpp_ir.Lowered.Expr.t -> _ = function
    | Call (cs, Local id, args) -> Option.map (fun self_id -> (self_id, args, cs.occurrence)) (find_self_id id)
    | Call (_, callee, args) ->
      Option.map (fun (self_id, inner, occurrence) -> (self_id, inner @ args, occurrence)) (self_call_spine callee)
    | _ -> None
  in
  let rec rewrite_expr (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
    match self_call_spine e with
    | Some (self_id, args, occurrence) -> call occurrence (Local self_id) (self_vars @ List.map rewrite_expr args)
    | None -> (
      match e with
      | Local id when passing && Option.has_some (find_self id) ->
        let self_id, self = Option.get (find_self id) in
        let tys_rev = self.param_tys_rev in
        let n = List.length tys_rev in
        let params_rev =
          List.mapi (fun i ty -> (ty, Some (Id.of_string (Printf.sprintf "_ec%d" (n - 1 - i))))) tys_rev
        in
        let args_rev =
          List.map2
            (fun (_, x) core ->
              let v : Cpp_ir.Lowered.Expr.t = Local (Option.get x) in
              if Ownership_ir.worth_moving core && not (Type_util.core_type_is_unit core) then
                (Move v : Cpp_ir.Lowered.Expr.t) else v )
            params_rev self.param_core_tys_rev
        in
        Lambda
          { type_params = [];
            binders = [];
            fixpoint = None;
            moved = [];
            params = List.rev params_rev;
            return_type = None;
            body = [Return (Some (call None (Local self_id) (self_vars @ List.rev args_rev)))];
            capture = Stored }
      | _ -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:rewrite_expr ~stmt:rewrite_stmt ~type_:Fun.id ()) e )
  and rewrite_stmt s = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:rewrite_expr ~stmt:rewrite_stmt ~type_:Fun.id ()) s in
  (rewrite_expr, rewrite_stmt)

(** Whether the generated code [stmts] lets the local fixpoint [target_id]
    escape: names it other than as the callee of a direct call
    [Call (_, Local target_id, args)], or names it at all inside a
    {!Closure}.  Core decides this ({!Analyze_closures}); the generated code
    is only the oracle [CRANE_CHECK_IR] checks it against. *)
let fixpoint_escapes_in_stmts target_id (stmts : Cpp_ir.Lowered.Stmt.t list) =
  let rec check_expr (e : Cpp_ir.Lowered.Expr.t) =
    match e with
    | Call (_, Local id, args) when Id.equal id target_id ->
      List.exists check_expr (List.rev args)
    | Local id when Id.equal id target_id -> true
    | Lambda {body; capture = Runs_in_place; _} -> check_stmts body
    | Lambda {body; capture = Stored; _} ->
      let rec has_var_in_expr (e : Cpp_ir.Lowered.Expr.t) =
        match e with
        | Local id when Id.equal id target_id -> true
        | _ ->
          let found = ref false in
          let fe e' = if not !found then found := has_var_in_expr e'; e' in
          let fs s' = if not !found then found := has_var_in_stmt s'; s' in
          ignore (Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id ()) e);
          !found
      and has_var_in_stmt s =
        let found = ref false in
        let on_expr e = if not !found then found := has_var_in_expr e in
        let on_stmts ss =
          if not !found then found := List.exists has_var_in_stmt ss
        in
        Cpp_ir.Subterms.stmt ~expr:on_expr ~stmts:on_stmts s;
        !found
      in
      List.exists has_var_in_stmt body
    | _ ->
      let found = ref false in
      let fe e = if not !found then found := check_expr e; e in
      ignore (Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:fe ~stmt:Fun.id ~type_:Fun.id ()) e);
      !found
  and check_stmt s =
    let found = ref false in
    let on_expr e = if not !found then found := check_expr e in
    let on_stmts ss = if not !found then found := check_stmts ss in
    Cpp_ir.Subterms.stmt ~expr:on_expr ~stmts:on_stmts s;
    !found
  and check_stmts ss = List.exists check_stmt ss
  in
  check_stmts stmts

(** Whether the generated bodies [funs_with_params] of a local fixpoint
    group let a member of [renamed_ids] escape ({!fixpoint_escapes_in_stmts}):
    the oracle of {!Analyze_closures} for a group's own bodies. *)
let fix_escapes_in_own_bodies renamed_ids funs_with_params =
  List.exists
    (fun (id, _) ->
      List.exists (fun (_, body) -> fixpoint_escapes_in_stmts id body) funs_with_params )
    renamed_ids
