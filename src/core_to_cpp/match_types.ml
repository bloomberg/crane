(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Typing a match before its branches are lowered: the C++ type of the
    scrutinee, the types its pattern binders are pinned to, a custom match's
    scrutinee and binders, the constructor a branch tests, and the type a
    match lowered to an IIFE returns. *)

open Base.Common
open Names
open Base.Core_util
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query

(** For inductives with dependent parameters (e.g. [sigT]), unresolved
    rigid type variables correspond to fields whose C++ type
    collapses to [std::any].  Retyping them as [Core.Type.Erased Core.Erasure_reason.Type_argument] marks them
    as erased, triggering [any_cast<T>] wrapping when returned as a
    template parameter. *)
let retype_dependent_params (typ : Core.Type.t) ids =
  let is_dep_ind = match typ with
    | Core.Type.Global_app {head = GlobRef.IndRef _ as g; _} -> Base.Table.has_dependent_params g
    | _ -> false
  in
  if is_dep_ind then
    List.map (fun (n, core_ty) ->
      match core_ty with Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; _} ->
        (n, Core.Type.Erased Core.Erasure_reason.Type_argument) | _ -> (n, core_ty)) ids
  else ids

(** The declared Core types of constructor [ctor]'s value fields, instantiated at
    scrutinee type [typ]'s type arguments — the types a branch's pattern
    variables have by construction, in field order.

    [None] when the answer would not be trustworthy: either the inductive has
    no recorded [constructor_argument_types] (custom-extracted ones such as [prod] do not; for
    those the scrutinee's own type arguments {i are} the field types), or a
    field mentions a parameter the scrutinee does not instantiate, in which
    case substitution would leave a stray [Core.Type.Variable] behind and a stray [Core.Type.Variable] is
    worse than the [std::any] it would replace. *)
let ctor_field_types_at ctor (typ : Core.Type.t) =
  let tyargs = match typ with Core.Type.Global_app {type_arguments = args; _} -> args | _ -> [] in
  let nargs = List.length tyargs in
  let rec within_scope : Core.Type.t -> bool = function
    | Core.Type.Variable {variable = i; _} -> i <= nargs
    | Core.Type.Variable_app {head = i; arguments = args} -> i <= nargs && List.for_all within_scope args
    | Core.Type.Arrow {parameter = a; result = b} -> within_scope a && within_scope b
    | Core.Type.Global_app {type_arguments = l; _} -> List.for_all within_scope l
    | Core.Type.Meta {contents = Some t} -> within_scope t
    | _ -> true
  in
  match Base.Table.get_ctor_ip_types_opt ctor with
  | Some tys ->
    let tys = List.filter (fun t -> not (Base.Core_util.is_erased_type t)) tys in
    if List.for_all within_scope tys then
      Some (List.map (Base.Core_util.type_subst_list tyargs) tys)
    else None
  | None -> (
    match typ with
    | Core.Type.Global_app {head = g; _} when is_prod_global g -> Some tyargs
    | _ -> None )

(** Recover a pattern variable's type from the scrutinee's own type structure
    when extraction left it as an unresolved meta-variable ([Core.Type.Meta
    {contents=None}]).

    For a [prod A B] scrutinee destructured as [(x, y)], [x]'s and [y]'s Core
    types are exactly [A] and [B] — but when [A]/[B] come from a
    non-reducible dependent computation (e.g. projecting an element out of
    [tuple (List.map symbol_semty gamma)] for a nonterminal/production
    grammar), Rocq's extraction can fail to unify the pattern variable's own
    type with the (perfectly concrete, if opaque) component type visible in
    the scrutinee's [Core.Type.Global_app(prod, [A; B])] annotation, leaving the pattern
    variable's type as a dangling meta.  A dangling meta erases to
    [std::any] with no further structure, discarding container information
    (e.g. "this is a [list]") that the scrutinee type still carries — so a
    "cons" production destructuring such a pattern var loses track of the
    fact that it's building a [list], while the "nil" production (whose
    return type is directly, concretely annotated, with no destructuring
    involved) keeps it — the reason nil and cons productions of the very
    same Coq-level [list] type diverge in their erased C++ representation.

    The pair is only the clearest case; the same recovery applies to any
    inductive, which is why the field types come from
    {!ctor_field_types_at} rather than from the scrutinee's type arguments
    directly.

    [ids] here is in reverse-bound order relative to the constructor's fields
    (the last pattern variable in the list is the first field), matching the
    convention already used elsewhere in this file. *)
let recover_pattern_var_types_from_scrutinee ~ctor (typ : Core.Type.t) ids =
  match ctor_field_types_at ctor typ with
  | Some ftys when List.length ftys = List.length ids ->
    let n = List.length ftys in
    List.mapi
      (fun i (x, core_ty) ->
        let fty = List.nth ftys (n - 1 - i) in
        (* The field at the scrutinee's instantiation is the binder's type
           wherever the pattern's own annotation says less: an open meta, or
           an erased component the scrutinee states ([md] of a pattern over
           [(nat * phi T) * list (metadata T)]). *)
        match core_ty with
        | Core.Type.Meta {contents = None} | Core.Type.Open _ -> (x, fty)
        | _
          when Base.Type_util.is_core_erased_ty core_ty
               && not (Base.Type_util.is_core_erased_ty fty) ->
          (x, fty)
        | _ -> (x, core_ty))
      ids
  | _ -> ids

(** The binder a match scrutinee names, seen through the wrappers that leave
    the value alone: a magic cast, and a dependent instantiation.  A payload
    whose type is written [P x] appears applied to its witness, but a binder
    of non-function type is no callable: the application names the binder
    itself, and that is where the value's C++ type was pinned down. *)
let rec scrutinee_binder cx = function
  | Core.Expr.Bound_variable {index = i; _} -> Some i
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    scrutinee_binder cx e
  | Core.Expr.Apply {callee = h; _} when not (scrutinee_head_is_callable cx h) ->
    scrutinee_binder cx h
  | _ -> None

(** Whether a term in head position really is a function being applied, as
    opposed to a binder that a dependent type spells applied to its index. *)
and scrutinee_head_is_callable cx h =
  match scrutinee_binder cx h with
  | Some i ->
    let rec is_arrow = function
      | Core.Type.Meta {contents = Some t} -> is_arrow t
      | Core.Type.Arrow _ -> true
      | _ -> false
    in
    (match get_env_type_opt cx i with Some t -> is_arrow t | None -> true)
  | None -> true

(** Test whether a C++ expression is "trivial" — a simple variable or member
    access that can safely be duplicated without side effects.  Non-trivial
    expressions (function calls, constructor applications, etc.) should be
    cached in a temporary when the custom match template uses [%scrut] more
    than once.  A member access or dereference is trivial only as far as the
    object it reads is: [mk(n).sub] calls [mk] at every mention. *)
let rec is_trivial_scrut : Cpp_ir.Lowered.Expr.t -> bool = function
  | Local _ | Scope _ | Type_member _ | Enum_value _ | Entity _ -> true
  | Member (e, _) | Project (e, _, _) | Access (_, e, _) | Dereference e -> is_trivial_scrut e
  | _ -> false

(** [iife_void_return env typ pv] is [Some Tvoid] when the match's branches
    produce nothing: a lambda that may fall off its end has to say [-> void]
    explicitly. *)
let iife_void_return cx env typ pv : Cpp_ir.Lowered.Type.t option =
  let branch_rty =
    match Array.to_list pv with {Core.Match.Branch.result_type = rty; _} :: _ -> rty | [] -> typ
  in
  let r = Types.cpp_of_core cx env branch_rty in
  if is_cpp_unit_type r || Monadic.core_type_is_void_call branch_rty then
    Some Void
  else None

(** The function type a lambda whose returns are written under the return
    type in force, [ret], and which computes a value annotated [r], is
    declared at: [ret], where it is [r] with its arrows grouped otherwise --
    curried, as a type variable instantiated at [r] takes it -- and [r]
    where [ret] is no such regrouping, the enclosing declaration's own
    return type, say, reaching a position that does not install one. *)
let joined_at ~(ret : Cpp_ir.Lowered.Type.t option) (r : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t option =
  let rec uncurried (t : Cpp_ir.Lowered.Type.t) =
    match t with
    | Function (doms, cod) ->
      let ds, c = uncurried cod in
      (doms @ ds, c)
    | t -> ([], t)
  in
  match (ret, r) with
  | Some (Function _ as f), Function _ when f <> r && uncurried f = uncurried r -> Some f
  | _, Function _ -> Some r
  | _ -> None

(** The types of the values [stmts] return at their own level (the
    [return]s of a nested lambda are its own), each as lowering synthesised
    it where it was returned ([returned], {!Lowering_state.with_returns}),
    and otherwise as its node says. *)
let returned_types ~returned (stmts : Cpp_ir.Lowered.Stmt.t list) : Cpp_ir.Lowered.Value_type.t list =
  let typed_of (e : Cpp_ir.Lowered.Expr.t) =
    match List.find_map (fun (e', ty) -> if e' == e then Some ty else None) returned with
    | Some ty -> ty
    | None -> Cpp_ir.Typed.node_type e
  in
  let rec stmt acc (s : Cpp_ir.Lowered.Stmt.t) =
    match s with
    | Return (Some e) -> typed_of e :: acc
    | _ ->
      let acc = ref acc in
      Cpp_ir.Subterms.stmt ~expr:(fun _ -> ()) ~stmts:(List.iter (fun s -> acc := stmt !acc s)) s;
      !acc
  in
  List.rev (List.fold_left stmt [] stmts)

(** [iife_closure_return env typ pv ~returned stmts] is the return type to
    annotate the IIFE wrapping a match with, given the branches already
    generated, [returned] what they returned.

    Distinct closures have no common type, so a match that returns one from
    some branch needs the [std::function] they all convert to.  Otherwise
    [None]: deducing beats annotating, because the branch's recorded Core type
    can outlive the term it described -- a motive's arrow surviving the
    application that consumed it -- and because it may still mention type
    variables that mean nothing in a non-template context.

    The question is asked of the types of the values returned
    ({!Cpp_ir.Value_type.deduces_none}), not of the Core terms: a branch
    returns a closure whether it was written as a lambda or arose from a
    partial application, a global function named is a function's name, a
    class method [I::m] among them, and two function-typed parameters are
    two deduced template parameters.

    The type joined at is the one the branches were written under, [ret],
    where that is a function type ({!Match.branch_return}): a lambda in a
    branch tail takes its arguments grouped as [ret] groups them -- curried
    where the match is handed to a parameter that is a type variable at a
    function type -- and the annotation, read off Core, groups them flat. *)
let rec iife_closure_return ?ret ~returned cx env typ pv (stmts : Cpp_ir.Lowered.Stmt.t list) : Cpp_ir.Lowered.Type.t option =
  let branch_rty =
    match Array.to_list pv with {Core.Match.Branch.result_type = rty; _} :: _ -> rty | [] -> typ
  in
  iife_closure_return_at ?ret ~returned cx env branch_rty stmts

(** The same question of any lambda whose return type C++ would deduce --
    an IIFE, or a function value ({!Lambda.gen_lambda}) -- computing a value
    of the Core type [rty], [~several] where only one returning from more
    than one place is asked it: a single closure returned deduces its own
    type, which converts wherever it goes. *)
and iife_closure_return_at ?(several = false) ?ret ~returned cx env rty (stmts : Cpp_ir.Lowered.Stmt.t list) :
    Cpp_ir.Lowered.Type.t option =
  let types = returned_types ~returned stmts in
  if (several && List.length types < 2) || not (Cpp_ir.Value_type.deduces_none types) then None
  else match Types.cpp_of_core cx env rty with Function _ as r -> joined_at ~ret r | _ -> None

(** An immediately invoked lambda over the body [gen] lowers, computing a
    value annotated [rty] -- the Core type of the term it stands for --
    whose returns are written under [ret]: declared at the type its
    callables join at ({!iife_closure_return_at}), deduced where they need
    none.  Every lambda of the kind that returns from more than one place
    goes through it. *)
and value_iife ?ret cx env (rty : Core.Type.t option) (gen : unit -> Cpp_ir.Lowered.Stmt.t list) : Cpp_ir.Lowered.Expr.t =
  let body, returned = Lowering_state.with_returns cx gen in
  Cpp_ir.Build.iife (Option.bind rty (fun rty -> iife_closure_return_at ~several:true ?ret ~returned cx env rty body)) body

(** [pattern_field_pins ~scrut_pinned ~cname ~typ ~env ~n_fields
    ~non_erased_def_site_field_tys] -- what a pattern-match branch pins down
    about each of its [n_fields] fields, in field order: whether the field is
    stored as a box, and the scrutinee's template argument that fixes its
    C++ type, if its definition-site type is one of the inductive's own
    parameters.  Reads no binder: the scrutinee is described by its Core type
    and, where an enclosing branch pinned it, by that C++ type.

    @param scrut_pinned  the C++ type an enclosing branch pinned down for the
           scrutinee, when it is a local binder
    @param cname  constructor reference (to look up parameter count)
    @param typ    Core type of the scrutinee
    @param env    translation environment
    @param n_fields    number of pattern variables in the branch
    @param non_erased_def_site_field_tys  definition-site field types
           with erased (dummy) entries filtered out *)
let pattern_field_pins cx ~scrut_pinned ~cname ~typ ~env ~n_fields
    ~non_erased_def_site_field_tys =
  let scrut_cpp_ty =
    (* An enclosing branch may already have pinned the scrutinee's C++ type
       down -- [SigT<any, pair<any,any>>] tells us its payload binder is a
       [pair<any,any>], which its Core type (a bare type variable) does not.
       Prefer that over re-deriving from the Core type. *)
    match scrut_pinned with
    | Some t when not (Types.resolves_to_any_type cx t) -> t
    | _ ->
      Types.cpp_of_core cx env typ
  in
  (* Whether an opaque type among the scrutinee's template arguments is
     a box.  [Topaque] only admits that the argument could not be resolved --
     but for an inductive Crane generates, the field that names it is written
     out, and {!Cpp_passes.Erasure.materialise} spells that declaration [std::any], so
     the value really is boxed.  A custom-extracted scrutinee has no such
     declaration: [std::optional<T>] is spelled by the mapping, and where the
     scrutinee is only ever bound to [auto] nothing wrote a box at all. *)
  let opaque_arg_is_a_box =
    match resolve_meta typ with
    (* ... unless the mapping's own type argument is one that erases: a family
       indexed by a value is spelled [std::any] in the instantiation, so the
       [std::optional<std::any>] the mapping produced really does hold a
       box. *)
    | Core.Type.Global_app {head = g; type_arguments = args; _} ->
      not (Base.Table.is_custom g) || List.exists (Erasure.core_erases_to_box cx env) args
    | _ -> true
  in
  (* Whether one of the scrutinee's template arguments holds a boxed value.
     This is the only question asked about an argument's erasure here, so it
     is settled once: [Topaque] is the sole case where being spelled
     [std::any] does not settle it, and it is decided above rather than
     re-decided at each site. *)
  let arg_is_a_box (t : Cpp_ir.Lowered.Type.t) =
    match t with Obligation Opaque_type -> opaque_arg_is_a_box | t -> Types.resolves_to_any_type cx t
  in
  let scrut_template_args =
    let args = extract_template_args scrut_cpp_ty in
    (* One boxed argument means the whole instantiation was erased, so every
       argument is boxed -- the same rule the type-index cutoff applies to a
       [Core.Type.Erased Core.Erasure_reason.Type_argument] index, here for an argument erased because it mentions a
       free (existential) type variable.  Without it a payload
       [pair<any, function<nat(any)>>] would be read back component-wise at
       two different erasures from the [pair<any, any>] its producer stored. *)
    (* An unresolved argument of a custom-extracted scrutinee does not count:
       see [opaque_arg_is_a_box]. *)
    if List.exists arg_is_a_box args then
      (* An argument that already carries an erased component is at the shape
         its producer stored it in -- a [pair<List<any>, any>] payload is
         written down that way in the field, and reading it back as a flat
         [any] would lose the components the producer boxed individually. *)
      List.map
        (fun a -> if has_tany_in_type a then a else index_erase_type a)
        args
    else args
  in
  let num_pv = Base.Table.get_ctor_num_param_vars cname in
  (* The scrutinee's template argument that fixes this field's type, if the
     field's definition-site type is one of the inductive's own parameters.
     [Core.Type.Variable_app (k, _)] counts: [sigT]'s payload field is written [P x], a
     parameter applied to the witness, and it is [P] that the instantiation
     pins down. *)
  let rec field_template_arg = function
    | Core.Type.Variable {variable = k; _} | Core.Type.Variable_app {head = k; _} ->
      List.nth_opt scrut_template_args (k - 1)
    | Core.Type.Meta {contents = Some t} -> field_template_arg t
    | _ -> None
  in
  let field_arg field_i =
    if num_pv = 0 then None
    else Option.bind (List.nth_opt non_erased_def_site_field_tys field_i)
           field_template_arg
  in
  let is_field_stored_as_any field_i =
    if num_pv = 0 then
      match List.nth_opt non_erased_def_site_field_tys field_i with
      | Some def_ty ->
        let cpp_ty =
          Types.cpp_ir_of_core_type cx (empty_env ()) ~ns:Core.Ref.User.Set.empty [] def_ty
        in
        has_unnamed_tvar cpp_ty
      | None -> false
    else
      match field_arg field_i with
      | Some t -> arg_is_a_box t
      | None -> false
  in
  List.init n_fields (fun field_i -> (is_field_stored_as_any field_i, field_arg field_i))

(** [populate_erased_field_env ?scrut_db ...] records {!pattern_field_pins}
    in {!cpp_binder_types} for a branch binding [n_pat_vars] pattern
    variables: a field stored as a box is recorded erased, then the template
    argument fixing a field's type, which does not overwrite the box.
    [scrut_db] is the scrutinee's de Bruijn index within the branch, when it
    is a local binder whose C++ type an enclosing branch recorded. *)
let populate_erased_field_env cx ?scrut_db ~cname ~typ ~env ~n_pat_vars ~n_fields
    ~non_erased_def_site_field_tys () =
  let scrut_pinned = Option.bind scrut_db (Binders.pattern_binder_type cx) in
  List.iteri
    (fun field_i (stored_as_any, arg) ->
      let db_idx = n_pat_vars - field_i in
      if stored_as_any then Binders.record_binder_type cx db_idx Any;
      Option.iter (Binders.record_binder_type cx db_idx) arg )
    (pattern_field_pins cx ~scrut_pinned ~cname ~typ ~env ~n_fields ~non_erased_def_site_field_tys)

(** [match_scrutinee_type env typ t pv ~var_type ~var_cpp_type] -- the type a
    match over [t] annotated [typ], with branches [pv], is generated at: the
    annotation, with what it leaves open filled from the scrutinee -- a
    variable's binder ([var_type] its Core type, [var_cpp_type] the C++ type
    it was decided to have), anything else its own structure -- and, failing
    an inductive, the one the first branch's constructor belongs to.  Reads
    no binder itself: what a variable stands for is the caller's to say. *)
let match_scrutinee_type cx env (typ : Core.Type.t) t pv ~var_type ~var_cpp_type =
  (* When the match type annotation has unresolved Tvars, try to resolve from
     context. This handles monomorphic functions where Core.Expr.Match has Core.Type.Variable but the
     concrete type is known. *)
  let rec resolvable_here = function
    | Core.Type.Global_app {head = g; type_arguments = ts; _} ->
      ( (not (Base.Table.is_promoted_type_var g))
      || Types.promoted_var_resolution cx g <> None )
      && List.for_all resolvable_here ts
    | Core.Type.Arrow {parameter = a; result = b} -> resolvable_here a && resolvable_here b
    | Core.Type.Meta {contents = Some t} -> resolvable_here t
    | _ -> true
  in
  let resolve_tvar_type typ candidate =
    match (typ, candidate) with
    | Core.Type.Global_app {head = r1; _}, Core.Type.Global_app {head = r2; _}
      when globref_equal r1 r2
           && has_tvar typ
           && (not (has_tvar candidate))
           (* Only a candidate that erased nothing replaces the annotation
              whole: [observe t] at a family its call erased is [itreeF D _]
              where the annotation knows the family. *)
           && not (core_type_contains_erased candidate) -> candidate
    | _ ->
      (* The annotation may state the inductive and leave its argument open --
         [EOU _] for a call whose declared result is [EOU ptr] -- and then the
         match spells [std::any] where the value has a type.  The candidate is
         the declaration the scrutinee was produced by, so it may fill what the
         annotation left open, and nothing more: see
         {!Base.Type_util.refine_erased}.  A promoted variable this scope cannot
         resolve is not an answer, and neither is an erased one. *)
      Base.Type_util.refine_erased
        ~writable:(fun t ->
          resolvable_here t
          && Types.names_only_scoped_tvars cx (Types.cpp_of_core cx env t)
          && not (Base.Type_util.has_tany_in_type (Types.cpp_of_core cx env t)) )
        typ candidate
  in
  let typ =
    match t with
    | Core.Expr.Bound_variable {index = i; _}
    | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
    | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
    | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} ->
      (* Scrutinee is a variable reference — use its concrete type, the one
         its binder was given, a parameter's as much as a let's.  Unwrap Core.Type.Meta
         wrappers since env_types may store types in Core.Type.Meta form. *)
      let rec unwrap_meta = function
        | Core.Type.Meta {contents = Some t} -> unwrap_meta t
        | t -> t
      in
      let env_ty_opt =
        try
          let env_ty =
            unwrap_meta (match var_type i with Some t -> t | None -> raise Not_found)
          in
          match env_ty with
          | Core.Type.Global_app _ -> Some env_ty
          | _ -> None
        with _ -> None
      in
      let typ =
        match env_ty_opt with
        | Some let_ty -> resolve_tvar_type typ let_ty
        | None -> typ
      in
      (* The variable's declared C++ type is what its value is: where it
         erased a position -- a pattern field of a plain family parameter,
         [Sum1<BE, cE, std::any>] inside [Sum1<AE, _, X>], whose Core type
         says [X] -- the match spells it erased too. *)
      let rec erase_as ml (cpp : Cpp_ir.Lowered.Type.t) =
        match (resolve_meta ml, Base.Type_util.unqualify_ty cpp) with
        | Core.Type.Global_app {head = g; type_arguments = mas; index_arguments = x}, Entity_application (g', cas, _)
          when GlobRef.CanOrd.equal g g' && List.length mas = List.length cas ->
          Core.Type.Global_app {head = g; type_arguments = List.map2
                (fun m c ->
                  if Cpp_ir.Types.prints_as_any c && not (core_type_contains_erased m) then
                    Core.Type.Unknown
                  else erase_as m c )
                mas cas; index_arguments = x}
        | m, _ -> m
      in
      ( match var_cpp_type i with
      | Some bt -> erase_as typ (strip_cpp_ref_const bt)
      | None -> typ )
    | _ ->
      (* Anything else: the scrutinee's own structure says what it produces,
         through the one reader -- a call's instantiated codomain, a
         projection's field type.  Reading it here rather than re-deriving a
         callee's return type keeps a projection, which is an [Core.Expr.Match] and not
         an application at all, from being left out. *)
      ( match
          ( match Erasure.core_projection_field_type (strip_magic t) with
          | Some _ as c -> c
          | None -> infer_core_body_type t )
        with
      | Some cand -> resolve_tvar_type typ cand
      | None -> typ )
  in
  (* When the type is still unresolved (Tunresolved / Core.Type.Erased / non-Core.Type.Global_app),
     recover the inductive from the first branch's constructor pattern -- a
     constructor determines the inductive it belongs to, so this is sound
     wherever the scrutinee's own type failed to resolve.  It happens for a
     dependent field stored as [std::any] (sigT's second projection) and for
     the body of an instance method, which is extracted against the class's
     erased carrier and so carries no type for the scrutinee at all. *)
  let typ =
    match typ with
    | Core.Type.Global_app _ -> typ
    | _ ->
      ( try
          let {Core.Match.Branch.pattern = pat0; _} = pv.(0) in
          match pat0 with
          | Core.Pattern.Constructor {constructor = GlobRef.ConstructRef (ip, _); _} ->
            Core.Type.Global_app {head = GlobRef.IndRef ip; type_arguments = []; index_arguments = []}
          | _ -> typ
        with _ -> typ )
  in
  typ

(** The C++ type a read of record field [fld] has, out of a value of Core type
    [typ]: the field's declared type at the record's instantiation, stored as
    the record stores it.  [None] where [typ] is not a record naming [fld]. *)
let record_field_cpp_ty cx env typ fld : Cpp_ir.Lowered.Type.t option =
  match resolve_meta typ with
  | Core.Type.Global_app {head = r; type_arguments = args; _} -> (
    let declared =
      List.find_map
        (fun {Core.Record.Field.projection = f; type_ = ty} ->
          match f with
          | Some f when GlobRef.CanOrd.equal f fld -> Some ty
          | _ -> None )
        (Base.Table.record_field_bindings_of_type typ)
    in
    match declared with
    | Some core_ty -> (
      try
        Some
          (Types.cpp_ir_of_core_type cx env ~ns:(Core.Ref.User.Set.singleton r)
             (get_current_type_vars cx)
             (Base.Core_util.type_subst_list args core_ty))
      with e when CErrors.noncritical e -> None )
    | None -> None )
  | _ -> None

(** [recover_erased_scrutinee env ~is_magic typ expr] casts a scrutinee that is
    carried at runtime as [std::any] -- an existential witness, say -- back to
    [typ], the inductive recovered from the branch patterns.  Neither the
    [switch] of an enum match nor the [v()] of a variant match is applicable to
    a [std::any].  When [typ] itself erases there is nothing to recover to and
    the scrutinee is returned unchanged. *)
let recover_erased_scrutinee cx env ~is_magic typ (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  if not is_magic then expr
  else
    let cpp_ty = Types.cpp_of_core cx env typ in
    if Cpp_ir.Types.prints_as_any cpp_ty then expr else Cpp_passes.Erasure.unbox cpp_ty expr

(** Build the qualified constructor struct type for a pattern match branch.

    For [list<int>::Cons], this produces
    [Member (In_namespace (r, Entity_application (r, temps, \[\])), ctor_name)].
    Local inductives omit the namespace wrapper to avoid double qualification. *)
let ctor_type_of_match cx env (typ : Core.Type.t) (cname : GlobRef.t) : Cpp_ir.Lowered.Type.t =
  let ctor_name = ctor_struct_id_of_ref cname in
  match typ with
  | Core.Type.Global_app {head = r; type_arguments = tys; _} ->
    let tys = List.map type_simpl tys in
    let tys =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Base.Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* A class template has to be spelled with all of its arguments.
             The scrutinee's type can be short of them -- the body of an
             instance method is extracted against the class's erased carrier,
             so it carries none at all -- and what is missing is precisely
             what erased: [std::any], which is what the method's own
             signature spells for the same type. *)
          let tys = safe_firstn num_param_vars tys in
          tys
          @ List.init
              (max 0 (num_param_vars - List.length tys))
              (fun _ -> Core.Type.Unknown)
        | None -> tys )
      | _ -> tys
    in
    (* The constructor struct is nested in the instantiation, so it has to be
       qualified by the same one the declaration spells: an inductive's
       argument at the flat arity a stored value has (see
       {!Types.template_arg_of_core_type}). *)
    let temps =
      Types.ind_promoted_type_args cx r
      @ Tvars.apply_hkt_tyctors cx r (Types.template_params_of_core cx ~site:Declared env tys)
    in
    Member (inductive_type cx r temps [], ctor_name)
  | _ -> Named (ctor_name, [])

(** What a custom match over [t], annotated [typ], with branches [pv], knows
    about whether its scrutinee is boxed, as {!Match.gen_custom_cpp_case}
    decides it: [var_boxed i occ] says whether the variable read at [occ],
    of the binder at de Bruijn index [i], holds a box, [var_type] gives a
    binder's Core type.  Reads no binder itself. *)
type custom_scrutinee = {
  wrapped : bool;  (** a coercion that boxes *)
  cpp_erased : bool;  (** a variable whose binder holds a box *)
  magic : bool;  (** either, or a variable whose Core type erases to a box *)
  callee_ret_erased : bool;  (** a call whose declared codomain is a box *)
  typ : Cpp_ir.Lowered.Type.t;  (** the annotation, converted *)
  concrete : Cpp_ir.Lowered.Type.t;  (** the inductive the patterns recover, where [typ] erases *)
  pair : GlobRef.t option;  (** that inductive, when it is a pair *)
  pair_any_cast : bool;  (** the pair is read back as [pair<any, any>], every field a box *)
}

(** A spine read whole, through the coercions around its head. *)
let rec flatten_app = function
  | Core.Expr.Apply {callee = f; arguments = args} ->
    ( match flatten_app f with
    | Core.Expr.Apply {callee = f'; arguments = inner_args} ->
      flatten_app (Core.Expr.Apply {callee = f'; arguments = inner_args @ args})
    | f' -> Core.Expr.Apply {callee = f'; arguments = args} )
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    flatten_app e
  | other -> other

let custom_match_scrutinee cx env (typ : Core.Type.t) t pv ~var_boxed ~var_type =
  (* [scrut_is_magic]: true when the scrutinee is erased at runtime (stored as
     [std::any]) even though the Core term may carry a concrete type annotation.
     Covers both explicit [Obj.magic] wrappers and variables retyped to [Tany]
     by an outer [fix_a_fired] pair match (detected via its binder). *)
  let scrut_is_wrapped = match t with
    | Core.Expr.Coerce {source_type = from; target_type = into; _} ->
      Erasure.coercion_is_boxed cx env ~from ~into
    | Core.Expr.Boxed_value _ -> true
    | Core.Expr.Lambda_group_barrier _ -> false
    | _ -> false
  in
  let scrut_is_cpp_erased = match t with
    | Core.Expr.Bound_variable {index = i; occurrence = occ} -> var_boxed i occ
    | _ -> false
  in
  let scrut_is_magic = match t with
    | Core.Expr.Coerce {source_type = from; target_type = into; _} ->
      Erasure.coercion_is_boxed cx env ~from ~into
    | Core.Expr.Boxed_value _ -> true
    | Core.Expr.Lambda_group_barrier _ -> false
    | Core.Expr.Bound_variable {index = i; occurrence = occ} ->
      var_boxed i occ
      || (match var_type i with
          (* A Core type that erases on its own may still have been written
             down concretely here -- a typeclass carrier resolved by the
             instance being generated, say -- in which case the binder holds
             the value itself and there is no box to open. *)
          | Some ty ->
            is_erased_core_type ty
            && Erasure.core_erases_to_box cx env ty
          | None -> false)
    | _ -> false
  in
  (* [scrut_callee_ret_erased]: the scrutinee is a call to a global function
     ([Core.Expr.Apply (Core.Expr.Global {callee = r; _}, args)], possibly coercion-wrapped) whose
     DECLARED (un-instantiated) codomain resolves to [std::any] — e.g.
     [rev_tuple : forall xs, syms_semty xs -> syms_semty (rev xs)], a single
     C++ function generic over [xs], so its actual return type is the
     value-dependent-erased [syms_semty] regardless of how a specific
     call-site's Rocq type-checker happened to reduce the annotated result
     type (e.g. to a concrete [prod] when [xs] is a literal list). Using the
     call-site-reduced [typ] alone under-detects this: it looks concrete even
     though the callee only ever returns [std::any] at the C++ level. *)
  let scrut_callee_ret_erased =
    match flatten_app t with
    | Core.Expr.Apply {callee = Core.Expr.Global ({callee = r; _} as use); arguments = args} ->
      ( match callee_core_type cx r with
      | Some fty ->
        let fty = Base.Core_util.instantiate_written ~reader:"scrut_callee_ret_erased" use fty in
        ( match strip_arrows_n (count_real_core_args args) fty with
        | Some rty ->
          (* Both spellings of "is a [std::any] at run time" are needed here:
             [resolves_to_any_type] follows a named alias for the box, and
             [prints_as_any] catches the codomain a callee left as an erased
             type argument, which converts to a dummy glob rather than to
             [Tany]. *)
          let rty_cpp = Types.cpp_of_core cx env rty in
          Erasure.spells_as_any cx rty_cpp
        | None -> false )
      | None -> false )
    | _ -> false
  in
  let typ = Types.cpp_of_core cx env typ in
  (* [concrete_match_type]: when [typ] is erased ([std::any]), recover the
     actual inductive type from the first branch's pattern constructor and
     its field types.  Used for non-pair matches (e.g. option, variant) where
     we need to emit [any_cast<ConcreteType>(scrut)]. *)
  let concrete_match_type : Cpp_ir.Lowered.Type.t =
    if Erasure.spells_as_any cx typ || scrut_callee_ret_erased then
      try
        let {Core.Match.Branch.pattern = pat0; _} = pv.(0) in
        let ind_ref = match pat0 with
          | Core.Pattern.Constructor {constructor = GlobRef.ConstructRef (ip, _); _} -> GlobRef.IndRef ip
          | _ -> raise Not_found
        in
        let {Core.Match.Branch.binders = ids0; _} = pv.(0) in
        let tyargs = List.rev_map (fun (_, ty) ->
          Types.erase_unresolved_tvars (Types.cpp_of_core cx env ty)
        ) ids0 in
        Entity_application (ind_ref, tyargs, [])
      with _ -> typ
    else typ
  in
  let pair_g_opt = match concrete_match_type with
    | Entity_application (g, _, _) when is_prod_global g -> Some g
    | _ -> None
  in
  let scrut_is_trivial_core = match t with
    | Core.Expr.Bound_variable _
    | Core.Expr.Coerce {value = Core.Expr.Bound_variable _; _}
    | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable _; _}
    | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable _; _} -> true
    | _ -> false
  in
  let needs_pair_any_cast =
    pair_g_opt <> None &&
    ( scrut_is_cpp_erased || scrut_is_wrapped || scrut_callee_ret_erased
      || (scrut_is_magic && Cpp_ir.Types.prints_as_any typ)
      (* Read off the type only where nothing says otherwise: a variable
         is boxed exactly when its binder is ([scrut_is_magic]), and one
         declared [pair<std::any, exp<std::any>>] holds that pair. *)
      || (not scrut_is_trivial_core)
         && (is_all_erased typ || Types.resolves_to_any_type cx typ) &&
         ( Base.Type_util.has_tany_in_type concrete_match_type
           || (match concrete_match_type with
               | Entity_application (_, args, _) -> List.exists (Types.resolves_to_any_type cx) args
               | _ -> false) ) )
  in
  {
    wrapped = scrut_is_wrapped;
    cpp_erased = scrut_is_cpp_erased;
    magic = scrut_is_magic;
    callee_ret_erased = scrut_callee_ret_erased;
    typ = typ;
    concrete = concrete_match_type;
    pair = pair_g_opt;
    pair_any_cast = needs_pair_any_cast;
  }

(** The pattern variables [ids] (innermost first) of a custom match's branch
    matching [r], at the types they are bound at: every one that is not a box
    or a list retyped as erased where the pair is read back as
    [pair<any, any>] ([fix_a_fired]), then recovered from the scrutinee's own
    type [scrut_core_typ] and retyped for the dependent parameters of [core_typ],
    the match's annotation. *)
let custom_branch_binders cx env ~fix_a_fired ~scrut_core_typ ~core_typ r ids' =
  let ids' =
    if fix_a_fired then
      List.map (fun (x, ty) ->
        let cpp_ty = Types.cpp_of_core cx env ty in
        match cpp_ty with
        | Entity_application (g, (_ :: _), _) when is_prod_global g ->
          (x, Core.Type.Erased Core.Erasure_reason.Type_argument)
        | Entity_application (g, _, _) when is_list_global g ->
          (x, ty)
        | _ when Cpp_ir.Types.prints_as_any cpp_ty ->
          (x, ty)
        | _ ->
          (x, Core.Type.Erased Core.Erasure_reason.Type_argument))
        ids'
    else ids'
  in
  let ids' = recover_pattern_var_types_from_scrutinee ~ctor:r scrut_core_typ ids' in
  let ids' = retype_dependent_params core_typ ids' in
  ids'
