(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type conversion for translation: MiniML types to C++ types, erasure and
    boxing judgements, the C++ types binders are assigned, template arguments,
    and coercions between representations.  Reaches expression generation
    only through {!type_term_arg}. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Translation_support

(** [promoted_var_binding var_id] -- what the scope says the promoted variable
    named [var_id] stands for, by name.  Reached from a globref through
    {!promoted_var_resolution}, and by name alone where only the name survives
    -- see {!Table.ind_promoted_params}. *)
let promoted_var_binding var_id =
  let r = Option.map snd
    (List.find_opt
       (fun (n, _) -> Id.equal n var_id)
       (!tctx).promoted_var_map ) in
  r

(** [ind_promoted_type_args g] -- the leading template arguments a mention of
    the type [g] passes for the promoted variables its definition names.  [g]
    is an inductive, whose payloads name them, or a type-level [Definition],
    whose body does.

    Such a variable is a type the definition does not own: it belongs to
    whichever instance was in scope where it was declared, so it is a
    parameter there (see {!Table.promoted_type_params} and its uses in
    [Cpp_ind] and [Gen_decls.gen_type_alias]) and an argument at every use.  Inside the inductive's own
    declaration the argument is that parameter, which is what the [Tpromoted]
    fallback spells; a scope that knows no instance spells the file-scope
    alias, as it did before there was a parameter at all. *)
let ind_promoted_type_args g =
  List.map
    (fun v ->
      match promoted_var_binding v with Some t -> t | None -> Tpromoted v )
    (Table.promoted_type_params g)

(** Strip the const/reference decoration a parameter type carries, leaving the
    type of the value the binder denotes.  [const auto &] assigns [Tauto]:
    a deduced parameter is never physically a box. *)
let rec strip_param_wrappers = function
  | Tref (_, t) | Tconst t -> strip_param_wrappers t
  | t -> t

(** Whether the binder at de Bruijn index [i] was typed by a pattern match.
    A binding-site assignment does not overwrite such an entry: the
    instantiation the branch pinned down is the more precise of the two. *)
let pinned_by_pattern i =
  match IntMap.find_opt i (!tctx).cpp_binder_types with
  | Some (_, Bpattern) -> true
  | _ -> false

(** [recover_carrier_result ~fun_ty ~n_args ~want expr] converts a call whose
    declared result is a carrier applied to a type variable -- [M A], a
    {!Miniml.Tapp} -- into the same carrier at the element the position means.

    A dictionary stores its methods monomorphically, so such a result comes
    back at the erased element whatever the call's own arguments were, and only
    an elementwise conversion gets from [M<std::any>] to [M<Nat>].  [fun_ty] is
    the callee's ML function type, or [None] where the caller knows the
    question does not arise. *)
let recover_carrier_result ~fun_ty ~n_args ~want expr =
  let carrier_result =
    match Option.map (ml_codomain_after n_args) fun_ty with
    | Some (Some (Miniml.Tapp _)) -> true
    | _ -> false
  in
  match want with
  (* A reified monadic carrier is a [shared_ptr], not a container: it has no
     elements to walk, and getting from one element type to another is the
     reification path's business, not a cast's. *)
  | Some (Tshared_ptr _) -> expr
  | Some want when carrier_result && not (prints_as_any want) ->
    CPPcontainer_cast (want, expr, false)
  | _ -> expr

(** The C++ type the binder at de Bruijn index [i] was decided to have: the
    instantiation a pattern match pinned down where there is one, and
    otherwise the type assigned where the binder was bound. *)
let binder_cpp_type i =
  Option.map fst (IntMap.find_opt i (!tctx).cpp_binder_types)

(** Wrap [expr] in the [crane_erase_fn] runtime helper, flagging the header
    that the helper is needed. *)
let wrap_crane_erase_fn ?ret_ty expr =
  CPPerase_fn (ret_ty, expr)

(** Re-instantiate a function value that is being adapted for an erased slot:
    the values it will be applied to reached that slot erased too -- a
    [list nat] argument is stored as [List<std::any>], not [List<uint64_t>] --
    so the function has to be taken at the erased instantiation, or the
    adapter would unbox to a shape nothing ever boxed. *)
let erased_fn_instantiation = function
  | CPPglob (g, (_ :: _ as tys), xs) ->
    CPPglob (g, List.map (fun _ -> Tany) tys, xs)
  | e -> e

(** [adapter_params ~prefix dom] -- fresh parameters for an adapter lambda,
    one per domain type, in source order.

    An adapter is a lambda whose only job is to call something else with its
    own arguments passed along, so its parameters exist only to be named.
    [prefix] distinguishes the adapters from one another in the generated
    code, and is the caller's to choose. *)
let adapter_params ~prefix dom =
  List.mapi
    (fun i ty -> (ty, Some (Id.of_string (Printf.sprintf "%s%d" prefix i))))
    dom

(** An {!adapter_params} parameter read back as the argument to pass along. *)
let adapter_arg (_, id) = CPPvar (Option.get id)

(** Strip [MLmagic] wrappers recursively — [MLmagic] is a transparent coercion
    in the ML AST and should be ignored by numeral-folding traversals. *)
let rec strip_magic = function MLmagic (_, e) -> strip_magic e | e -> e

(** Whether a position has stated a type concrete enough to recover a box into.
    A slot spelled [std::any] wants the box as it stands, and one still spelled
    as a template parameter has not been stated at all: an [any_cast] there
    would be a guess about an instantiation this site cannot see. *)
let states_unboxed_target into = not (prints_as_any into || contains_tvar into)

(** [inline_iife k expr] checks whether [expr] is an IIFE
    ([CPPfun_call(CPPlambda
      { cl_params = \[\];
        cl_body = body;
        _ }, \[\])]).  If so, it replaces
    the final [Sreturn(Some v)] in [body] with [k v] and returns the
    inlined statement list.  Otherwise it falls back to [\[k expr\]].

    Only zero-argument, zero-parameter IIFEs are inlined — parameterised
    lambdas and those with explicit return-type annotations involving
    captures are left untouched, since they may have name-scoping or
    type-deduction side-effects.

    @param k     the statement-level continuation (e.g. [Sreturn], [Sasgn])
    @param expr  the expression produced by [gen_expr] *)
let inline_iife (k : cpp_expr -> cpp_stmt) = function
  | CPPfun_call (_, CPPlambda
    { cl_params = {rev = []};
      cl_ret = ret_ty;
      cl_body = body;
      _ }, {rev = []})
    when body <> [] ->
    let k_is_return =
      match k (CPPint 0) with Sreturn _ -> true | _ -> false
    in
    if not k_is_return then
      (* Non-return continuations (e.g. Sasgn for let-bindings) keep the
         IIFE to prevent name clashes between variables from separately
         inlined IIFEs in the same block scope. *)
      [k (mk_iife ret_ty body)]
    else
    (* Replace each [Sreturn(Some v)] in the IIFE body with [k(v)] and
       emit the body statements directly, eliminating the lambda wrapper.

       Since k is guaranteed to produce [Sreturn], inlining into
       [Sswitch] and [Scustom_case] is safe — [return] preserves the
       "exit the enclosing case" semantics.  [Sif] is always safe
       because if/else branches are mutually exclusive. *)
    let map_all_or_none transform branches =
      let results = List.map transform branches in
      if List.for_all (fun x -> x <> None) results then
        Some (List.filter_map Fun.id results)
      else None
    in
    let rec replace_last_return = function
      | [Sreturn (Some v)] -> Some [k v]
      | [Sreturn None] -> None  (* void return — cannot apply k *)
      | [Sif (c, then_br, else_br)] ->
        ( match (replace_last_return then_br, replace_last_return else_br) with
        | Some then_br', Some else_br' -> Some [Sif (c, then_br', else_br')]
        | _ -> None )
      | [Sswitch (scrut, ind_ref, branches, default)] ->
        let default' =
          match default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (id, stmts) ->
              Option.map (fun stmts' -> (id, stmts')) (replace_last_return stmts))
            branches, default')
        with
        | Some branches', Some default' -> Some [Sswitch (scrut, ind_ref, branches', default')]
        | _ -> None )
      | [Scustom_case (ty, scrut, tyargs, branches, cmatch)] ->
        Option.map
          (fun branches' -> [Scustom_case (ty, scrut, tyargs, branches', cmatch)])
          (map_all_or_none
            (fun (args, bty, stmts) ->
              Option.map (fun stmts' -> (args, bty, stmts')) (replace_last_return stmts))
            branches)
      | [Smatch (scrut, branches, default)] ->
        let default' =
          match default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun br ->
              Option.map (fun body' -> { br with smb_body = body' }) (replace_last_return br.smb_body))
            branches, default')
        with
        | Some branches', Some default' ->
          Some [Smatch (scrut, branches', default')]
        | _ -> None )
      | stmt :: rest when rest <> [] ->
        Option.map (fun rest' -> stmt :: rest') (replace_last_return rest)
      | _ -> None
    in
    ( match replace_last_return body with
    | Some stmts -> stmts
    | None -> [k (mk_iife ret_ty body)] )
  | expr -> [k expr]

(** The C++ type a position is being generated into: what it states
    ([expected], a generator's [?expected_ty]), and where it states nothing,
    the enclosing function's return type -- which a tail position lands in.
    The one place that precedence is written down, so that "the type this
    position expects" cannot mean the position at one site and the enclosing
    return type at another. *)
let position_cpp_ty (expected : cpp_type option) =
  match expected with
  | Some _ as t -> t
  | None -> (!tctx).current_cpp_return_type

(** A callable handed to a parameter the callee declared at one of its own
    type variables has to arrive under a name: a closure's type cannot be
    spelled, so it can never agree with the same type variable as deduced
    from another argument -- [f (nat -> nat) S []], where the list argument
    settles the variable on [std::function<uint64_t(uint64_t)>].
    {!Minicpp.CPPfn_value} gives the closure that very type, deduced from it.

    The parameter type must be the callee's own, before this call site's
    instantiation is substituted into it: it is the template parameter that
    C++ has to deduce, not what it should deduce to. *)
let name_fn_arg_for_tvar_param param_ml_ty expr =
  match (resolve_tmeta param_ml_ty, expr) with
  | (Miniml.Tvar (_, _)), CPPlambda _ -> CPPfn_value expr
  | _ -> expr

(** Whether [expr] is a pair recovered from a box, i.e. one whose [any_cast]
    named the erased shape [pair<any, any>] and whose components are therefore
    boxes in their own right. *)
let reads_recovered_pair = function
  | CPPany_cast (Tglob (g, args, _), _)
  | CPPany_cast_tolerant (Tglob (g, args, _), _) ->
    is_prod_global g && args <> [] && List.for_all prints_as_any args
  | _ -> false

(** [yields_boxed_component expr] -- whether [expr] reads a component out of a
    pair that was itself recovered from a box, and so hands back a
    [std::any] however concrete its ML type looks.

    A boxed pair stores each component separately boxed, so recovering it
    lands on [pair<any, any>] and [.first] on that is still a box.  The
    accessor path in {!gen_expr_custom} builds exactly this shape, and the
    let-binding and tail-position paths ask here rather than being told out of
    band: the emitted expression is the evidence, so no flag has to be
    threaded from producer to consumer. *)
let yields_boxed_component = function
  | CPPfun_call (_, CPPglob (_, _, Some ci), {rev = [arg]}) when reads_recovered_pair arg ->
    (match inline_shape ci with Some (Inline_pair_projection _) -> true | _ -> false)
  (* The accessor is not always a custom-inline call: a projection out of a
     [std::pair] is a plain member read, and that is the same evidence. *)
  | CPPaccess (Adot, arg, _) -> reads_recovered_pair arg
  | _ -> false

(** [subst_dict_carrier carrier ty] puts [carrier] in place of the leading
    class parameter throughout [ty].  A class parameter stands in a method's
    own types as [Tapp (1, _)] -- the carrier applied -- and the call's type
    arguments instantiate the method's [forall]s, not the class's, so without
    this substitution a parameter declared [m A] resolves to nothing at all.

    [carrier] is a type constructor written as an application whose
    placeholders stand for what it is applied to, so applying it is filling
    them -- which is what {!Mlutil.apply_ml_type} does, including for the
    type-level lambda [fun T => holder T (box T)] whose binder occurs twice.

    An occurrence that cannot be filled is left as the [Tapp] it was: a type of
    the wrong arity in its place is worse than an unrecovered one, which is
    only a missed opportunity. *)
let subst_dict_carrier ?(at = 1) carrier ty =
  let apply k xs =
    match carrier with
    | Miniml.Tglob _ -> Mlutil.apply_ml_type carrier xs
    | _ -> Miniml.Tapp (k, xs)
  in
  let rec go t =
    match resolve_tmeta t with
    | Miniml.Tapp (j, xs) when j = at -> apply j (List.map go xs)
    | Miniml.Tapp (j, xs) -> Miniml.Tapp (j, List.map go xs)
    | Miniml.Tglob (c, a, l) -> Miniml.Tglob (c, List.map go a, l)
    | Miniml.Tarr (a, b) -> Miniml.Tarr (go a, go b)
    | t -> t
  in
  go ty

(** The carrier a call's dictionary argument fixes, as an ML type.

    The dictionary reaches the call wrapped in the adapter lambda that erases
    its arguments, so the instance is found by descending to the head of the
    lambda's body.  It need not be an instance at all: where the enclosing
    function abstracts over the instance, the dictionary is a binder, and the
    carrier is written in the constraint that binder's own type spells.  Both
    sources end at an ML type headed by the carrier, and are consumed as one. *)
let dict_carrier_ml_type id args =
  let ( let* ) = Option.bind in
  let* ml_ty = find_type_opt id in
  (* The class parameter is quantified first, and an explicit argument list is
     positional, so only a leading carrier can be written.

     The position wanted is into the {e arguments}, which is not the position
     in the domain list: an erased domain takes no argument.  A class method
     quantifies its own [forall]s before the class, so counting domains would
     land past the dictionary -- [tfmap]'s class domain is second but its
     dictionary is the first argument. *)
  let* i, cls =
    let rec find i = function
      | [] -> None
      | d :: ds -> (
        match resolve_tmeta d with
        | Miniml.Tglob (c, [arg], _)
          when ( match resolve_tmeta arg with
               | Miniml.Tapp (1, _) -> true
               | _ -> false ) ->
          Some (i, c)
        | Miniml.Tdummy _ -> find i ds
        | _ -> find (i + 1) ds )
    in
    find 0 (ml_domains ml_ty)
  in
  let* dict = List.nth_opt args i in
  (* The class applied to one argument {e is} the carrier, already applied:
     a MiniML type has no way to hold a constructor that is not.  Both sources
     below may land on it -- a binder's type is the constraint itself, and a
     dictionary that is a record value has the class as its own type -- so
     both go through this one step. *)
  let strip_class t =
    match t with
    | Miniml.Tglob (c, [arg], _) when Environ.QGlobRef.equal (Global.env ()) c cls -> resolve_tmeta arg
    | t -> t
  in
  (* Two sources, one consumer.  A dictionary that {e is} a named instance
     says what its carrier is through the method it defines; a dictionary that
     is a binder -- the enclosing function abstracting over the instance --
     says so through the constraint its own type spells.  Both end at an ML
     type whose head is the carrier and whose last argument is the one the
     carrier varies in. *)
  (* A dictionary-producing global abstracts over the class parameters of the
     instances it is built from: [TFunctor_holder] takes a [TFunctor FnBody]
     and returns the traversal of [fun T => holder T (FnBody T)].  Its
     codomain names [FnBody] as a [Tapp], and what stands for it is whatever
     dictionary the call supplies.  Paired here as (argument position, type
     variable), the positions counted over arguments rather than domains for
     the reason above. *)
  let class_params ty =
    let rec go i acc = function
      | [] -> List.rev acc
      | d :: ds -> (
        match resolve_tmeta d with
        | Miniml.Tdummy _ -> go i acc ds
        | Miniml.Tglob (_, [arg], _) -> (
          match resolve_tmeta arg with
          | Miniml.Tapp (k, _) -> go (i + 1) ((i, k) :: acc) ds
          | _ -> go (i + 1) acc ds )
        | _ -> go (i + 1) acc ds )
    in
    go 0 [] (ml_domains ty)
  in
  let rec head_glob = function
    | Miniml.MLlam (_, _, b) | Miniml.MLmagic (_, b) | Miniml.MLapp (b, _) ->
      head_glob b
    | Miniml.MLglob (r, _) -> Some r
    | _ -> None
  in
  (* [depth] counts the binders descended through to reach the term in hand.
     The dictionary arrives wrapped in the adapter lambda that erases its
     arguments, so a dictionary that is a binder of the enclosing declaration
     is spelled at an index shifted by that lambda's own parameters, while the
     environment those indices are resolved against does not have them.  Left
     unshifted, the first dictionary of a class context reads past the end and
     the second reads the first one's constraint -- so the carriers of two
     sibling traversals come out crossed rather than merely missing, which is
     the shape that made this findable. *)
  let rec dict_ml_type ?(depth = 0) = function
    | Miniml.MLlam (_, _, b) -> dict_ml_type ~depth:(depth + 1) b
    | Miniml.MLmagic (_, b) -> dict_ml_type ~depth b
    | Miniml.MLapp (b, dicts) as tm ->
      (* The head's codomain still names its own class parameters; the
         dictionaries it is applied to are what say which carriers those are.
         Without this the generic instance's binder is what gets written, and
         at a site with no binder in scope it does not even name anything. *)
      let* cod = dict_ml_type ~depth b in
      let params =
        match Option.bind (head_glob tm) find_type_opt with
        | Some ty -> class_params ty
        | None -> []
      in
      Some
        (List.fold_left
           (fun acc (p, k) ->
             match Option.bind (List.nth_opt dicts p) (dict_ml_type ~depth) with
             | Some carrier -> subst_dict_carrier ~at:k carrier acc
             | None -> acc )
           cod params )
    | Miniml.MLglob (r, _) ->
      (* The instance's method returns [T1] applied: [TFunctor_box]'s codomain
         is [box B]. *)
      Option.map (fun t -> resolve_tmeta (ml_codomain t)) (find_type_opt r)
    | Miniml.MLrel i ->
      let i = i - depth in
      let constraint_arg t =
        match Option.map resolve_tmeta t with
        | Some (Miniml.Tglob (_, [_], _) as t) -> Some (strip_class t)
        | _ -> None
      in
      let recorded = constraint_arg (get_env_type_opt i) in
      ( match recorded with
      | Some _ -> recorded
      | None ->
        (* The recorded type can be gone: a class with a single field is
           inlined to that field, so the binder is remembered as the method's
           own arrow and the class it came from is nowhere in it.  The
           enclosing declaration still spells the constraint, and while the
           body is under nothing but that declaration's own binders, the two
           lists are the same list read from opposite ends. *)
        let ( let* ) = Option.bind in
        let* r = !Table.current_decl_ref in
        let* decl_ty = find_type_opt r in
        let doms = ml_domains decl_ty in
        let n = List.length (!tctx).env_types in
        (* [List.nth_opt] raises rather than answering [None] on a negative
           index, and [i] can exceed [n]: a dictionary reached through an
           argument of the call need not be a binder of this body at all. *)
        if n <> List.length doms || i > n || i <= 0 then None
        else constraint_arg (List.nth_opt doms (n - i)) )
    | _ -> None
  in
  Option.map strip_class (dict_ml_type dict)

(** [ty], global [id]'s declared type, as a call with type arguments [tys] and
    value arguments [value_args] instantiates it.  [tys] instantiates the
    callee's own [forall]s; a class parameter is not among them, and stands in
    every type as the carrier applied -- so the dictionary argument has to be
    read first, or a [bind]'s [m A] resolves to nothing: erased, where the
    type argument written for it is a dummy. *)
let instantiate_at_call id tys value_args ty =
  let ty =
    match dict_carrier_ml_type id value_args with
    | Some carrier -> subst_dict_carrier carrier ty
    | None -> ty
  in
  try type_subst_list tys ty with _ -> ty

(** What an application of a global yields, as an ML type.

    The callee's declared type says it, once instantiated the way the call
    instantiates it: [tys] for its own [forall]s, and the dictionary argument
    for the class parameter its parameter types spell as the carrier applied.
    That is the same pair of substitutions {!gen_app}'s [subst_ml_ty] makes,
    read at the codomain instead of at a domain.

    [None] where the callee has no recorded type, or fewer value arrows than
    the call has value arguments -- a partial application returns a function,
    which is not what the callers of this want. *)
let ml_app_result_type (f : ml_ast) (args : ml_ast list) : ml_type option =
  let ( let* ) = Option.bind in
  match f with
  | MLglob (id, tys) ->
    let value_args =
      List.filter (function MLdummy _ -> false | _ -> true) args
    in
    let* ty = find_type_opt id in
    Ml_type_util.ml_codomain_after (List.length value_args)
      (instantiate_at_call id tys value_args ty)
  | _ -> None

(** The binder a match scrutinee names, seen through the wrappers that leave
    the value alone: a magic cast, and a dependent instantiation.  A payload
    whose type is written [P x] appears applied to its witness, but a binder
    of non-function type is no callable: the application names the binder
    itself, and that is where the value's C++ type was pinned down. *)
let rec scrutinee_binder = function
  | MLrel i -> Some i
  | MLmagic (_, e) -> scrutinee_binder e
  | MLapp (h, _) when not (scrutinee_head_is_callable h) ->
    scrutinee_binder h
  | _ -> None

(** Whether a term in head position really is a function being applied, as
    opposed to a binder that a dependent type spells applied to its index. *)
and scrutinee_head_is_callable h =
  match scrutinee_binder h with
  | Some i ->
    let rec is_arrow = function
      | Miniml.Tmeta {contents = Some t} -> is_arrow t
      | Miniml.Tarr _ -> true
      | _ -> false
    in
    (match get_env_type_opt i with Some t -> is_arrow t | None -> true)
  | None -> true

(** Test whether a C++ expression is "trivial" — a simple variable or member
    access that can safely be duplicated without side effects.  Non-trivial
    expressions (function calls, constructor applications, etc.) should be
    cached in a temporary when the custom match template uses [%scrut] more
    than once. *)
let is_trivial_scrut = function
  | CPPvar _ | CPPget _ | CPPget' _ | CPPaccess _
  | CPPscope _ | CPPqualified_t _ | CPPderef _ | CPPenum_val _
  | CPPglob _ -> true
  | _ -> false

(** The C++ type a pattern match pinned down for the binder at de Bruijn index
    [i], if this branch pinned one.  A binding-site assignment is not an
    answer here: it says what the binder's ML type converts to, which for a
    field read out of an erased carrier is the type the value {e would} have
    had, not the [std::any] it is actually stored as. *)
let pattern_binder_type i =
  match IntMap.find_opt i (!tctx).cpp_binder_types with
  | Some (t, Bpattern) -> Some t
  | _ -> None

(** Generate a custom match body using user-provided custom extraction syntax.
    Wraps the body in a lambda with pattern-bound variables. *)
let rec collect_recursive_ns ml_ty =
  (* Collect self-recursive inductive types that appear *nested inside* ml_ty
     and return them as a namespace set so convert_ml_type_to_cpp_type wraps
     them with Tshared_ptr when they appear as field references.

     The top-level type itself is NOT added: a binding variable h : T has the
     same C++ type as the deque element (e.g. `const T&` from `front()`), not
     `shared_ptr<T>`.  Recursive wrapping is only needed when T appears as a
     *field* of an enclosing composite type (e.g. `pair<string, json_value>`
     → field `json_value` wrapped as `shared_ptr<json_value>`). *)
  let rec collect_nested acc = function
    | Miniml.Tglob (GlobRef.IndRef _ as g, args, _) ->
      let acc' =
        if Table.has_recursive_fields g && not (Table.is_custom g)
        then Refset'.add g acc
        else acc
      in
      List.fold_left collect_nested acc' args
    | Miniml.Tarr (a, b) -> collect_nested (collect_nested acc a) b
    | Miniml.Tmeta {contents = Some t} -> collect_nested acc t
    | _ -> acc
  in
  (* Start from the args of the top-level type so the top-level itself
     is never added to the namespace. *)
  match ml_ty with
  | Miniml.Tglob (_, args, _) ->
    List.fold_left collect_nested Refset'.empty args
  | Miniml.Tarr (a, b) ->
    collect_nested (collect_nested Refset'.empty a) b
  | Miniml.Tmeta {contents = Some t} -> collect_recursive_ns t
  | _ -> Refset'.empty

(** [convert_ml_type_to_cpp_type] only resolves [Tvar] indices within
    [tvars]; anything out of range comes back as [Tvar (Tv_index (_, None))], which
    prints as a bogus, undeclared template parameter name (e.g. "T3").
    Normalize those to [Topaque]: the variable was quantified somewhere we
    cannot see, so [std::any] is the only spelling available, but nothing here
    establishes that the value is actually boxed. *)
let rec erase_unresolved_tvars = function
  | Tvar (Tv_index (_, None)) -> Topaque
  | Tglob (g, ts, es) -> Tglob (g, List.map erase_unresolved_tvars ts, es)
  | Tfun (dom, cod) ->
    Tfun (List.map erase_unresolved_tvars dom, erase_unresolved_tvars cod)
  | Tshared_ptr t -> Tshared_ptr (erase_unresolved_tvars t)
  | Tref (k, t) -> Tref (k, erase_unresolved_tvars t)
  | t -> t

(** Extract block template info from an inline custom expression.
    Returns [Some(ref, template, args, tyargs)] if the expression is
    an inline custom whose template contains [%result]. *)
let extract_block_template = function
  | CPPglob (ref, tys, Some ci) -> begin
    match ci.ci_inline with
    | Some {it_form = Block_iife; it_text = tmpl; _} ->
      Some (ref, tmpl, [], tys)
    | _ -> None
    end
  | CPPfun_call (_, CPPglob (ref, tys, Some ci), args) -> begin
    match ci.ci_inline with
    | Some {it_form = Block_iife; it_text = tmpl; _} ->
      Some (ref, tmpl, call_args args, tys)
    | _ -> None
    end
  | _ -> None

(** Whether the statements a let-binding's right-hand side generated assign a
    value that is really a box.  The right-hand side is generated as an
    assignment, so the bound value is the one expression in it. *)
let stmts_yield_boxed = function
  | [Sasgn (_, _, v)] -> yields_boxed_component v
  | _ -> false

let fixpoint_escapes_in_stmts target_id stmts =
  let rec check_expr e =
    match e with
    | CPPfun_call (_, CPPvar id, args) when Id.equal id target_id ->
      (* Safe: direct call.  But check the arguments for escapes. *)
      List.exists check_expr (to_reversed args)
    | CPPvar id when Id.equal id target_id ->
      true  (* Escape: bare reference outside call position *)
    | CPPlambda {cl_body = body; cl_capture = Immediate; _} ->
      (* Runs where it is written, so a call in it is a call here. *)
      check_stmts body
    | CPPlambda {cl_body = body; cl_capture = Closure; _} ->
      (* A closure may outlive the fixpoint's scope, so any reference in it
         -- even a call -- is an escape: the closure would copy a fixpoint
         whose own captures are references into that scope.  Must use a
         properly recursive walker since map_expr/map_stmt only do one level
         of descent. *)
      let rec has_var_in_expr e =
        match e with
        | CPPvar id when Id.equal id target_id -> true
        | _ ->
          let found = ref false in
          let fe e' = if not !found then found := has_var_in_expr e'; e' in
          let fs s' = if not !found then found := has_var_in_stmt s'; s' in
          ignore (Minicpp.map_expr fe fs Fun.id e);
          !found
      and has_var_in_stmt s =
        let found = ref false in
        let on_expr e = if not !found then found := has_var_in_expr e in
        let on_stmts ss =
          if not !found then found := List.exists has_var_in_stmt ss
        in
        Minicpp.iter_stmt_children ~on_expr ~on_stmts s;
        !found
      in
      List.exists has_var_in_stmt body
    | _ ->
      (* Recurse into sub-expressions *)
      let found = ref false in
      let fe e = if not !found then found := check_expr e; e in
      ignore (Minicpp.map_expr fe Fun.id Fun.id e);
      !found
  and check_stmt s =
    let found = ref false in
    let on_expr e = if not !found then found := check_expr e in
    let on_stmts ss = if not !found then found := check_stmts ss in
    Minicpp.iter_stmt_children ~on_expr ~on_stmts s;
    !found
  and check_stmts ss = List.exists check_stmt ss
  in
  check_stmts stmts

(** [names_only_scoped_tvars ty] -- whether every type variable [ty] spells is
    one this scope declares.  A slot type read off a callee's signature is
    written in the callee's type variables, which name nothing here, so such a
    type cannot be used as the type a use site wants. *)
let names_only_scoped_tvars ty =
  let scope = current_scope_type_names () in
  List.for_all (fun id -> List.exists (Id.equal id) scope) (get_tvars ty)

(** [ty], where this scope can write it: every variable it names is in scope,
    and it is not erased. *)
let spell_in_scope ty =
  if names_only_scoped_tvars ty && not (prints_as_any ty) then Some ty else None

(** The variable {!Gen_decls.relax_tt_applied_return} takes out of [id]'s
    template head, if any: the higher-kinded head of an applied codomain that
    only a callback's result otherwise names -- [case_]'s [M] in [M X], which
    the declaration spells [std::invoke_result_t<F0 &, ...>] instead.  Read off
    the Rocq type for the reason {!writable_tvar_count} is. *)
let relaxed_tt_return_var id =
  match find_type_opt id with
  | None -> None
  | Some ml_ty -> (
    match resolve_tmeta (ml_codomain ml_ty) with
    | Miniml.Tapp (h, [ _ ])
      when IntSet.mem h (declared_higher_kinded_tvars ml_ty) ->
      let occurs t = IntSet.mem h (collect_tvars_set IntSet.empty t) in
      let doms = List.map resolve_tmeta (ml_domains ml_ty) in
      (* A callback's result, written as an arrow; a definitional class
         spells its variable in the declaration's parameter list and so names
         it ([MonadIter<T1>]). *)
      let under_arrow d =
        match d with Miniml.Tarr _ -> true | _ -> false
      in
      if
        List.for_all (fun d -> under_arrow d || not (occurs d)) doms
        && List.exists (fun d -> under_arrow d && occurs d) doms
      then Some h
      else None
    | _ -> None )

(** How many template parameters [id]'s declaration has room for.

    A call can hold more type arguments than the callee has parameters: Rocq
    counts every variable the definition quantified, C++ only those the
    converted signature can mention.  A variable no converted type mentions
    never became a parameter -- the erased [itree] index of [h AE AE nat] is
    the case -- and an argument written for it overruns the list.  Recomputed
    from [id]'s type rather than recorded, for the same reason
    {!phantom_prefix_args} recomputes its own: a call can precede its callee's
    declaration. *)
let declared_tvar_count id =
  match find_type_opt id with
  | None -> None
  | Some ml_ty -> Some (Mlutil.type_maxvar (type_simpl ml_ty))

(** [targs] without the position {!relaxed_tt_return_var} names, where the list
    is still indexed by kept position. *)
let drop_relaxed_tt_position id targs =
  match (relaxed_tt_return_var id, declared_tvar_count id) with
  | Some h, Some n ->
    let kept =
      kept_type_arg_positions id n
    in
    let rec index k = function
      | [] -> None
      | i :: rest -> if i = h then Some k else index (k + 1) rest
    in
    ( match index 0 kept with
    | Some k when k < List.length targs ->
      List.filteri (fun i _ -> i <> k) targs
    | _ -> targs )
  | _ -> targs

(** The Rocq type-variable positions a call may still write, given that the
    declaration reorders some of them out of reach.

    {!Gen_decls.relax_applied_return} handles a variable named only by the
    return type -- C++ deduces nothing from a return type -- by giving it the
    producing callback's result as its default and moving it {e last}, since a
    default may only name parameters declared before it.  That pass records
    "nothing supplies this signature's arguments explicitly, so the order is
    free", and for a lifted helper that is true.  For a class method it is not:
    [tfmap] is called with its Rocq arguments written out.

    Once such a variable has moved, every position from it onwards is
    unreachable positionally -- reaching it would mean spelling the synthesised
    callable parameter that now precedes it, which is deduced and has no Rocq
    argument to spell.  So the writable prefix ends there.

    The condition is read off the Rocq type rather than the emitted
    declaration, which a call site cannot consult ({!Table.census}'s rule that
    discovery decides and emission reads): the variable occurs in the
    codomain, and every domain occurrence of it is under an arrow -- that is,
    it is a callback's result, which is exactly the parameter the declaration
    collapses to a deduced callable and stops naming. *)
let writable_tvar_count id =
  let ( let* ) o f = match o with None -> None | Some x -> f x in
  let* n = declared_tvar_count id in
  let* ml_ty = find_type_opt id in
  let occurs v t = IntSet.mem v (collect_tvars_set IntSet.empty t) in
  let cod = resolve_tmeta (ml_codomain ml_ty) in
  (* Only a codomain that {e applies} a variable is relaxed.  [list B] names
     [B] as a plain leading parameter that the call still has to write, and
     dropping it would leave nothing to deduce it from; [T V] is the
     higher-kinded shape {!Gen_decls.relax_applied_return} rewrites. *)
  (* And only a higher-kinded head: a family's application is written plain,
     which the declaration does not relax ({!Gen_decls.relax_applied_return}). *)
  let applied_cod =
    match cod with
    | Miniml.Tapp (h, _) ->
      IntSet.mem h (Ml_type_util.higher_kinded_ml_tvars [ml_ty])
    | _ -> false
  in
  let derived v =
    applied_cod && occurs v cod
    && List.for_all
         (fun d ->
           match resolve_tmeta d with
           | Miniml.Tarr _ -> true
           | d -> not (occurs v d) )
         (ml_domains ml_ty)
    && List.exists (fun d -> occurs v d) (ml_domains ml_ty)
  in
  (* Only a derived {e suffix} may be dropped.  A derived position followed by
     one that is still written cannot be removed without taking that one with
     it, and the later position may be doing work the truncation would undo --
     [iter]'s [R] is derived but its [I] is not, and dropping both loses an
     argument deduction was relying on the first two to place.  Where the list
     cannot be fixed by cutting its tail, it is left exactly as it was. *)
  let rec suffix_start v = if v < 1 then 1 else if derived v then suffix_start (v - 1) else v + 1 in
  Some (suffix_start n - 1)

(** [targs] cut back to the prefix {!writable_tvar_count} says is reachable. *)
let truncate_to_writable id targs =
  match writable_tvar_count id with
  | Some n when n < List.length targs -> List.filteri (fun i _ -> i < n) targs
  | _ -> targs

(** [mk_arity_call ~params ~saturated args] applies a callee to [args], given
    in {e source} order, where the callee's declaration fixes its parameters
    to [params].  [saturated] builds the call, from exactly as many arguments
    as [params] has.

    A call site need not match that arity, and a flat call is wrong whichever
    way it misses.  Arguments past the arity apply to the call's {e result} --
    a binder instantiated at a function type, say -- rather than to the
    callee.  Arguments short of it leave a closure over the ones still to
    come, so the call is eta-expanded instead of emitted shorter than it is
    declared.

    Omit [params] where the declaration is not known: an empty list means a
    nullary callee, which is a different thing and applies every argument to
    the result. *)
let mk_arity_call ?params ~saturated args =
  match params with
  | None -> saturated args
  | Some params ->
  let arity = List.length params in
  let given = List.length args in
  if given > arity then
    mk_apply
      (saturated (List.filteri (fun i _ -> i < arity) args))
      (List.filteri (fun i _ -> i >= arity) args)
  else if given < arity then
    let waiting =
      adapter_params ~prefix:"_sat"
        (List.filteri (fun i _ -> i >= given) params)
    in
    mk_lambda waiting None
      [Sreturn (Some (saturated (args @ List.map adapter_arg waiting)))]
      ~capture:Closure
  else
    saturated args

(** Escape analysis for local fixpoint variables.

    Determines whether [target_id] appears in any position other than the
    callee of a direct call [CPPfun_call(CPPvar target_id, args)].  If so,
    the fixpoint "escapes" and must use the [shared_ptr<std::function>]
    pattern (see {!gen_local_fix_shared_ptr}) instead of the simpler [\[&\]]
    capture pattern (see {!gen_local_fix_by_ref}).

    Escape positions include: function argument, constructor field, return
    value, record field, or binding RHS.

    Lambda bodies are treated conservatively: {b any} reference to the
    fixpoint inside a lambda body — even in call position — counts as an
    escape.  This is because the lambda captures the [std::function] value,
    and a [\[&\]]-captured [std::function]'s internal lambda still holds
    dangling stack references when the lambda outlives the fixpoint's scope.

    @param target_id  The fixpoint variable to track.
    @param stmts      The statement list (typically the continuation after
                      the fixpoint's let-binding) to scan.
    @return [true] if the fixpoint escapes. *)
let fix_escapes_in_own_bodies renamed_ids funs_with_params =
  List.exists
    (fun (id, _) ->
      List.exists (fun (_, body) -> fixpoint_escapes_in_stmts id body) funs_with_params )
    renamed_ids

(** The inclusive range of a fixed-width C++ integer type, or [None] when the
    spelling is not one this compiler can bound (a user-defined bignum, say).
    Only the spellings a numeral mapping can name are listed; anything else is
    left unchecked rather than guessed at. *)
let cpp_integer_range = function
  | "bool" -> Some (Z.zero, Z.one)
  | "uint8_t" | "unsigned char" -> Some (Z.zero, Z.of_string "255")
  | "uint16_t" | "unsigned short" -> Some (Z.zero, Z.of_string "65535")
  | "uint32_t" | "unsigned" | "unsigned int" ->
    Some (Z.zero, Z.of_string "4294967295")
  | "uint64_t" | "size_t" | "unsigned long" | "unsigned long long" ->
    Some (Z.zero, Z.of_string "18446744073709551615")
  | "int8_t" | "signed char" -> Some (Z.of_string "-128", Z.of_string "127")
  | "int16_t" | "short" -> Some (Z.of_string "-32768", Z.of_string "32767")
  | "int32_t" | "int" ->
    Some (Z.of_string "-2147483648", Z.of_string "2147483647")
  | "int64_t" | "long" | "long long" | "ptrdiff_t" ->
    Some (Z.of_string "-9223372036854775808",
          Z.of_string "9223372036854775807")
  | _ -> None

(** Render a folded literal through a numeral mapping's format string.

    A numeral inductive is unbounded in Rocq but its C++ image usually is not,
    and the format string ([UINT64_C(%n)]) carries the value without checking
    it.  Emitting an out-of-range literal moves the failure to the C++
    compiler at best and wraps silently at worst, so refuse it here, where the
    Rocq definition responsible can still be named. *)
let render_numeral info (n : Z.t) : cpp_expr =
  let cpp_ty = Table.find_custom_opt info.Table.num_ind in
  ( match Option.bind cpp_ty cpp_integer_range with
  | Some (lo, hi) when Z.lt n lo || Z.gt n hi ->
    CErrors.user_err
      (Pp.(
         str "Crane: the literal " ++ str (Z.to_string n)
         ++ str " does not fit in " ++ str (Option.get cpp_ty)
         ++ str ", the C++ type "
         ++ Printer.pr_global info.Table.num_ind
         ++ str " extracts to."))
  | _ -> () );
  CPPnumeral (info.Table.num_ind, n)

(** Try to fold a binary positive chain [xI(xO(...xH...))] into an [int64].
    Returns [Some n] where [n > 0] if the entire chain can be folded, or
    [None] if any node is not a recognized positive constructor.
    Constructor indices (1-based): xI=[positive_xI_idx], xO=[positive_xO_idx],
    xH=[positive_xH_idx]. *)
let rec try_fold_positive expr : int64 option =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), []) when idx = positive_xH_idx ->
    Some 1L
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) when idx = positive_xI_idx ->
    Option.map (fun n -> Int64.add (Int64.mul 2L n) 1L) (try_fold_positive inner)
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) when idx = positive_xO_idx ->
    Option.map (fun n -> Int64.mul 2L n) (try_fold_positive inner)
  | _ -> None

(** Fold a Zpos/Zneg constructor wrapping a positive chain into a rendered
    numeral string.  [cidx] is the 1-based constructor index of the Z
    constructor; [inner] is its positive argument.  Returns [None] if [inner]
    cannot be folded. *)
let try_fold_z_binary info cidx inner : cpp_expr option =
  Option.map
    (fun pos_val ->
      let z_val =
        if cidx = z_pos_idx then pos_val
        else if cidx = z_neg_idx then Int64.neg pos_val
        else pos_val
      in
      render_numeral info (Z.of_int64 z_val))
    (try_fold_positive inner)

(** Whether [r] is a type family over a value -- [sem : idx -> Type] --
    whose applications ML writes without their argument, so that a generic
    declaration erases them where an instantiation can name them. *)
let value_indexed_family r =
  match r with
  (* A class's or record's type field is a function of the instance, not a
     family over a value. *)
  | GlobRef.ConstRef kn
    when Table.is_projection r || Structures.Structure.is_projection kn ->
    false
  | GlobRef.ConstRef _ -> (
    try
      let env = Global.env () in
      let ty, _ = Typeops.type_of_global_in_context env r in
      let prods, head = Reduction.whd_decompose_prod env ty in
      (* A class argument -- a section's [{Pa : Params}] -- is an instance,
         resolved where the family is used, not a value it is indexed by. *)
      let is_class_type t =
        match Constr.kind (fst (Constr.decompose_app t)) with
        | Constr.Ind (ind, _) -> Typeclasses.is_class (GlobRef.IndRef ind)
        | Constr.Const (c, _) -> Typeclasses.is_class (GlobRef.ConstRef c)
        | _ -> false
      in
      Constr.isSort head
      && List.exists
           (fun d ->
             let dty = Context.Rel.Declaration.get_type d in
             let _, h = Reduction.whd_decompose_prod env dty in
             (not (Constr.isSort h)) && not (is_class_type dty) )
           prods
    with _ -> false )
  | _ -> false

(** [t] with the instance's family written where a slot erased it: wherever
    the carrier [carrier] heads a type, an erased argument at a position the
    carrier fills with one of its variables takes that variable's binding in
    [m].  See {!instance_family_binding}. *)
let refine_by_instance_family (carrier, _, m) t =
  match carrier with
  | Tglob (h, cargs, _) ->
    map_cpp_type
      (function
        | Tglob (h', args, es) when GlobRef.CanOrd.equal h h' ->
          let n = List.length cargs in
          Tglob
            ( h',
              List.mapi
                (fun i a ->
                  match List.nth_opt cargs i with
                  | Some (Tvar (Tv_index (_, Some v) | Tv_named v)) when i < n && prints_as_any a -> (
                    match List.find_opt (fun (v', _) -> Id.equal v v') m with
                    | Some (_, b) -> b
                    | None -> a )
                  | _ -> a )
                args,
              es )
        | t -> t )
      t
  | _ -> t

(** [param_states_type_args x orig] -- whether the parameter whose Rocq type
    is [orig] constrains the type variables of the global [x] in a way that
    another argument's deduction can conflict with.

    This is a question about the {e declaration} Crane emits for [x], not
    about this call.  Two kinds of parameter say nothing.  A custom-extracted
    callee's C++ is spelled by its mapping, so it has no template parameters
    at all.  And a function-typed parameter is declared as a deduced template
    parameter of its own ({!Common.fun_tparam_name}), so whatever type
    variables its Rocq type mentions, the signature does not state them. *)
let param_states_type_args x orig =
  let rec is_arrow = function
    | Miniml.Tarr _ -> true
    | Miniml.Tmeta {contents = Some t} -> is_arrow t
    | _ -> false
  in
  (not (Table.is_custom x)) && not (is_arrow orig)

(** [erase_type_args_to_any ty] boxes a compound type's arguments but leaves a
    ground type alone: [deque<Nat>] becomes [deque<any>], while [Nat] stays
    [Nat].  This is the shape a box built out of a pattern binder physically
    has, and so the type an [any_cast] recovering it must name.  Deliberately
    weaker than {!Ml_type_util.erase_type_to_any}, which boxes the leaf too. *)
let rec erase_type_args_to_any = function
  | Tglob (g, (_ :: _ as args), ns) ->
    Tglob (g, List.map erase_type_args_to_any args, ns)
  | Tglob (_, [], _) as t -> t
  | Tnamespace (ns_g, inner) -> Tnamespace (ns_g, erase_type_args_to_any inner)
  | _ -> Tany

(** Handle eta expansion, curried function application, and promoted type arg
    resolution. Recovers erased template type args at call sites where C++ can't
    deduce them from lambda arguments, using the enclosing function's return
    type.

    In the normal (exact-application) case, also detects calls that return
    [std::any] because the callee is higher-rank polymorphic — either a record
    field (e.g. [apply : forall A, A -> A] stored as
    [std::function<std::any(std::any)>]) or an [MLrel] callback with a
    [Tdummy]-guarded [Tvar] codomain.  When such a call is made in a context
    where the enclosing function's return type is a concrete C++ type [T], the
    result is wrapped with [std::any_cast<T>].  See [ml_codomain_erases_to_any]. *)
let binder_is_instance env i =
  (* An instance parameter is not a value argument.  One Crane minted is
     known by its name: {!promote_typeclass_params} renames a typeclass-typed
     parameter to a {!Common.tc_instance_id}, and such a binder has no ML type
     of its own.  One that came from Coq keeps its name -- [h : E -< F], whose
     class [ReSum] is skipped, is never renamed -- and is known by its class
     being skipped.  Skipped is the whole test there: a binder at a class
     Crane {e kept} is an ordinary value wherever it was not renamed, and
     reading it as an instance would take the argument away from the call.
     The declaration drops both kinds; without the second the call sites went
     on passing the one the declaration had dropped. *)
  Option.cata Common.is_tc_instance_id false (Common.get_db_name_opt i env)
  || ( match get_env_type_opt i with
     | Some ty -> ml_ret_is_skipped ty
     | None -> false )

(* Check if an ML arg is a type class instance (a reference to a struct that
   implements a type class).

   [MLmagic] is a transparent coercion -- extraction inserts one around an
   instance whose class is applied to a type CONSTRUCTOR (e.g. [Mon Opt] with
   [Opt : Type -> Type]).  Look through it, or the instance is left in value
   position and the generated call names the instance struct as if it were a
   value. *)
let is_typeclass_instance_arg env ml_arg =
  match strip_magic ml_arg with
  | MLglob (r, _) ->
    (* An instance parameterised over types alone carries its parameters in
       the [MLglob]'s type arguments, so its ML type is still an arrow --
       [MList : forall A, Monoid (list A)].  Read the codomain, as the
       application case below does, or such an instance is left in value
       position and the call names the instance struct as if it were one. *)
    ref_is_instance r
  | MLrel i -> binder_is_instance env i
  | MLapp (MLglob (r, _), _) ->
    (* Parameterized instance application, e.g. numList A H. Check if r's
       return type (after stripping Tarr) is a typeclass type, or if it
       returns a skipped type (e.g. ReSum instances where the Class is a
       ConstRef not recognized by is_typeclass). *)
    ref_is_instance r
  | MLcase (case_ty, _scrutinee, branches) when Array.length branches = 1 ->
    (* Single-branch case = record field projection.  If the projected
       field's type is itself a typeclass, this is a typeclass instance
       arg — e.g., [base_category(PS)] projects a [PreCategory]-typed
       field from a [PreStableCategory] record.
       Look up the record's field types from the case type rather than
       relying on branch binding types (which may be Tunresolved). *)
    let (binds, _, _, br_body) = branches.(0) in
    ( match br_body with
    | MLrel j when j >= 1 && j <= List.length binds ->
      let idx = List.length binds - j in
      (* Try to get the field type from the record definition *)
      let field_is_tc =
        match case_ty with
        | Tglob (r, _, _) when Table.is_typeclass r ->
          let field_types = Table.record_field_types r in
          let non_dummy =
            filter_value_types field_types
          in
          ( try
              let fty = List.nth non_dummy idx in
              Table.is_typeclass_type fty
            with _ -> false )
        | _ -> false
      in
      field_is_tc
    | _ -> false )
  | _ -> false

(* Convert type class instance args to template type arguments *)

let instance_arg_is_erased env ml_arg =
  (* An instance argument is not a value argument, but only one whose class
     Crane kept is a template argument either: {!collect_typeclass_param_ids}
     mints a concept-constrained parameter per kept class and none for a
     skipped one, so an [E -< F] has no parameter of any kind to be passed at.
     Passing it anyway put the instance in the callee's template argument
     list, where it names no type. *)
  match strip_magic ml_arg with
  | MLglob (r, _) | MLapp (MLglob (r, _), _) ->
    (* Either the instance's class is infrastructure Crane skips -- [E -< F],
       whose [ReSum] is a [ConstRef] mapped to the empty string -- or the
       instance itself is, as [Monad_itree] is in both ITree modes.  Skipping
       the instance is how a mode says its carrier's operations are named by
       their mappings and not by a dictionary. *)
    ref_returns_skipped r || ref_is_skipped r
  | MLrel i -> (
    match get_env_type_opt i with
    | Some ty -> ml_ret_is_skipped ty
    | None -> false )
  | _ -> false

(** [split_instance_args env args] -- the class dictionaries a call passes,
    the ones an erasure removed left out; how many were removed, which still
    occupy a parameter of the declaration; and the regular arguments. *)
let split_instance_args env args =
  let tc, regular = List.partition (is_typeclass_instance_arg env) args in
  let erased, kept = List.partition (instance_arg_is_erased env) tc in
  (kept, List.length erased, regular)

(** [inline_custom_arg_arity id] is the number of [%aN] term placeholders an
    inline-custom mapping for [id] names -- one past the largest index it
    uses -- or [None] when [id] has no inline-custom mapping.

    A call has to supply exactly that many arguments: the printer drops any
    beyond the last placeholder, and raises on a placeholder it cannot fill. *)
let inline_custom_arg_arity id =
  if not (Table.is_inline_custom id) then None
  else
    match Table.find_custom_opt id with
    | None -> None
    | Some tmpl ->
      let re = Str.regexp "%a\\([0-9]+\\)" in
      let rec scan pos acc =
        match Str.search_forward re tmpl pos with
        | i ->
          scan (i + 1) (max acc (int_of_string (Str.matched_group 1 tmpl) + 1))
        | exception Not_found -> acc
      in
      Some (scan 0 0)

(** [promoted_var_resolution g] -- what the promoted type variable [g] stands
    for here, if the scope says.  A promoted variable is a class's [Type]
    field, and the type that mentions one records the field alone, never the
    instance it belongs to; the enclosing scope is what supplies that, through
    [promoted_var_map].  A variable the scope does not answer has no spelling
    here, which is a different thing from having an erased one. *)
let promoted_var_resolution g =
  match Table.promoted_type_var_name g with
  | Some var_id -> promoted_var_binding var_id
  | None -> None

(** Whether [ty] names a class field the current scope does not resolve, so
    that it would print through the field's file-scope [std::any] alias: a
    type read off another declaration, whose own instance resolved it. *)
let mentions_unresolved_promoted ty =
  exists_cpp_type
    (function
      | Tpromoted v -> promoted_var_binding v = None
      | Tglob (g, _, _) ->
        Table.is_promoted_type_var g && promoted_var_resolution g = None
      | _ -> false )
    ty

(** Apply a callee recovered from a bare [std::any], one argument at a time.

    Nothing about a boxed callable says how many arguments it takes: the
    producer's lambda stops at the first codomain that erases, so a value of an
    opaque function type ([nfun 2], a type-level [Fixpoint]) is a chain of unary
    [std::function<std::any(std::any)>]s.  Handing it every argument at once
    would cast it to a signature it was never stored at. *)
let apply_erased_curried ?(box = false) callee arg_exprs =
  List.fold_left
    (fun f a ->
      let a = if box then Cpp_erasure.converting_ctor Tany [a] else a in
      match f with
      (* A callable boxed right here never lost its type: recovering it would
         be a cast straight back to what it already was. *)
      | CPPbox (_, callable) -> mk_call callable [a]
      | _ -> CPPerased_call (f, a) )
    callee arg_exprs

(** Apply a callee whose static C++ type is the erased [std::any].  [std::any]
    is not callable, so the canonical [std::function<std::any(std::any...)>]
    adapter the producer stored via {!erase_fn_for_any_slot} is recovered with
    an [any_cast] and each argument is boxed.  The result is a [std::any]. *)
let apply_erased_callee callee arg_exprs =
  apply_erased_curried ~box:true callee arg_exprs

(** Save the current binder-type state for later restoration. *)
let save_erased_env () : binder_env = (!tctx).cpp_binder_types

(** Restore binder-type state saved by {!save_erased_env}. *)
let restore_erased_env saved = tctx := { !tctx with cpp_binder_types = saved }

(** Try to fold a Peano numeral chain (nested constructors) into an integer *)
let rec try_fold_numeral info expr =
  match strip_magic expr with
  | MLcons (_ty, cr, []) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_zero_ctor ->
      Some 0
    | _ -> None )
  | MLcons (_ty, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_succ_ctor ->
      Option.map (fun n -> n + 1) (try_fold_numeral info inner)
    | _ -> None )
  | _ -> None

(** [promoted_tys_of_arity n] is the concrete types the enclosing scope's
    promoted type variables stand for, when there are exactly [n] of them and
    so they can be read as the arguments of an [n]-ary type.  Erased entries
    are dropped, since a promoted variable that resolves to [std::any] says no
    more than the erased annotation it would replace. *)
let promoted_tys_of_arity n =
  match List.filter_map (fun (_, t) -> if prints_as_any t then None else Some t)
          (!tctx).promoted_var_map
  with
  | tys when List.length tys = n -> Some tys
  | _ -> None

(** When a lambda literal is about to be stored via [crane_erase_fn] (see the
    [ml_expr_is_function_value] call site in the custom-constructor arg loop),
    the lambda will only ever be invoked with its whole argument boxed as a
    single raw [std::any] (never with the generically-deduced concrete type),
    because that is exactly what [crane_erase_fn]'s CTAD-non-viable fallback
    forwards. If the lambda's own bound parameter [n] is immediately
    pattern-matched via a custom (e.g. pair) match, that match must therefore
    treat the scrutinee as erased — wrap it in [MLmagic] so
    [gen_custom_cpp_case] emits [any_cast<pair<any,any>>(...)] instead of a
    structured binding directly on the (at runtime erased) parameter. Without
    this, a domain type that is a pair with a mix of erased/concrete fields
    (e.g. [S.sem a * unit]) renders the parameter as a generic [auto&], and the
    destructure compiles fine at the OCaml/template level but fails at C++
    instantiation time when [auto&] deduces to [std::any] (structured
    bindings are not valid on [std::any]). *)
let rec mark_own_param_for_pair_erasure n body =
  match body with
  | MLcase (ty, MLrel i, pv) when i = n && is_custom_match pv ->
    MLcase (ty, MLmagic (Mboxed, MLrel i), pv)
  | MLmagic (m, a) -> MLmagic (m, mark_own_param_for_pair_erasure n a)
  | other -> other

(** [field_stores_erased_fn_value ?field_cpp_ty field_types i e] — true when
    constructor field [i] has an abstract type-variable (schema) type — a
    value-dependent field such as the predicate [P] of [sigT A P] — and the
    argument [e] is either a lambda function value or any value landing in a
    slot that is genuinely erased here ([field_cpp_ty], the field type
    instantiated with this call's own type arguments, is [std::any]).

    Such a function's return value is boxed into the field's [std::any] at
    runtime and recovered by consumers with a fixed [any_cast] shape.  To keep
    that shape consistent across every producer of the same Coq type (e.g. the
    "cons" and "nil" productions of a value-dependent [list (nat*nat)] action),
    the function body must be generated with [deep_erase] so its
    list/pair/record producers deep-erase to the canonical erased C++ form.
    Without this, a "cons" production built from concrete values would keep a
    concrete element type (e.g. [deque<Prod<Nat,Nat>>]) while the matching
    "nil" production erases to [deque<Prod<any,any>>], and reading the value
    back out of the [std::any] throws [std::bad_any_cast]. *)
let field_stores_erased_fn_value ?field_cpp_ty field_types i e =
  match List.nth_opt field_types i with
  | Some ft ->
    (* The (schema) field type must be an abstract type VARIABLE — e.g. the
       predicate parameter [P] of [sigT A P], instantiated here to a function
       type whose codomain is value-dependent and erased ([unit -> semty s]
       ↦ [std::function<std::any(Unit)>]).  A lambda stored into such an
       erased field has its result boxed into a single [std::any] at runtime,
       so its body's list/pair/record producers must deep-erase to a canonical
       C++ representation shared with every other producer of the same Coq
       type — otherwise a concretely-typed "cons" production
       ([deque<Prod<Nat,Nat>>]) and the erased "nil" production
       ([deque<Prod<any,any>>]) disagree and [std::any_cast] throws. *)
    let field_is_abstract_var =
      match ft with Miniml.Tvar (_, _) -> true | _ -> false
    in
    (* A non-function value needs the same canonical erasure whenever the
       slot it lands in is REALLY [std::any] here — e.g. the [list nat]
       payload of [sigT (fun b => if b then nat else list nat)], which a
       consumer reads back as the element-erased [List<std::any>].  When the
       abstract field instead instantiates to a concrete type (an ordinary
       polymorphic container such as [Sig<List<nat>>]), the value must keep
       its concrete element type. *)
    let slot_is_erased =
      match field_cpp_ty with Some ct -> prints_as_any ct | None -> false
    in
    field_is_abstract_var
    && (slot_is_erased || match strip_magic e with MLlam _ -> true | _ -> false)
  | None -> false

(** Adapt a callable produced with fewer parameters than its use site expects.
    A body like [fun f acc => f acc] is eta-reduced before it reaches here, so
    the lambda takes one argument where the slot's type takes two; the missing
    arguments are supplied by eta-expansion, applying what the shorter lambda
    returns to the arguments it did not take.

    [ml_arity] is how many arguments the slot's MiniML type takes: a lambda
    that takes fewer than its C++ slot but as many as its ML type is curried
    on purpose, not shortened, and is left alone -- as is one whose body
    [returns_a_lambda], having spelled the remaining arguments out itself. *)
let eta_expand_to_expected ?expected_ty ~ml_arity ~returns_a_lambda ~arity f =
  match Option.map strip_cpp_ref_const expected_ty with
  | Some (Tfun (dom, _))
    when arity > 0 && ml_arity > arity && List.length dom > arity
         && not returns_a_lambda ->
    let params = adapter_params ~prefix:"_ee" dom in
    let taken = List.filteri (fun i _ -> i < arity) params in
    let rest = List.filteri (fun i _ -> i >= arity) params in
    let call =
      List.fold_left
        (fun acc group -> mk_call acc (List.map adapter_arg group))
        f [taken; rest]
    in
    mk_lambda params None [Sreturn (Some call)] ~capture:Closure
  | _ -> f

(* The class an instance argument is an instance of, as an ML type. *)
let instance_class_ty env ml_arg =
  let of_ref r =
    match Table.find_type r with
    | ty -> ml_return_type ty
    | exception Not_found -> Miniml.Tunknown
  in
  match strip_magic ml_arg with
  | MLglob (r, _) | MLapp (MLglob (r, _), _) -> of_ref r
  | MLrel i -> (
    match get_env_type_opt i with
    | Some ty -> ml_return_type ty
    | None -> Miniml.Tunknown )
  | _ -> Miniml.Tunknown

(* The instance a projection call would project through, where Crane kept it.

   A mapping on a class field is written for a mode that erases the class's
   instances: with nothing left to project from, the field's C++ text has to
   name the operation itself.  That text speaks for one particular carrier --
   [Monad.bind] in reified ITree mode is [itree_bind] -- so it may only stand
   where the instance it speaks for was the one erased.  An instance Crane kept
   reached C++ as a struct or as a concept-constrained template parameter, and
   names its own operations; projecting through it is both what the Rocq term
   says and the only thing that can typecheck.

   Requiring the field to belong to {e this} instance's class is what keeps the
   rule from firing on an ordinary mapped constant that merely takes an
   instance among its arguments. *)
let kept_instance_of_projection env x args =
  List.find_opt
    (fun a ->
      is_typeclass_instance_arg env a
      && (not (instance_arg_is_erased env a))
      && List.mem (Some x)
           (record_fields_of_type (instance_class_ty env a)) )
    args

(** The shape a value physically has once it has been through a [std::any]:
    unchanged for a leaf, and one level of template with every argument boxed
    for a compound ([pair<Nat, tup>] becomes [pair<any, any>]).  A compound's
    components are separately boxed, so the erasure stops at one level --
    nesting it would name [pair<any, pair<any, any>>] for a box whose second
    component is itself only a box.  This is the type an [any_cast] reading
    such a value back has to name, whatever concrete type the context has in
    mind for it. *)
let boxed_shape_of = function
  | Tglob (g, (_ :: _ as args), ns) -> Tglob (g, List.map (fun _ -> Tany) args, ns)
  | t -> t

(** Fold a Decimal.uint digit chain into an arbitrary-precision integer.
    Constructor indices (1-based): Nil=[uint_nil_idx], D0..[decimal_d9_idx].
    Digits are processed outside-in (most significant first).
    Uses [Z.t] from zarith to avoid overflow on large literals. *)
let rec try_fold_decimal_uint expr acc =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), []) when idx = uint_nil_idx ->
    Some acc
  | MLcons (_, GlobRef.ConstructRef (_, cidx), [inner])
    when cidx >= decimal_d0_idx && cidx <= decimal_d9_idx ->
    let digit = Z.of_int (cidx - decimal_d0_idx) in
    try_fold_decimal_uint inner Z.(acc * of_int 10 + digit)
  | _ -> None

(** Fold a Decimal.signed_int (Pos | Neg) wrapping a Decimal.uint chain.
    Constructor indices (1-based): Pos=[signed_pos_idx], Neg=[signed_neg_idx]. *)
let try_fold_signed_decimal_int expr =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) ->
    if idx = signed_pos_idx then try_fold_decimal_uint inner Z.zero
    else if idx = signed_neg_idx then
      Option.map Z.neg (try_fold_decimal_uint inner Z.zero)
    else None
  | _ -> None

(** Fold a Hexadecimal.uint digit chain into an arbitrary-precision integer.
    Constructor indices (1-based): Nil=[uint_nil_idx], D0..[hex_df_idx].
    Uses [Z.t] from zarith to avoid overflow on large literals. *)
let rec try_fold_hex_uint expr acc =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), []) when idx = uint_nil_idx ->
    Some acc
  | MLcons (_, GlobRef.ConstructRef (_, cidx), [inner])
    when cidx >= hex_d0_idx && cidx <= hex_df_idx ->
    let digit = Z.of_int (cidx - hex_d0_idx) in
    try_fold_hex_uint inner Z.(acc * of_int 16 + digit)
  | _ -> None

(** Fold a Hexadecimal.signed_int (Pos | Neg) wrapping a Hexadecimal.uint chain.
    Constructor indices (1-based): Pos=[signed_pos_idx], Neg=[signed_neg_idx]. *)
let try_fold_signed_hex_int expr =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) ->
    if idx = signed_pos_idx then try_fold_hex_uint inner Z.zero
    else if idx = signed_neg_idx then
      Option.map Z.neg (try_fold_hex_uint inner Z.zero)
    else None
  | _ -> None

(** Fold a Number.signed_int (IntDecimal | IntHexadecimal) into an
    arbitrary-precision integer.
    Constructors: IntDecimal(idx=1), IntHexadecimal(idx=2). *)
let try_fold_num_int expr =
  match strip_magic expr with
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> try_fold_signed_decimal_int inner
    | GlobRef.ConstructRef (_, 2) -> try_fold_signed_hex_int inner
    | _ -> None )
  | _ -> None

(** Whether [e] reads a component straight out of a pair recovered from a
    [std::any].  Such a component is itself a box, so it needs no further
    recovery here -- the site that consumes it does its own. *)
let is_erased_pair_component = function
  | CPPfun_call (_, _, {rev = [CPPany_cast (Tglob (g, (_ :: _ as args), _), _)]}) ->
    is_prod_global g && List.for_all prints_as_any args
  | _ -> false

(** How a term argument of a custom type is generated: by {!gen_expr}, which
    fills this in once it is defined.  The one place type conversion calls
    back into expression generation -- a mapped type applied to a term, as a
    fixed-size array is to its length -- so it is the edge the two are
    separated at. *)
let type_term_arg : (env -> ml_ast -> cpp_expr) ref =
  ref (fun _ _ -> CErrors.anomaly (Pp.str "Translation.type_term_arg: unset"))

(** Fold a Number.uint (UIntDecimal | UIntHexadecimal) into an
    arbitrary-precision integer.
    Constructor indices (1-based): UIntDecimal=[num_uint_decimal_idx],
    UIntHexadecimal=[num_uint_hex_idx]. *)
let try_fold_num_uint expr =
  match strip_magic expr with
  | MLcons (_, GlobRef.ConstructRef (_, idx), [inner]) ->
    if idx = num_uint_decimal_idx then try_fold_decimal_uint inner Z.zero
    else if idx = num_uint_hex_idx then try_fold_hex_uint inner Z.zero
    else None
  | _ -> None

let rec convert_ml_type_to_cpp_type
    env
    ?(ns : Refset'.t = Refset'.empty)
    (tvars : Id.t list)
    (ml_t : ml_type) : cpp_type =
  (* [ns] is the only source of recursive-storage wrapping.  Most callers
     omit it (defaulting to empty), so types like [List<tree>] stay value
     shaped in function signatures.  Struct-field storage conversion passes the
     owning inductive in [ns], so non-coinductive recursive occurrences at
     constructor storage sites become [shared_ptr]. *)
  match ml_t with
  | Tarr (t1, t2) ->
    (* std::function<F(A)> is already a value type and provides the heap
       indirection needed to break recursive layout cycles.  Always pass an
       empty [ns] for domain and codomain so that recursive self-references
       inside function types stay as value types instead of being wrapped in
       shared_ptr.  The outer field-position wrapping (shared_ptr for direct
       self-ref fields) is handled at the call site, not here. *)
    let t1c = convert_ml_type_to_cpp_type env tvars t1 in
    (* Reify monadic domain types: itree E R in parameter position becomes
       shared_ptr<ITree<R>> so the tree can be passed as a value. *)
    let t1c = reify_monadic_param_type t1 t1c in
    let t2c = convert_ml_type_to_cpp_type env tvars t2 in
    (* Skip erased params: isTdummy catches direct Tdummy, is_cpp_dummy_type
       catches Tdummy wrapped in Tmeta (e.g., Tmeta{contents=Some(Tdummy Kprop)}
       which converts to dummy_prop glob). Do NOT use prints_as_any here as it
       also catches Tany (std::any), which is a valid type for universally
       quantified parameters — stripping it would incorrectly collapse (A -> IO)
       into just IO. *)
    if isTdummy t1 || is_cpp_dummy_type t1c then
      t2c
    else (
      (* Void-ify unit codomain: function types returning [unit] (directly
         or via monadic wrapper like [itree E unit]) should map to [void]
         to match void-ified function definitions. Check the ML type [t2]
         since the C++ type may still be a monad Tglob, not bare unit. *)
      let voidify_cod c =
        if is_cpp_unit_type c then Tvoid
        else if ml_type_is_void_call t2 then Tvoid
        else c
      in
      (* A result the arguments only pin down as a type index is not something
         a template parameter can stand for; erase it. *)
      let voidify_cod c =
        if result_is_index_only_tvar ml_t then Tany else voidify_cod c
      in
      match
        t2c
      with
      | Tfun (l, t) -> Tfun (t1c :: l, voidify_cod t)
      | _ -> Tfun (t1c :: [], voidify_cod t2c) )
  | Tglob (g, _, _) when is_void g -> Tvoid
  (* PROMOTED TYPE VARIABLES: Handle references to record fields that were
     "promoted" from value-level fields to type-level parameters.

     A "promoted" field is a Type-valued record field (e.g., [m_carrier : Type]
     in [Record Monoid]) that became a C++ concept type requirement instead of
     a struct field. At usage sites, references to these fields must be treated
     as TYPES, not values.

     Example:
       Coq: [mfold (M : Monoid) (l : list (m_carrier M))]
            Here [m_carrier M] is a TYPE (the carrier type of the monoid M)

       C++: [template <Monoid _tcI0> ... List<typename _tcI0::m_carrier> ...]
            Must qualify as a type, not access as a field: NOT _tcI0->m_carrier

     Three contexts for promoted type vars:
     1. Inside template functions with typeclass params: [promoted_var_map] is
        populated, resolve to qualified types like [typename _tcI0::m_carrier]
     2. Module-level (constructor expressions): Use module aliases ([std::any])
     3. No context: Mark with [Tpromoted] for later resolution *)
  | Tglob (g, ts, _) when Table.is_promoted_type_var g ->
    ( match Table.promoted_type_var_name g with
    | Some var_id ->
      ( match promoted_var_resolution g with
      | Some resolved -> resolved
      | None ->
        (* No resolution found.  When the constructor-expression flag is set,
           all promoted vars become [Tany] (= std::any) because module-level
           type aliases are always std::any and non-Type promoted vars (like
           [base_category]) have no alias at all.  Otherwise keep the marker
           for concept generation and signature printing. *)
        if (!tctx).in_constructor_expr then Tany
        else Tpromoted var_id )
    | None -> Tany )
  | Tglob (g, _, _) when Table.is_value_dep_type_scheme g ->
    (* Value-dependent type scheme (e.g. [sym_semty : sym -> Type]) applied to a
       runtime value — not representable as a C++ type, so erase to [std::any].
       This keeps erasure consistent: such values are already stored as
       [std::any], so the types that mention them are [std::any] too, and no
       [any_cast] guard is needed at use sites. *)
    Tany
  | Tglob (g, ts, args) when is_custom g ->
    Tglob
      ( g,
        List.map (convert_ml_type_to_cpp_type env ~ns tvars) ts,
        List.map (!type_term_arg env) args )
  | Tglob (g, ts, _) ->
    (* For inductives, only keep type args that correspond to parameters (not
       indices). Parameters become template params in C++; indices are
       erased. *)
    let filtered_ts =
      match g with
      | GlobRef.IndRef (kn, _) ->
        (* Filter type args to keep only parameters (not indices). Use
           get_ind_num_param_vars_opt to determine how many to keep. For
           local/self-references with non-empty tvars, we can use tvars length
           as a fallback, but prefer the table lookup for accuracy. *)
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* Only keep the first num_param_vars type args - the rest are
             indices *)
          safe_firstn num_param_vars ts
        | None ->
          (* Fallback: if tvars is non-empty and this is a local reference, use
             tvars length *)
          let is_local =
            Refset'.mem g ns
            || List.exists
                 (globref_equal g)
                 !local_inductives
          in
          if is_local && tvars <> [] then
            safe_firstn (List.length tvars) ts
          else
            ts )
        (* Keep all if we can't determine *)
      | _ -> ts
    in
    (* Only propagate ns into type arguments when g itself is a self-ref.
       For non-self types (e.g. list inside tree's definition), type args
       stay bare — the field-level wrapping handles the cycle-breaking.
       This ensures type variables are never shared_ptr-wrapped at instantiation. *)
    let ns_for_args =
      if Refset'.mem g ns then ns else Refset'.empty
    in
    let converted_ts =
      List.map (convert_ml_type_to_cpp_type env ~ns:ns_for_args tvars) filtered_ts
    in
    let converted_ts =
      match g with
      (* Only where a later parameter's type mentions an earlier one --
         [sigT A (P : A -> Type)] -- does erasing the earlier one erase the
         later.  An erased family ([tree void1 R], [void1] logical) is
         nothing [R] depends on. *)
      | GlobRef.IndRef _ when Table.has_dependent_params g ->
        let rec first_ktype_idx i = function
          | [] -> max_int
          | (Tdummy Ktype | Tmeta {contents = Some (Tdummy Ktype)}) :: _ -> i
          | _ :: rest -> first_ktype_idx (i + 1) rest
        in
        let cutoff = first_ktype_idx 0 filtered_ts in
        if cutoff < max_int then
          List.mapi
            (fun i t -> if i > cutoff then index_erase_type t else t)
            converted_ts
        else
          converted_ts
      | _ -> converted_ts
    in
    let converted_ts = apply_hkt_tyctors g converted_ts in
    let converted_ts = ind_promoted_type_args g @ converted_ts in
    let core = Tglob (g, converted_ts, []) in
    ( match g with
    | GlobRef.IndRef _ ->
      (* Enum inductives are value types - no shared_ptr wrapping *)
      if is_enum_inductive g then
        let is_local =
          Refset'.mem g ns
          || List.exists
               (globref_equal g)
               !local_inductives
        in
        if is_local then
          core
        else
          Tnamespace (g, core)
      else
        (* Check if this inductive is in the explicit ns list or in
           local_inductives context *)
        let is_self_ref = Refset'.mem g ns in
        (* Check if g is a mutual sibling: shares the same MutInd.t KerName
           as any member of ns, but at a different index. Mutual siblings
           need shared_ptr because their types are incomplete (forward-declared). *)
        let is_mutual_sibling =
          (not is_self_ref) &&
          match g with
          | GlobRef.IndRef (kn_g, _) ->
            Refset'.exists (fun r ->
              match r with
              | GlobRef.IndRef (kn_r, _) ->
                MutInd.CanOrd.equal kn_g kn_r
              | _ -> false) ns
          | _ -> false
        in
        let is_local =
          is_self_ref
          || List.exists
               (globref_equal g)
               !local_inductives
        in
        let is_uniform_self_ref =
          if not is_self_ref then
            true
          else if converted_ts = [] then
            (* Non-parametric inductive: self-reference is trivially uniform.
               The surrounding context may have type vars (e.g. T1 in rect<T1>)
               that are unrelated to the inductive's own parameters — don't
               let those force shared_ptr for a monomorphic self-reference. *)
            true
          else
            List.length converted_ts = List.length tvars
            && List.for_all2
                 (fun ty id ->
                   match ty with
                   | Tvar (Tv_index (_, Some id') | Tv_named id') -> Id.equal id id'
                   | _ -> false)
                 converted_ts
                 tvars
        in
        if
          (is_self_ref || is_mutual_sibling)
          && not (Table.is_coinductive g)
          && is_uniform_self_ref
        then
          (* Recursive value-type self/mutual references are owned by their
             containing constructor. The pointed-to type may be incomplete at
             field declaration time, so it still needs indirection, but unique
             ownership plus explicit clone is enough. (Arena mode rewrites this
             shared_ptr to a raw arena pointer at the field-declaration site in
             gen_decls, so that method return/parameter positions are unaffected.) *)
          Tshared_ptr core
        else if (is_self_ref || is_mutual_sibling) && Table.is_coinductive g
        then
          (* A coinductive value is already a handle on one shared node, so
             a field holding one holds it by value.  The constructor struct
             that holds it is a member template, completed only once the
             coinductive is -- see [Fdeferred_struct]. *)
          core
        else if is_self_ref || is_mutual_sibling then
          (* Non-uniform recursion uses shared_ptr rather than unique_ptr
             because destructor instantiation would diverge. *)
          Tshared_ptr core
        else if is_local then
          (* Local non-self inductive: value type, no pointer wrapping *)
          core
        else if not (get_record_fields g == []) then
          (* Record inductive: value type, no pointer wrapping *)
          core
        else
          (* External inductive: value type, namespace-qualified *)
          Tnamespace (g, core)
    | _ -> core )
  | Miniml.Tvar (_, i) -> Tvar (Tv_index (i, tvar_name_at tvars i))
  (* A higher-kinded variable applied to arguments.  The head stays a type
     variable here; [Gen_decls.apply_hkt_resolutions] rewrites it to the
     instance's associated type, leaving [Tapply] to render the application. *)
  | Tapp (i, args) ->
    let head = Tvar (Tv_index (i, tvar_name_at tvars i)) in
    Tapply (head, List.map (convert_ml_type_to_cpp_type env ~ns tvars) args)
  | Tmeta {contents = Some t} -> convert_ml_type_to_cpp_type env ~ns tvars t
  | Tmeta {id = i} ->
    (* Unresolved meta - use std::any for type erasure. This happens for
       existential type variables in indexed inductives. *)
    Tany
  (* Tdummy marks erased type/prop/implicit parameters in the ML AST. We convert
     them to Tglob(VarRef "dummy_*") as intermediate markers so that downstream
     filtering (is_cpp_dummy_type / prints_as_any / filter_erased_type_args in
     gen_expr, eta_fun, and gen_decl_for_pp) can detect and drop them. These
     markers should never survive to the C++ output — the filtering pipeline
     removes them from template argument lists and function signatures. *)
  | Tdummy Ktype -> Terased Ek_type
  | Tdummy Kprop -> Terased Ek_prop
  | Tdummy (Kimplicit _) -> Terased Ek_implicit
  | Tstring ->
    Tid_external ("std::string", [])
  (* Extraction gave up naming this type.  It prints as [std::any], but we
     know nothing about how the value is actually represented. *)
  | Tunknown -> Topaque
  | Taxiom -> Tglob (GlobRef.VarRef (Id.of_string "axiom"), [], [])

(** Convert ML type arguments to C++ template parameters, applying type
    simplification and handling out-of-scope type variables.

    This function maps a list of ML types to C++ types for use in template
    argument lists. It performs two key transformations:

    1. Type simplification via [type_simpl] to normalize ML types
    2. Conversion to C++ types via [convert_ml_type_to_cpp_type]
    3. Detection and erasure of unbound type variables

    The [tvars] parameter specifies the type variables in scope (as a list of
    typename declarations in the current C++ context). When a [Tvar] appears
    with [None] for its binding and [tvars] is non-empty, this indicates the
    type variable index is out of scope — it references a typename that doesn't
    exist in the current C++ context.

    Out-of-scope type variables are marked as [dummy_type], which triggers
    [filter_erased_type_args] to drop the entire type argument list. This is
    safer than emitting invalid C++ like [template<typename T> ... U] where
    [U] is undefined.

    Example scenario where this occurs:
    - ML function with type scheme [forall A B, A -> B -> option A]
    - Partial application instantiates [A] but leaves [B] polymorphic
    - C++ code generator enters context with only [typename A]
    - Type arg list includes [Tvar 2] for [B]
    - [convert_ml_type_to_cpp_type] returns [Tvar(2, None)] (no binding)
    - We mark it [dummy_type] to trigger erasure

    @param env   Translation environment (unused in current implementation)
    @param tvars Type variables in scope (C++ typename parameters)
    @param tys   ML type arguments to convert
    @return List of C++ types, with out-of-scope Tvars marked as dummy_type *)

(** Whether a bare reference to global [x] must be spelled [x()]: it is
    declared as a zero-parameter function rather than a data member.  That is
    the case for thunked values (monadic definitions, cofixpoints, extracted
    axioms) and for definitions that really do take C++ parameters.

    An ML arrow is {i not} enough: a definition all of whose arguments are
    erased (a lemma-only argument, say) converts to a non-function C++ type
    and is emitted as a data member by {!Gen_decls.gen_spec}.  Asking the
    converter is what keeps the two in step. *)
let glob_is_nullary_function x =
  match find_type_opt x with
  | None -> false
  | Some ml_ty ->
    is_monadic_ml_type ml_ty
    || Table.is_cofixpoint x
    || Table.is_throwing_value x
    || ( match convert_ml_type_to_cpp_type (empty_env ()) [] ml_ty with
       | Tfun _ -> true
       | _ -> false )

(** [resolves_to_any_type ty] — true if [ty] ultimately resolves to
    [std::any].  Handles direct [Tany], erased-type constants (aliases for
    [std::any] registered via {!Table.is_erased_type_const}), and type
    aliases that expand to an erased type.  Used to decide whether a
    scrutinee's template argument makes a constructor field store its
    value as [std::any] at runtime. *)
let rec resolves_to_any_type = function
  | Tany | Topaque -> true
  (* An erasure marker is a position the filtering passes drop, not a value
     that resolves to a box. *)
  | Terased _ -> false
  | Tglob (g, [], _) when Table.is_erased_type_const g -> true
  | Tglob (g, [], _) ->
    let via_ml_ty =
      match find_type_opt g with
      | Some ml_ty ->
        let tvars = get_current_type_vars () in
        Some (convert_ml_type_to_cpp_type (empty_env ()) tvars ml_ty)
      | None ->
        (* A type-level Definition/Fixpoint (e.g. [syms_semty g := tuple (map
           sym_semty g)]) has no entry in the [find_type_opt] type table, but its
           erased [using] expansion is recorded as a typedef.  Follow that so a
           multi-level alias chain ([syms_semty -> tuple -> std::any]) still
           resolves. *)
        (match g with
         | GlobRef.ConstRef kn ->
           (match Table.lookup_typedef_unchecked kn with
            | Some ml_ty ->
              let tvars = get_current_type_vars () in
              Some (convert_ml_type_to_cpp_type (empty_env ()) tvars ml_ty)
            | None -> None)
         | _ -> None)
    in
    (match via_ml_ty with
     | Some cvt -> resolves_to_any_type cvt
     | None -> false)
  | t when prints_as_any t -> true
  | _ -> false

(** [cpp_of_ml env t] converts an ML type in the type-variable scope that is
    currently in effect.  Nearly every conversion inside expression generation
    wants this, and spelling out {!get_current_type_vars} at each one invites
    passing the wrong scope. *)
let cpp_of_ml env t =
  convert_ml_type_to_cpp_type env (get_current_type_vars ()) t

(** [template_arg_of_ml_type env tvars ty] converts [ty] for a template
    argument position, where a function type has to keep the currying the
    Rocq arrows had; see {!Minicpp.curry_fun_type}.

    [~curry:false] for an argument that instantiates an {e inductive}'s
    parameter.  Such a parameter only names the type of a stored value, and the
    value is spelled at the flat arity {!convert_ml_type_to_cpp_type} gives the
    declaration; currying it would make the instantiation disagree with the
    type the declaration writes.  A {e function}'s parameter is different: the
    signature may mention it inside an arrow it writes out itself (as [ap : F
    (A -> B) -> ...] does), and there the currying is what makes the argument
    match. *)
let template_arg_of_ml_type ?(curry = true) env tvars ty =
  (* Template params emitted at expression/function-call sites are public API
     types. Recursive storage wrapping is introduced only when converting
     constructor fields with an explicit storage namespace. *)
  let t =
    convert_ml_type_to_cpp_type env ~ns:Refset'.empty tvars (type_simpl ty)
  in
  if curry then curry_fun_type t else t

let build_template_params ?curry env tvars tys =
  List.map
    (fun ty ->
      let t = template_arg_of_ml_type ?curry env tvars ty in
      (* Check for unbound type variables *)
      match t with
      | Tvar (Tv_index (_, None)) when tvars <> [] ->
        (* Type variable has no binding, but we're in a context with typename
           params. This means the Tvar index exceeds the scope of tvars.
           Mark as dummy_type to trigger full erasure via filter_erased_type_args.
           Using the unbound Tvar would generate invalid C++ references. *)
        Terased Ek_type
      | _ ->
        (* Type is either bound, or we're in an untyped context (tvars = []).
           Keep the type as-is. *)
        t )
    tys

(** Generate code for a custom-extracted constructor application.

    Custom-extracted constructors have user-defined C++ syntax (registered via
    [Crane Extract Constant]) that may include type argument placeholders like
    [%t0], [%t1], etc. This function builds the C++ expression by:
    1. Filtering the ML type argument list to keep only type parameters
       (dropping index arguments that don't correspond to C++ template params)
    2. Converting ML types to C++ types via [build_template_params]
    3. Filtering erased types (Tdummy Ktype → dummy_type) to avoid passing
       empty or partial template argument lists to custom syntax
    4. Wrapping in [mk_cppglob] to apply the custom syntax template

    The filtering is critical because custom syntax strings expect concrete
    type arguments for their placeholders. If we pass an empty or erased
    type arg list, the custom syntax renderer in cpp_print.ml will raise
    an anomaly ("Custom syntax: unbound type argument").

    Example:
    - ML: [MLcons(Tglob(option, [Tglob(nat)]), cons_ctor, [5])]
    - Custom syntax: [(Datatypes.option, 0) := "std::optional<%t0>"]
    - After filtering: [std::optional<unsigned int>]
    - Generated C++: [std::make_optional<unsigned int>(5u)]

    Note: This only handles custom constructors. Regular (non-custom) inductives
    follow a different code path via the main [gen_expr] MLcons case.

    @param env Translation environment (contains type context)
    @param ty  ML type of the constructor application (contains type args)
    @param r   Constructor reference (must be custom-extracted)
    @param ts  ML expression arguments (converted to C++ recursively)
    @return C++ expression applying custom syntax with type/value arguments *)

(** [template_params_of_ml env tys] is {!build_template_params} against the
    type variables the enclosing scope has in hand; see {!cpp_of_ml}. *)
let template_params_of_ml ?curry env tys =
  build_template_params ?curry env (get_current_type_vars ()) tys

(** [param_expected_cpp_ty env param_tys i] is the C++ type the callee declares
    for its [i]th parameter, and so the type an argument generated for that
    position should aim at.  [None] when the position says nothing useful:
    either the callee has fewer parameters, or the declared type is erased and
    naming [std::any] as the expectation would only invite a spurious box. *)
let param_expected_cpp_ty env param_tys i =
  match List.nth_opt param_tys i with
  | Some ml_ty ->
    let cpp_ty = cpp_of_ml env ml_ty in
    if prints_as_any cpp_ty then None else Some cpp_ty
  | None -> None

(** [ml_erases_to_box env t] -- whether [t] is represented as a [std::any]
    here.  Conversion is what answers this: a value-dependent type such as
    [syms_semty xs], or a type variable this scope leaves unresolved, is only
    revealed as a box once converted, and a [Type]-valued definition hides one
    behind a [using] alias that {!resolves_to_any_type} follows. *)
let ml_erases_to_box env t = resolves_to_any_type (cpp_of_ml env t)

(** [result_cpp_via_receiver env callee_ty args] is the C++ type a call's
    result really has, where the callee's declared codomain is one of the type
    variables its first argument's type instantiates -- the field a projection
    out of a dependent pair hands back, say.

    The answer is read off the {e converted} receiver, at the template position
    the codomain occupies in it.  Converting the codomain's own instantiation
    instead is not the same thing: a type argument that the receiver's
    conversion erases still spells concretely in isolation, and the field it
    describes is then physically a [std::any] while its ML type denies it.
    [None] means the call is not of this shape, or that the two spellings of
    the receiver disagree on how many arguments it has -- the position would
    then name the wrong one. *)
let result_cpp_via_receiver env callee_ty args =
  let var_index t = match resolve_tmeta t with Miniml.Tvar (_, j) -> Some j | _ -> None in
  let position_of j formals =
    let rec find i = function
      | [] -> None
      | f :: rest -> if var_index f = Some j then Some i else find (i + 1) rest
    in
    find 0 formals
  in
  match (var_index (ml_codomain callee_ty), ml_value_domains callee_ty, args) with
  | Some j, dom0 :: _, arg :: _ -> (
    match (resolve_tmeta dom0, Option.map resolve_tmeta (infer_ml_body_type arg)) with
    | Miniml.Tglob (g1, formals, _), Some (Miniml.Tglob (g2, actuals, _) as recv)
      when Common.globref_equal g1 g2 -> (
      match (position_of j formals, template_args (cpp_of_ml env recv)) with
      | Some i, Some cpp_args when List.length actuals = List.length cpp_args ->
        List.nth_opt cpp_args i
      | _ -> None )
    | _ -> None )
  | _ -> None

(** [iife_void_return env typ pv] is [Some Tvoid] when the match's branches
    produce nothing: a lambda that may fall off its end has to say [-> void]
    explicitly. *)
let iife_void_return env typ pv =
  let branch_rty =
    match Array.to_list pv with (_, rty, _, _) :: _ -> rty | [] -> typ
  in
  let r = cpp_of_ml env branch_rty in
  if is_cpp_unit_type r || ml_type_is_void_call branch_rty then
    Some Tvoid
  else None

(** [iife_closure_return env typ pv stmts] is the return type to annotate the
    IIFE wrapping a match with, given the branches already generated.

    Distinct closures have no common type, so a match that returns one from
    some branch needs the [std::function] they all convert to.  Otherwise
    [None]: deducing beats annotating, because the branch's recorded ML type
    can outlive the term it described -- a motive's arrow surviving the
    application that consumed it -- and because it may still mention type
    variables that mean nothing in a non-template context.

    The question is asked of the generated statements, not of the ML terms: a
    branch spells a closure whether it was written as a lambda, arose from a
    partial application, or is a function-typed binder handed straight back,
    and only the C++ says which.  A binder counts because a function-typed
    parameter is a deduced template parameter of its own -- [f] and [g] of the
    same Rocq type are still two C++ types, and two branches returning one
    each deduce nothing. *)
let iife_closure_return env typ pv stmts =
  let found = ref false in
  let rec is_arrow = function
    | Miniml.Tarr _ -> true
    | Miniml.Tmeta {contents = Some t} -> is_arrow t
    | _ -> false
  in
  let binder_is_fun id =
    match List.assoc_opt id (!tctx).env_types with
    | Some ty -> is_arrow ty
    | None -> false
  in
  let scan_expr e =
    match e with
    | CPPlambda _ -> found := true
    | CPPvar id when binder_is_fun id -> found := true
    | _ -> ()
  in
  let rec scan_stmt s =
    match s with
    | Sreturn (Some e) -> scan_expr e
    | _ ->
      Minicpp.iter_stmt_children
        ~on_expr:(fun _ -> ())
        ~on_stmts:(List.iter scan_stmt) s
  in
  List.iter scan_stmt stmts;
  if not !found then None
  else
    let branch_rty =
      match Array.to_list pv with (_, rty, _, _) :: _ -> rty | [] -> typ
    in
    match cpp_of_ml env branch_rty with Tfun _ as r -> Some r | _ -> None

(** [glob_declared_cod_erases r] -- whether the declaration of [r] returns a
    box.  A declaration is converted from the global's own ML type with no
    type variables in scope, and that conversion erases a result no parameter
    pins down -- a type index, say -- however concrete the type is at a given
    call site.  So the question can only be asked of the whole type: the
    codomain alone converts to the type variable and reveals nothing. *)
let glob_declared_cod_erases r =
  match find_type_opt r with
  | Some ty -> (
    match convert_ml_type_to_cpp_type (empty_env ()) [] (type_simpl ty) with
    | Tfun (_, cod) -> prints_as_any cod
    | _ -> false )
  | None -> false

(** Record the C++ type of the pattern variable at de Bruijn index [i].

    A box is never overwritten by a concrete type.  Several passes describe
    the same binder -- an outer erased pair match says every field is a
    [std::any], and the per-field pass then reports the definition-site type
    the scrutinee instantiates -- and the erased view is the one that
    describes the runtime value. *)
let record_binder_type i t =
  let boxed_by_pattern =
    match IntMap.find_opt i (!tctx).cpp_binder_types with
    | Some (t', Bpattern) -> t' <> Topaque && resolves_to_any_type t'
    | _ -> false
  in
  if not boxed_by_pattern then
    tctx :=
      { !tctx with
        cpp_binder_types = IntMap.add i (t, Bpattern) (!tctx).cpp_binder_types }

(** [populate_erased_field_env ~cname ~typ ~env ~n_pat_vars ~n_fields
    ~non_erased_def_site_field_tys] populates {!cpp_binder_types} for a
    pattern-match branch.  For each
    constructor field whose definition-site type is a type variable that
    resolves to [std::any] via the scrutinee's template arguments, marks
    the corresponding de Bruijn index as erased and records its concrete
    C++ type from the template arguments.

    @param scrut_db  de Bruijn index of the scrutinee within this branch, when
           it is a local binder whose C++ type an enclosing branch recorded
    @param cname  constructor reference (to look up parameter count)
    @param typ    ML type of the scrutinee
    @param env    translation environment
    @param n_pat_vars  number of pattern variables in this branch
    @param n_fields    number of non-erased constructor fields
    @param non_erased_def_site_field_tys  definition-site field types
           with erased (dummy) entries filtered out *)
let populate_erased_field_env ?scrut_db ~cname ~typ ~env ~n_pat_vars ~n_fields
    ~non_erased_def_site_field_tys () =
  let scrut_cpp_ty =
    (* An enclosing branch may already have pinned the scrutinee's C++ type
       down -- [SigT<any, pair<any,any>>] tells us its payload binder is a
       [pair<any,any>], which its ML type (a bare type variable) does not.
       Prefer that over re-deriving from the ML type. *)
    match Option.bind scrut_db pattern_binder_type with
    | Some t when not (resolves_to_any_type t) -> t
    | _ ->
      cpp_of_ml env typ
  in
  (* Whether a {!Minicpp.Topaque} among the scrutinee's template arguments is
     a box.  [Topaque] only admits that the argument could not be resolved --
     but for an inductive Crane generates, the field that names it is written
     out, and {!Cpp_erasure.materialise} spells that declaration [std::any], so
     the value really is boxed.  A custom-extracted scrutinee has no such
     declaration: [std::optional<T>] is spelled by the mapping, and where the
     scrutinee is only ever bound to [auto] nothing wrote a box at all. *)
  let opaque_arg_is_a_box =
    match resolve_tmeta typ with
    (* ... unless the mapping's own type argument is one that erases: a family
       indexed by a value is spelled [std::any] in the instantiation, so the
       [std::optional<std::any>] the mapping produced really does hold a
       box. *)
    | Miniml.Tglob (g, args, _) ->
      not (Table.is_custom g) || List.exists (ml_erases_to_box env) args
    | _ -> true
  in
  (* Whether one of the scrutinee's template arguments holds a boxed value.
     This is the only question asked about an argument's erasure here, so it
     is settled once: [Topaque] is the sole case where being spelled
     [std::any] does not settle it, and it is decided above rather than
     re-decided at each site. *)
  let arg_is_a_box t =
    if t = Topaque then opaque_arg_is_a_box else resolves_to_any_type t
  in
  let scrut_template_args =
    let args = extract_template_args scrut_cpp_ty in
    (* One boxed argument means the whole instantiation was erased, so every
       argument is boxed -- the same rule the type-index cutoff applies to a
       [Tdummy Ktype] index, here for an argument erased because it mentions a
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
  let num_pv = Table.get_ctor_num_param_vars cname in
  (* The scrutinee's template argument that fixes this field's type, if the
     field's definition-site type is one of the inductive's own parameters.
     [Tapp (k, _)] counts: [sigT]'s payload field is written [P x], a
     parameter applied to the witness, and it is [P] that the instantiation
     pins down. *)
  let rec field_template_arg = function
    | Miniml.Tvar (_, k) | Miniml.Tapp (k, _) ->
      List.nth_opt scrut_template_args (k - 1)
    | Miniml.Tmeta {contents = Some t} -> field_template_arg t
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
          convert_ml_type_to_cpp_type (empty_env ()) ~ns:Refset'.empty [] def_ty
        in
        has_unnamed_tvar cpp_ty
      | None -> false
    else
      match field_arg field_i with
      | Some t -> arg_is_a_box t
      | None -> false
  in
  List.iteri (fun field_i _ ->
    let db_idx = n_pat_vars - field_i in
    if is_field_stored_as_any field_i then
      record_binder_type db_idx Tany;
    match field_arg field_i with
    | Some t -> record_binder_type db_idx t
    | None -> ()
  ) (List.init n_fields Fun.id)

(** The C++ type of the binder at de Bruijn index [i], for readers that have
    to produce an answer for every binder: the assignment made where it was
    bound, and failing that the conversion of its ML type under the current
    scope.

    The fallback is not a second opinion -- it is what the assignment
    deliberately declines to record.  {!assign_binder_types} keeps no entry
    when the conversion is [Topaque], a dummy, or fails outright, because
    recording those would state a fact it does not have.  Prefer
    {!binder_cpp_type} where [None] is a usable answer; this is for the
    places where it is not. *)
let binder_cpp_type_or_derive env i =
  match binder_cpp_type i with
  | Some _ as t -> t
  | None -> Option.map (cpp_of_ml env) (get_env_type_opt i)

(** Follow a name for a type through to the type it stands for.  A [using]
    alias hides the arguments its right-hand side was written with, and those
    arguments are exactly what a value built into such a slot has to agree
    with.  Returns the type unchanged when it is not an alias. *)
let rec unfold_cpp_typedef env cpp_ty =
  match cpp_ty with
  | Tnamespace (_, inner) -> unfold_cpp_typedef env inner
  | Tglob (GlobRef.ConstRef kn, args, _) -> (
    match Table.lookup_typedef_unchecked kn with
    | Some ml_ty ->
      (* A parameterised alias hides its arguments twice over: [texp T] stands
         for [(T * exp T)], so the one argument the name takes is not the two
         the [std::pair] behind it was written with.  Put the alias's own
         arguments back where its body's variables stand. *)
      let body = cpp_of_ml env ml_ty in
      (* The promoted variables the alias takes lead its argument list
         ({!ind_promoted_type_args}); the body's own variables come after. *)
      let n_promoted =
        let n = List.length (Table.promoted_type_params (GlobRef.ConstRef kn)) in
        if List.length args >= n + Mlutil.type_maxvar ml_ty then n else 0
      in
      if args = [] then body
      else
        Minicpp.subst_cpp_tvars
          (fun i -> if i >= 1 then List.nth_opt args (n_promoted + i - 1) else None)
          body
    | None -> cpp_ty )
  | _ -> cpp_ty

(** Whether an application reads its result out of a value that carries
    erasure.

    An accessor's ML result type says nothing on its own: the second component
    of a dependent pair is a bare type variable whatever the pair holds.  What
    decides is the value being projected from -- a [SigT<std::any, std::any>]
    hands back a box, a [SigT<List<uint64_t>, List<uint64_t>>] hands back a
    list.  So the arguments are the evidence, and each is asked at whichever
    is the better authority on its C++ type: the assignment made where a
    binder was bound, or the term's own ML type. *)
let app_reads_erased_value env args =
  let carries t =
    Ml_type_util.has_erased_type_in_type (unfold_cpp_typedef env t)
  in
  (* A typeclass dictionary is not one of the values the result is read out
     of: it is how the call states its type arguments, and C++ resolves the
     result through it. *)
  let is_dictionary a =
    match infer_ml_body_type (strip_magic a) with
    | Some ty -> (
      match resolve_tmeta ty with
      | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
      | _ -> false )
    | None -> false
  in
  List.exists
    (fun a ->
      if is_dictionary a then false
      else
      match strip_magic a with
      | MLrel i -> (
        match binder_cpp_type_or_derive env i with
        | Some t -> carries (strip_cpp_ref_const t)
        | None -> false )
      | a -> (
        match infer_ml_body_type a with
        | Some ty -> carries (cpp_of_ml env ty)
        | None -> false ) )
    args

(** Whether the pattern variable at de Bruijn index [i] holds a box, and so
    must be recovered with an [any_cast] before it is used at a concrete
    type.  Read off the recorded type rather than tracked alongside it: a
    binder is boxed exactly when the scrutinee's instantiation erased its
    field. *)
let binder_is_boxed i =
  (* [Topaque] prints as [std::any] but admits only that the representation is
     unknown here; nothing may be unboxed on the strength of it.  The
     distinction is {!coerce}'s, and a binder's answer has to draw it too. *)
  match binder_cpp_type i with
  | Some Topaque | None -> false
  | Some t -> resolves_to_any_type t

(** Record the C++ type of each of the [ids] most recently pushed binders,
    without pushing them again.  [?cpp] overrides the conversion for binders
    whose declared C++ type the caller has already computed; a declaration is
    always a better answer than re-deriving from the ML type, because it is
    what the emitted code actually says.  Call sites that only learn the
    declared types after pushing (a lambda decides [const auto &] for its
    erased parameters well after opening their scope) call this a second time
    to correct the assignment. *)
let assign_binder_types ?(cpp = []) env (ids : (Id.t * ml_type) list) =
  List.iteri
    (fun j (_, ml_ty) ->
      let assigned =
        match List.nth_opt cpp j with
        | Some (Some t) -> Some (strip_param_wrappers t)
        | _ -> (try Some (cpp_of_ml env ml_ty) with _ -> None)
      in
      match assigned with
      | Some t
        when t <> Topaque && not (is_cpp_dummy_type t)
             && not (pinned_by_pattern (j + 1)) ->
        tctx :=
          { !tctx with
            cpp_binder_types =
              IntMap.add (j + 1) (t, Bbinding) (!tctx).cpp_binder_types }
      | _ -> ())
    ids

(** [push_binders env ids] is {!push_env_types} plus the C++ type assignment:
    each binder's C++ type is decided here, once, at the point it is bound,
    and recorded in {!Translation_state.cpp_binder_types}.

    This is the assignment that use sites are being migrated onto.  Today they
    re-derive a binder's C++ type wherever they need it, from whatever type
    variable scope happens to be in effect, so two uses of one binder can
    disagree about whether it holds a box -- which is what a [bad_any_cast]
    is.  Deciding at the binding site makes that disagreement unrepresentable.

    [?cpp] overrides the conversion for a binder whose type the caller already
    knows better than its ML type says, which is the case for pattern
    variables: it is the scrutinee's instantiation, not the field's
    definition-site type, that fixes those.  A [None] entry (or a short list)
    falls back to converting the ML type.

    The assignment records only types it actually knows.  A conversion that
    yields [Topaque] means the scope could not resolve the binder at all, and
    a dummy stands for a value that is not there; recording either would turn
    ignorance into the assertion "this binder holds a box", which is the one
    thing {!Minicpp.Topaque} exists to refuse.  Such binders keep no entry, so
    a reader still falls through to whatever it does today.  Conversion
    failures are skipped for the same reason, and so that a binder Crane
    cannot currently type does not become a new way for extraction to fail. *)
let push_binders ?(cpp = []) env (ids : (Id.t * ml_type) list) =
  push_env_types ids;
  assign_binder_types ~cpp env ids

(** The type arguments the enclosing function's return type supplies for the
    inductive [ind], when it names [ind] with exactly [arity] of them.

    A constructor call for an inductive with dependent parameters has to
    instantiate the same template its caller expects, and the return type is
    where that expectation is recorded.  Namespace and [shared_ptr] wrappers
    are seen through, as are typedefs, which may name [ind] only indirectly.
    [None] when the return type says nothing about [ind]. *)
let expected_type_args_from_return env ?slot ind ~arity =
  let rec go cpp_ty =
    match cpp_ty with
    | Tglob (r, tys, _)
      when Names.GlobRef.CanOrd.equal ind r && List.length tys = arity ->
      Some tys
    | Tnamespace (_, inner) | Tshared_ptr inner -> go inner
    (* An element type counts: a value can be built into a slot the return
       type only mentions inside a container ([list {T : Type & T}]), and the
       arguments the container was declared with are what the element has to
       agree with. *)
    | Tglob (_, tys, _) when List.exists (fun t -> go t <> None) tys ->
      List.find_map go tys
    | Tglob (GlobRef.ConstRef kn, _, _) -> (
      match Table.lookup_typedef_unchecked kn with
      | Some ml_ty ->
        go (cpp_of_ml env ml_ty)
      | None -> None )
    | _ -> None
  in
  (* The slot the value is being built into is the closer answer, and the
     only one available inside a constructor argument -- generating those
     clears the enclosing return type. *)
  let r = match slot with
  | Some t when go t <> None -> go t
  | _ -> (
    match (!tctx).current_cpp_return_type with
    | Some rt -> go rt
    | None -> None ) in
  r

(** Collapse the erased parts of a type to [std::any]: the type itself when it
    resolves to [std::any], and, structurally, a function type's arguments and
    result.  Lets an expected type argument be compared against a computed one
    on equal terms, the computed side already being erased. *)
let rec normalize_erased_types = function
  | t when resolves_to_any_type t -> Tany
  | Tfun (ps, r) ->
    Tfun (List.map normalize_erased_types ps, normalize_erased_types r)
  | t -> t

(** [phantom_prefix_args id] is the list of template arguments a call to [id]
    has to spell out because [id]'s generated signature does not represent
    them: one filler per leading phantom parameter, as counted by
    {!Ml_type_util.explicit_tvar_prefix} off [id]'s declared type.

    The filler is [void] where the signature writes the parameter nowhere --
    nothing can then disagree with it -- and [std::any] where it does.  A
    return-only parameter is the second case: it is undeducible, so the call
    must still spell it, but [void] there is not a filler but a claim, and
    [ITree<void>] is one the body goes on to contradict.

    The declaration emitter counts the same run and leaves those parameters
    undefaulted, so the two stay in step without either recording anything for
    the other -- which matters because a call can precede its callee's
    declaration (mutual recursion, forward references). *)
let phantom_prefix_args id =
  match find_type_opt id with
  | None -> []
  | Some ml_ty ->
    let cty =
      convert_ml_type_to_cpp_type (empty_env ()) [] (type_simpl ml_ty)
    in
    let force_required = collect_ml_type_index_tvars ml_ty in
    List.init (explicit_tvar_prefix ~force_required cty) (fun _ -> Tvoid)

(** Make an explicit argument list as long as {!writable_tvar_count} says the
    callee's parameter list is.

    Extraction and C++ disagree at both ends.  A Rocq application can carry an
    argument for a variable the declaration never got -- an erased index -- and
    writing it overruns the list.  It can also be missing the leading ones,
    which erasure dropped before the call was built; those are exactly the
    positions {!phantom_prefix_args} has fillers for, and without them the
    arguments that remain are read at the wrong positions.

    An empty list is left empty: a call that writes nothing is asking for
    deduction, and it is only a call already committed to writing its
    arguments that has to get their count right. *)
let fit_to_declared_tvars id targs =
  match declared_tvar_count id with
  | Some n when n < List.length targs ->
    List.filteri (fun i _ -> i < n) targs
  | Some n when targs <> [] && n > List.length targs ->
    let missing = n - List.length targs in
    let fillers = phantom_prefix_args id in
    if List.length fillers < missing then targs
    else List.filteri (fun i _ -> i < missing) fillers @ targs
  | _ -> targs

(** The explicit type arguments a call needs when the callee is generic in a
    type {e constructor} and Rocq erased which one.

    A higher-kinded class parameter reaches the call as [Tdummy]: the carrier
    of [TFunctor (fun T => T * box T)] is a term Rocq computed away.  C++
    deduces the parameter from the value argument instead, by matching
    [T1<T2>] against the argument's type -- which works exactly when the
    carrier is a template name applied to one argument, and fails outright
    when it is not: [std::pair<Nat, Box<Nat>>] deduces [T1 = std::pair], a
    binary template where a unary one was declared.

    The carrier is recovered from the type the result is expected to have.
    The callee returns [Tapp (p, [Tvar v])] -- the carrier at position [p]
    applied to the variable at position [v] -- so abstracting the expected
    result over whatever [v] was instantiated to inverts that application.
    {!Minicpp.abstract_cpp_type} writes the sentinel the printer mints an
    alias template for, and only position [p] is written: the rest deduce
    through the alias, which is transparent.

    Nothing is claimed where the abstraction does not fire.  If [v]'s
    instantiation does not occur in the result then the carrier is constant in
    its argument and the result says nothing about it, and if the result type
    is unknown there is nothing to read. *)
let hkt_carrier_type_args env tvars ?result id tys =
  let ( let* ) = Option.bind in
  let* ml_ty = find_type_opt id in
  let* p, v =
    match resolve_tmeta (ml_return_type ml_ty) with
    (* Only a leading carrier is written: an explicit argument list is
       positional, so a carrier further in would need every argument before it
       spelled as well, and a class parameter is always quantified first. *)
    | Miniml.Tapp (1, [Miniml.Tvar (_, v)]) -> Some (1, v)
    | _ -> None
  in
  let* () =
    match List.nth_opt tys (p - 1) with
    | Some (Miniml.Tdummy _) -> Some ()
    | _ -> None
  in
  let* v_ml = List.nth_opt tys (v - 1) in
  let* result =
    match result with None -> (!tctx).current_cpp_return_type | r -> r
  in
  let over = template_arg_of_ml_type env tvars v_ml in
  let* carrier = Minicpp.abstract_cpp_type ~over result in
  (* A carrier that is one template applied to the argument is left to
     deduction, which reads it off the value argument and gets it right.  Only
     a carrier with no head to read -- a composite, or a partial application --
     has to be written, and it is written alone: everything after it deduces
     through the alias, which is transparent. *)
  let sentinel = Minicpp.Thole in
  let rec is_plain_head = function
    (* A namespace or a const/reference wrapper is spelling, not structure. *)
    | Minicpp.Tnamespace (_, t) | Minicpp.Tconst t | Minicpp.Tref (Minicpp.Lvalue, t)
    | Minicpp.Tref (Minicpp.Forwarding, t) ->
      is_plain_head t
    | Minicpp.Tglob (_, [arg], _)
    | Minicpp.Tid (_, [arg])
    | Minicpp.Tid_external (_, [arg])
    | Minicpp.Tapply (_, [arg]) ->
      arg = sentinel
    | _ -> false
  in
  if is_plain_head carrier then None else Some [Minicpp.Ttyctor carrier]

(** The explicit type arguments a call to a lifted helper has to carry.

    Lifting turns the body's type variables into template parameters of a new
    top-level function, and a parameter that occurs only in the {e return}
    type is deducible from nothing: the call must spell it or the overload is
    discarded.  [binder_ty] is the lifted thing's own ML type, whose codomain
    is matched against the enclosing function's C++ return type to say what
    each variable beyond [outer_tvars] stands for at this call.

    What the parameters already spell is left to deduction, because one
    explicit list stands for every reference while the instantiations need not
    agree -- a polymorphic local helper may be used at two types in one body.
    Explicit arguments are positional, so only a trailing deducible run can be
    dropped.

    Both lift paths ask this, and the only difference between them is where
    the type and the parameters come from. *)
let lifted_call_type_args
    ~class_args ~env ~outer_tvars ~head ~all_tvar_names ~binder_ty ~param_ml_tys =
  (* Only what the declaration's head still declares can be named; [None]
     where the head is every variable. *)
  let in_head id =
    match head with
    | None -> true
    | Some h -> List.exists (Id.equal id) h
  in
  let outer_tvars = List.filter in_head outer_tvars in
  let all_tvar_names = List.filter in_head all_tvar_names in
  class_args
  @
  let extra_tvar_names =
    List.filter
      (fun id -> not (List.exists (Id.equal id) outer_tvars))
      all_tvar_names
  in
  if extra_tvar_names = [] then
    List.map (fun id -> named_tvar id) outer_tvars
  else
    let tmpl_cod =
      match convert_ml_type_to_cpp_type env all_tvar_names binder_ty with
      | Tfun (_, cod) -> cod
      | t -> t
    in
    let tvar_map =
      match (!tctx).current_cpp_return_type with
      | Some conc_ret -> extract_tvar_map tmpl_cod conc_ret
      | None -> []
    in
    let args =
      List.map (fun id -> named_tvar id) outer_tvars
      @ List.map
          (fun tvar_name ->
            match
              List.find_opt (fun (id, _) -> Id.equal id tvar_name) tvar_map
            with
            | Some (_, ty) -> ty
            | None -> (
              match (!tctx).current_cpp_return_type with
              | Some ret_ty -> ret_ty
              | None -> named_tvar tvar_name ) )
          extra_tvar_names
    in
    let deducible =
      List.concat_map
        (fun ml_ty ->
          get_tvars (convert_ml_type_to_cpp_type env all_tvar_names ml_ty) )
        param_ml_tys
    in
    if List.length all_tvar_names <> List.length args then
      args
    else
      let rec strip = function
        | [] -> []
        | (id, ty) :: rest -> (
          match strip rest with
          | [] when List.exists (Id.equal id) deducible -> []
          | rest -> (id, ty) :: rest )
      in
      List.map snd (strip (List.combine all_tvar_names args))

(** The carrier of a higher-kinded class parameter, read off the {e dictionary}
    the call passes for that class.

    {!hkt_carrier_type_args} recovers a carrier from the type the result is
    expected to have, which needs the result to mention it.  An instance
    {e method} for a nested functor does not qualify: [TFunctor_list']'s result
    is [list (T1 B)], and by the time the call is built the expected type has
    already erased the element to [std::any], so there is nothing left to
    abstract over.

    What still knows the carrier is the dictionary argument.  A parameter of
    class type -- [TFunctor T1] -- is instantiated by the instance for exactly
    one type constructor, and that instance's method returns [T1] applied: the
    dictionary for [box] is a function whose codomain is [box B].  So the head
    of the dictionary's codomain {e is} the carrier.

    The dictionary reaches the call wrapped in the adapter lambda that erases
    its arguments, so the instance is found by descending to the head of the
    lambda's body.  It need not be an instance at all: where the enclosing
    function abstracts over the instance, the dictionary is a binder, and the
    carrier is written in the constraint that binder's own type spells.  Both
    sources end at an ML type headed by the carrier, and are consumed as one.

    Nothing is claimed when neither source yields a type, or when that type is
    not an application -- a carrier has to be applied to something to be one.

    Written unconditionally, unlike the result route: [T1] here occupies a
    non-deduced position ([std::type_identity_t<TFunctor<T1>>], and [T1<std::any>]
    against an already-erased argument), so even a carrier that is a plain
    template name has to be named rather than left to deduction. *)
let dict_carrier_type_args env tvars id args =
  let ( let* ) = Option.bind in
  let* cod = dict_carrier_ml_type id args in
  (* Abstracted over the traversed type, as {!apply_hkt_tyctors} does: the
     class applies its carrier to it and this idiom writes it first, so the two
     agree on one body and the printer mints one alias for both.

     The carrier need not apply to it {e directly}.  A composed carrier
     [fun t => option (Exp t)] reaches it through the constructors it composes,
     and the codomain's leading argument is then [Exp t] rather than [t];
     abstracting over that yields [option] alone -- the composition's outer
     head, which is the arity deduction would have guessed and precisely what
     a composition is not.  So the leading arguments are descended to the type
     that is not itself an application: that is what the whole composition is
     applied to, and where the carrier is a plain head the descent stops at
     once.

     Descended only where the composition is fully known.  An occurrence
     {!apply_carrier} declined to fill is left as the [Tapp] it was, and by
     then nothing tells it apart from one that was recovered; writing it out
     spells a carrier built partly from a class parameter that is in scope and
     is not the one meant.  There the leading argument is abstracted over as
     before, which yields the outer head alone -- still wrong, but wrong the
     way deduction is wrong, and absorbed wherever a converting constructor
     absorbs it.  A wrong spelling is worse than an unrecovered one.

     Only occurrences among the {e arguments} count.  The head may be a [Tapp]
     and be right: a carrier that {e is} a class parameter is written as that
     parameter, which the enclosing declaration has in scope. *)
  let rec unrecovered t =
    match resolve_tmeta t with
    | Miniml.Tapp _ -> true
    | Miniml.Tglob (_, targs, _) -> List.exists unrecovered targs
    | _ -> false
  in
  (* Which argument the composition is applied {e in}, which is a different
     question from how far to descend and only looks like the same one while
     every constructor in the chain takes a single argument.  The carrier is
     the method's codomain abstracted over the variable the method quantifies,
     so the argument to follow is the one that variable occurs in:
     [fun t => list (nat * Exp t)] reaches it through the {e second} component
     of the pair, and following the leading argument abstracts over [nat]
     instead -- a carrier of the right shape, varying in the wrong place, which
     nothing downstream can tell from the right one. *)
  let rec mentions_traversed t =
    match resolve_tmeta t with
    | Miniml.Tunknown | Miniml.Tvar _ -> true
    | Miniml.Tglob (_, targs, _) | Miniml.Tapp (_, targs) ->
      List.exists mentions_traversed targs
    | Miniml.Tarr (a, b) -> mentions_traversed a || mentions_traversed b
    | _ -> false
  in
  let rec traversed t =
    match resolve_tmeta t with
    | Miniml.Tglob (_, (t0 :: _ as targs), _)
    | Miniml.Tapp (_, (t0 :: _ as targs)) ->
      (* No argument mentioning it means there is nothing better to say than
         what the leading one says, which is what this did before. *)
      traversed (Option.default t0 (List.find_opt mentions_traversed targs))
    | t -> t
  in
  let* over =
    match resolve_tmeta cod with
    | Miniml.Tglob (_, (t0 :: _ as targs), _)
    | Miniml.Tapp (_, (t0 :: _ as targs)) ->
      let whole = if List.exists unrecovered targs then t0 else traversed cod in
      Some (template_arg_of_ml_type env tvars whole)
    | _ -> None
  in
  let* carrier =
    Minicpp.abstract_cpp_type ~over (template_arg_of_ml_type env tvars cod)
  in
  Some [Minicpp.Ttyctor carrier]

(** Spell the erased arguments of [id]'s phantom prefix with the fillers
    {!phantom_prefix_args} gives them.

    An erased argument normally costs a call its whole explicit argument list:
    the positions are what give the others their meaning, so one that cannot be
    written drops all of them ({!Ml_type_util.filter_erased_type_args}).  A
    phantom position is the exception, because it has a filler that is right
    whatever the argument was -- the signature does not mention the parameter,
    so nothing can disagree with [void] -- and the arguments after it keep
    their positions.

    This is what an erased {e event} needs.  A single event family reaches C++
    as its own struct and is written as itself, but a sum ([E +' F]) has no
    spelling; without the filler, [raise]'s result type goes unwritten too, and
    it appears only in the return position, where nothing can deduce it. *)
let fill_phantom_prefix id targs =
  let fillers = phantom_prefix_args id in
  List.mapi
    (fun i t ->
      match List.nth_opt fillers i with
      | Some f when prints_as_any t -> f
      | _ -> t )
    targs

(** Whether [e] denotes a value whose ML type is a function (at least one value
    arrow).  Used to decide, at a constructor argument that is stored into an
    erased ([std::any]) field, whether to route it through the [crane_erase_fn]
    runtime helper so the canonical [std::function<std::any(std::any...)>]
    representation is stored (matching the [any_cast] on the application side)
    rather than a raw closure.  An [MLrel] already erased to [std::any]
    ([binder_is_boxed]) is excluded: it is not callable, so wrapping it
    would miscompile. *)
let ml_expr_is_function_value e =
  match strip_magic e with
  | MLrel i ->
    (not (binder_is_boxed i))
    && ( match get_env_type_opt i with
       | Some t -> count_ml_value_arrows t >= 1
       | None -> false )
  (* A partial application of a global whose codomain mentions a
     value-dependent erased type (e.g. [mk_action n : domty n -> bool]) is
     wrapped in [MLmagic] by the kernel's typing coercion even at the
     application node itself, not just around the whole expression — so
     [strip_magic] above (which only strips the outer expression) does not
     expose the [MLglob] underneath. Look through it here, locally, rather
     than in [infer_ml_body_type] itself (whose result also feeds unrelated
     callers like lambda return-type annotation), so this fix cannot change
     behavior anywhere but function-value detection. *)
  | MLapp (MLmagic (_, f), args) ->
    ( match infer_ml_body_type (MLapp (f, args)) with
    | Some t -> count_ml_value_arrows t >= 1
    | None -> false )
  | other ->
    ( match infer_ml_body_type other with
    | Some t -> count_ml_value_arrows t >= 1
    (* Inference is best-effort and gives up when a binder's type is itself a
       type-level computation ([sem (TArr a b)] for a [Fixpoint sem : ty ->
       Type]).  A syntactic lambda is a function value whatever its type, so
       fall back on the shape rather than on the failed inference. *)
    | None -> ( match other with MLlam _ -> true | _ -> false ) )

(** [is_boxed_source t] -- whether a value whose C++ type is [t] is
    physically inside a [std::any], and so may be read back out with an
    [any_cast].

    {!Ml_type_util.is_boxed_type} answers this structurally, which misses a
    named alias for the box: a [Type]-valued definition is emitted as
    [using sel = std::any], and only following the alias chain reveals that a
    parameter of type [sel] is a box.  {!Minicpp.Topaque} is deliberately
    excluded -- it prints as [std::any] without promising one, so nothing may
    be cast out of it. *)
let is_boxed_source t =
  is_boxed_type t
  || (match t with
      | Topaque -> false
      | Tglob _ -> resolves_to_any_type t
      | _ -> false)

(** [classify_erasure ty] -- the erasure status of one side of a value
    boundary, as the single question worth asking about it.

    Three answers are easy to confuse, and the difference decides whether a
    value may be boxed, [any_cast] out of, or left alone:

    - [`Unknown] -- the type was not tracked. Boxing into such a slot is
      allowed; casting {e out} of it never is, since nothing says a box is
      there.
    - [`Boxed] -- the value really is inside a [std::any], so an [any_cast]
      recovers it.  Follows alias chains: a [Type]-valued definition emitted
      as [using sel = std::any] is a box under a name.
    - [`Opaque] -- spelled [std::any] but promising nothing about the
      representation ({!Minicpp.Topaque}).  Distinct from [`Unknown]: there
      the type is untracked, here it is untrackable.  Nothing may be boxed or
      cast on the strength of it.
    - [`Concrete t] -- an ordinary type.

    Prefer this to assembling an answer out of {!Ml_type_util.prints_as_any},
    {!Ml_type_util.is_boxed_type} and {!resolves_to_any_type} at each site:
    those sit at different layers (see [ml_type_util.mli]) and a site that
    picks the wrong one silently gets [false]. *)
let classify_erasure = function
  | None -> `Unknown
  | Some f when is_boxed_source f -> `Boxed
  | Some f when prints_as_any f -> `Opaque
  | Some f -> `Concrete f

(** [spells_as_any t] -- whether [t] is written [std::any] in the generated
    code, following the alias chains that {!Ml_type_util.prints_as_any}, being
    structural, cannot see through. *)
let spells_as_any t = prints_as_any t || resolves_to_any_type t

(** [coerce ?term ?from ~into expr] adapts [expr] across a representation
    boundary: it is the single place that decides between boxing, [any_cast],
    [crane_erase_fn] and doing nothing.

    It first classifies the source side as boxed, opaque, concrete or unknown,
    and then reads the answer off that.  The classification rests on
    {!Ml_type_util.is_boxed_type}, not on {!Ml_type_util.prints_as_any}:
    {!Minicpp.Topaque} also prints as [std::any], but it is an admission that
    the representation is unknown, and nothing may be boxed or cast on the
    strength of it.  A boundary with a [Topaque] on either side is therefore
    left alone, for the representation-tolerant helpers in [crane_fn.h] to
    sort out at instantiation time.  The pointer dimension (bare value versus
    [shared_ptr]) is delegated to {!gen_type_conversion_expr}, which already
    handles it.

    Omit [from] where the value's C++ type is not tracked -- a freshly
    generated constructor argument, say.  The value is then taken to be
    concrete but unnamed, which licenses boxing it (boxing any value is
    well-formed) but never an [any_cast] out of it, which would be a claim
    about a representation we cannot see.

    [term] is the ML expression [expr] was generated from.  It is consulted
    only for the one question a missing [from] leaves open: whether the value
    is a function, and so has to be adapted by [crane_erase_fn] before it is
    boxed. *)
let rec coerce ?term ?from ~into expr =
  let source = classify_erasure from in
  let same_type = match from with Some f -> cpp_ty_eq f into | None -> false in
  if same_type || into = Tvoid then expr
  else
    match source with
    (* Casting a box to a name that is itself the box is not a recovery but
       an [any_cast<std::any>], which only succeeds on a doubly-boxed value
       and otherwise throws. *)
    | `Boxed when spells_as_any into -> expr
    (* A closure built here is not a box, whatever its erased type says: what
       is boxed is what it returns -- [@id lit] eta-expanded, with [id : ID]
       erased to [std::any id(std::any)], read at [Endo<lit>].  Its returns
       are recovered at the codomain instead. *)
    | `Boxed when (match expr with CPPlambda _ -> true | _ -> false) -> (
      match (expr, unfold_cpp_typedef (empty_env ()) into) with
      | CPPlambda l, Tfun (_, cod) ->
        let rec at_returns = function
          | Sreturn (Some e) -> Sreturn (Some (coerce ~from:Tany ~into:cod e))
          | st -> map_stmt Fun.id at_returns Fun.id st
        in
        CPPlambda
          { l with
            cl_ret =
              (match l.cl_ret with Some t when prints_as_any t -> Some cod | r -> r);
            cl_body = List.map at_returns l.cl_body }
      | _ -> expr )
    (* Already recovered; a second cast would be reading the same box twice. *)
    | `Boxed -> (
      match expr with
      | CPPany_cast _ -> expr
      | _ -> (
        (* A list went into the box with its elements boxed, so that is the
           shape the cast has to name however concrete the context's element
           type is; the converting constructor then recovers each element. *)
        match Cpp_erasure.erased_list_shape into with
        (* A custom list has no converting constructor to unbox its elements
           with, so it stays at the flat shape until a consumer converts it. *)
        | Some (g, shape) when Table.is_custom g -> Cpp_erasure.unbox shape expr
        | Some (_, shape) ->
          Cpp_erasure.converting_ctor into [Cpp_erasure.unbox shape expr]
        | None -> Cpp_erasure.unbox into expr ) )
    (* Nothing may be boxed or cast on the strength of an admission that the
       representation is unknown. *)
    | `Opaque -> expr
    | (`Unknown | `Concrete _) as concrete_source ->
      let is_function_value =
        match concrete_source with
        | `Concrete (Tfun _) -> true
        | `Concrete _ -> false
        | `Unknown -> (
          match term with Some t -> ml_expr_is_function_value t | None -> false )
      in
      if is_boxed_type into then
        (* Boxing is not idempotent: [std::any] holding a [std::any] is a box
           no consumer opens twice. *)
        match expr with
        | CPPbox (Tany, _) | CPPany_cast (Tany, _) -> expr
        | _ ->
          (* A closure does not survive as itself: the consumer recovers it with
             [any_cast<std::function<std::any(std::any...)>>], so it is adapted
             to that canonical shape first.  It is then boxed like any other
             value -- a custom constructor template such as [std::make_pair]
             deduces its field type from the argument, and an unboxed
             [std::function] would store [pair<any, function<any(any)>>] where
             the consumer expects [pair<any,any>]. *)
          let adapted =
            if is_function_value then
              wrap_crane_erase_fn (erased_fn_instantiation expr)
            else expr
          in
          Cpp_erasure.converting_ctor Tany [adapted]
      else
        match into with
        (* A slot that erased its domain -- a record field whose Rocq type is
           [dty -> nat] at a value-dependent [dty], so
           [std::function<uint64_t(std::any)>] -- does not accept a closure
           written at the concrete domain, nor a generic lambda (which has no
           signature to convert from).  It takes one through the same
           [crane_erase_fn] adapter an erased parameter uses, whether or not the
           result erased along with the arguments. *)
        | Tfun (_, cod) when is_function_value && erased_domain_fun_ty into ->
          wrap_crane_erase_fn ~ret_ty:cod expr
        (* The mirror image: a callable whose result erased -- a constant
           whose Rocq type hides its quantifier behind a type alias, or whose
           result a type index alone pins down -- reaching a slot that names
           that result concretely.  It is called through a lambda that gives
           each argument the shape the callable declares and recovers what it
           returns. *)
        | Tfun (dom, cod)
          when (not (prints_as_any cod))
               && ( match concrete_source with
                  | `Concrete (Tfun (_, scod)) -> prints_as_any scod
                  | _ -> false ) ->
          let sdom, scod =
            match concrete_source with
            | `Concrete (Tfun (d, c)) -> (d, c)
            | _ -> ([], Tany)
          in
          let params = adapter_params ~prefix:"_ue" dom in
          let args =
            List.mapi
              (fun i ((ty, _) as p) ->
                let into = Option.default Tany (List.nth_opt sdom i) in
                coerce ~from:ty ~into (adapter_arg p) )
              params
          in
          let call = coerce ~from:scod ~into:cod (mk_call expr args) in
          mk_lambda params None [Sreturn (Some call)] ~capture:Closure
        | _ -> (
          match concrete_source with
          | `Concrete f when not (prints_as_any into) ->
            gen_type_conversion_expr ~src_ty:f ~dst_ty:into expr
          | _ -> expr )

(** Whether a coercion is one the Rocq indices rule out, rather than one C++
    can perform.

    Extraction records [Mcoerce (unit, nat)] for the [vnil] branch of a match
    on [vec (S n)] whose [return] clause computes [unit] there: a branch whose
    type differs from the type the match was instantiated at is one the
    scrutinee's index makes impossible.  [unit] is where this shows up
    unambiguously -- it carries no information, so no value of it can be
    converted to anything else, and a position holding one at another type can
    only be a position that is never reached.  What it returns is immaterial,
    and the only thing writable at an impossible type is an abort.

    The mirror is {!Gen_decls.dead_unit_returns_to_abort}, which catches the
    same branch where extraction recorded no coercion at all and a bare [tt]
    reaches a [return]; both throw {!Minicpp.dead_branch_message}. *)
let absurd_coercion from into =
  Ml_type_util.ml_type_is_unit from
  && (not (is_cpp_unit_type into))
  && into <> Tvoid
  && not (resolves_to_any_type into)

(** Adapt a function value being stored into a slot whose C++ type is the
    erased [std::any].  The application side reads such a callable back with
    [any_cast<std::function<std::any(std::any...)>>], so the producer must
    store that same canonical representation rather than the raw closure --
    which is what the [crane_erase_fn] runtime helper builds, deducing the
    callable's signature with [std::function] CTAD.  Non-function values are
    returned unchanged. *)
let erase_fn_for_any_slot e expr =
  if ml_expr_is_function_value e then wrap_crane_erase_fn expr else expr

(** True when environment variable at de Bruijn index [i] has an erased C++
    type (i.e. [std::any] or a dummy type, arising from dependent-parameter
    collapse).  Returns [false] if [i] is out of range.

    This deliberately converts the binder's ML type under [tvars] rather than
    reading {!binder_cpp_type}, and it is not a re-derivation of the binding
    site's answer: the two say different things, and callers pair them
    precisely to tell those things apart.  A binder the assignment types
    concretely, whose ML type is an out-of-scope variable, is a value held in
    a box under a concrete static type -- exactly the one that has to be
    unboxed.  Reading the assignment here would collapse the contrast and
    drop the [any_cast] (measured: [existential_erased_apply_bad_cpp] and
    [list_cons_erasure_bleed] stop casting). *)
let is_env_var_erased env tvars i =
  match get_env_type_opt i with
  | Some ml_ty ->
    prints_as_any (convert_ml_type_to_cpp_type env tvars ml_ty)
  | None -> false

(** Check whether an ML expression's C++ type is erased ([std::any]).
    Used by the [MLmagic] handler to decide whether [any_cast] is needed. *)
let rec ml_expr_is_erased env (t : ml_ast) : bool =
  let tvars = get_current_type_vars () in
  match t with
  | MLrel i -> is_env_var_erased env tvars i
  | MLapp (f, args) ->
    let n_value_args =
      List.length (List.filter (fun a ->
        match a with MLdummy _ -> false | _ -> true) args)
    in
    let ml_ty_opt = match f with
      | MLglob (r, _) -> find_type_opt r
      | MLrel i -> get_env_type_opt i
      | _ -> None
    in
    ( match ml_ty_opt with
      | Some ml_ty -> ml_codomain_erases_to_any n_value_args ml_ty
      | None -> false )
  | MLglob (r, _) ->
    ( match find_type_opt r with
      | Some ml_ty -> prints_as_any (cpp_of_ml env ml_ty)
      | None -> false )
  | MLmagic (_, inner) -> ml_expr_is_erased env inner
  | MLcase (case_ty, _, _) ->
    ( match case_ty with
      | Miniml.Tvar (_, _) | Miniml.Tunknown -> true
      | _ -> false )
  | _ -> false

(** The C++ type a read of record field [fld] has, out of a value of ML type
    [typ]: the field's declared type at the record's instantiation, stored as
    the record stores it.  [None] where [typ] is not a record naming [fld]. *)
let record_field_cpp_ty env typ fld =
  match resolve_tmeta typ with
  | Miniml.Tglob (r, args, _) -> (
    let declared =
      List.find_map
        (fun (f, ty) ->
          match f with
          | Some f when GlobRef.CanOrd.equal f fld -> Some ty
          | _ -> None )
        (Table.record_field_bindings_of_type typ)
    in
    match declared with
    | Some ml_ty -> (
      try
        Some
          (convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton r)
             (get_current_type_vars ())
             (Mlutil.type_subst_list args ml_ty))
      with e when CErrors.noncritical e -> None )
    | None -> None )
  | _ -> None

(** [recover_boxed_component into e] opens the box when [e] is evidently a
    component read out of a pair that was recovered from one.  The context's
    type [into] is what the value is declared to be; the emitted expression is
    the evidence that it is physically a [std::any]. *)
let recover_boxed_component into e =
  if yields_boxed_component e then coerce ~from:Tany ~into e else e

(** Whether an [MLmagic] node says its subterm is physically inside a
    [std::any] here, and so has to be opened before it can be used.

    A [Mbarrier] carries no type gap at all.  An [Mcoerce] is a box only when
    one of its two types erases at this instantiation: a coercion between two
    types that are both written down concretely -- a typeclass carrier
    resolved by the instance being generated, say -- is a static mismatch the
    C++ types already agree on, and casting on account of it would read a box
    that was never built. *)
let magic_is_boxed env = function
  | Mboxed -> true
  | Mbarrier -> false
  | Mcoerce (from, into) ->
    let erases ty = ml_erases_to_box env ty in
    erases from || erases into

(** [recover_erased_scrutinee env ~is_magic typ expr] casts a scrutinee that is
    carried at runtime as [std::any] -- an existential witness, say -- back to
    [typ], the inductive recovered from the branch patterns.  Neither the
    [switch] of an enum match nor the [v()] of a variant match is applicable to
    a [std::any].  When [typ] itself erases there is nothing to recover to and
    the scrutinee is returned unchanged. *)
let recover_erased_scrutinee env ~is_magic typ expr =
  if not is_magic then expr
  else
    let cpp_ty =
      cpp_of_ml env typ
    in
    if prints_as_any cpp_ty then expr else Cpp_erasure.unbox cpp_ty expr

(** Build the qualified constructor struct type for a pattern match branch.

    For [list<int>::Cons], this produces
    [Tqualified(Tnamespace(r, Tglob(r, temps, \[\])), ctor_name)].
    Local inductives omit the namespace wrapper to avoid double qualification. *)
let ctor_type_of_match env (typ : ml_type) (cname : GlobRef.t) : cpp_type =
  let ctor_name = ctor_struct_id_of_ref cname in
  match typ with
  | Tglob (r, tys, _) ->
    let tys = List.map type_simpl tys in
    let tys =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Table.get_ind_num_param_vars_opt kn with
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
              (fun _ -> Miniml.Tunknown)
        | None -> tys )
      | _ -> tys
    in
    (* The constructor struct is nested in the instantiation, so it has to be
       qualified by the same one the declaration spells. *)
    let temps =
      ind_promoted_type_args r
      @ apply_hkt_tyctors r (template_params_of_ml env tys)
    in
    let is_local_ind =
      List.exists
        (globref_equal r)
        (get_local_inductives ())
    in
    let ind_type =
      if is_local_ind then Tglob (r, temps, [])
      else Tnamespace (r, Tglob (r, temps, []))
    in
    Tqualified (ind_type, ctor_name)
  | _ -> Tid (ctor_name, [])

(** [recover_boxed_result ~boxed ~expected expr] casts the result of a call
    back into the type the position expects -- see {!position_cpp_ty} -- when
    [boxed]
    says the callee hands back a [std::any] whatever its ML type claims,
    because its codomain erases or because it was itself recovered from a box
    and so goes through the canonical [std::function<std::any(std::any...)>]
    adapter.

    [boxed] is a statement about the callee, not a guess, so the recovery is
    unconditional: unlike {!unbox_into} it casts at a template parameter too,
    which inside a template is the one name the result has. *)
let recover_boxed_result ~boxed ~expected expr =
  match position_cpp_ty expected with
  | Some into when boxed -> coerce ~from:Tany ~into expr
  | _ -> expr

(** [unbox_value into e] recovers [e], a value known to come out of a box, at
    [into]: {!coerce} from [std::any]. *)
let unbox_value into e = coerce ~from:Tany ~into e

(** [unbox_into into e] recovers [e] from its box at [into], where the position
    stated a type to recover it at, and leaves it boxed otherwise. *)
let unbox_into into e =
  match into with
  | Some into when states_unboxed_target into -> coerce ~from:Tany ~into e
  | _ -> e
