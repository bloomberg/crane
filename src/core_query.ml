(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What Core elaboration asks of a term, its types and the table, and
    translation asks too: a global's recorded type, the role of a parameter,
    the type variables a call's arguments instantiate or a C++ compiler
    deduces, how a let-bound lambda is generated, which arguments are class
    dictionaries, and where a class-field call projects statically.  Nothing
    here reads translation's state or builds C++: {!Core_elaborate} plans on
    it before translation runs. *)

open Miniml
open Names
open Mlutil
open Table
open Util
open Ml_type_util

(** {!Table.find_type}, [None] where [r] has no recorded type. *)
let find_type_opt (r : GlobRef.t) : ml_type option =
  try Some (Table.find_type r) with Not_found -> None

(** A declaration's parameter of type [ty] is its dictionary exactly when
    [ty] is a class: the one criterion the head generators promote a
    parameter to an instance by. *)
let parameter_role ty = if Table.is_typeclass_type ty then Lexenv.Dictionary else Lexenv.Value

(** Like [List.firstn] but returns [min(n, length lst)] elements instead of
    raising when [n > length lst]. Needed because extraction sometimes produces
    type argument lists shorter than expected (due to [Tdummy Ktype] erasure,
    higher-kinded extraction failures, or universe polymorphism).

    @param n    number of elements to take (must be >= 0)
    @param lst  input list
    @return prefix of [lst] with length [min(n, length lst)] *)
let safe_firstn n lst =
  let rec aux n lst acc =
    match n, lst with
    | 0, _ | _, [] -> List.rev acc
    | n, hd::tl -> aux (n-1) tl (hd::acc)
  in
  aux n lst []

(** Collect all Tvar indices from an ml_type. Used to find type variables beyond
    those of the containing inductive/record. *)
let collect_tvars_set acc ty = IntSet.union acc (Mlutil.ml_tvars ty)

(** Convert an IntSet of type variable indices back to a list, wrapping
    [collect_tvars_set]. Used to collect all Tvar indices from an ml_type. *)
let collect_tvars acc ty =
  IntSet.elements (collect_tvars_set (IntSet.of_list acc) ty)

(** [reconcile_parameter_type body_ty sig_ty] -- the type a definition's
    parameter is bound at in its body, from the type its lambda is annotated
    with, [body_ty] (unified with the signature's), and the type the
    definition's signature gives it, [sig_ty].

    A [Tunknown] in the annotation is the signature's: a promoted dependent
    record's lambda leaves the erased carrier unknown, where the signature
    has [Tglob (m_carrier, \[\])], which converts.

    The signature's type replaces the annotation outright only where the
    signature has fewer arrows -- a type alias like [State S A = S -> A * S]
    expands to extra ones, and binding the parameter at the alias lets inner
    call sites see an over-application and chain it ([f(a)(s')], not
    [f(a, s')]) -- or names a type alias taking promoted parameters
    ([FusedS := state * ...] under [Existing Instance], declared [template
    <typename ptr>]): its body names class fields only the alias's own
    parameters resolve, so the expansion spells them erased.  Not
    unconditionally, because the definition's parameter types would then
    differ from the declaration's, which [gen_sfun] spells from the expanded
    types. *)
let reconcile_parameter_type body_ty sig_ty =
  let rec merge_unknown body_ty sig_ty =
    match (body_ty, sig_ty) with
    | Miniml.Tunknown, _ -> sig_ty
    | Miniml.Tglob (r1, ts1, a1), Miniml.Tglob (r2, ts2, _)
      when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
      Miniml.Tglob (r1, List.map2 merge_unknown ts1 ts2, a1)
    | Miniml.Tarr (t1a, t1b), Miniml.Tarr (t2a, t2b) ->
      Miniml.Tarr (merge_unknown t1a t2a, merge_unknown t1b t2b)
    | _ -> body_ty
  in
  let promoted_alias t =
    match Mlutil.type_simpl t with
    | Miniml.Tglob ((GlobRef.ConstRef _ as g), _, _) -> Table.promoted_type_params g <> []
    | _ -> false
  in
  let body_ty = merge_unknown body_ty sig_ty in
  if count_ml_arrows body_ty > count_ml_arrows sig_ty || promoted_alias sig_ty then sig_ty
  else body_ty

(** The type variables a type spells out in a deducible position.  A
    function-typed parameter reaches C++ as an opaque template parameter [F0]
    rather than as a written-out signature, so a variable occurring only
    inside one -- the callback's own codomain, say -- is in no deducible
    context; every other parameter spells its type out. *)
let rec spelled_tvars_of ?(plain = fun _ -> false) acc = function
  | Miniml.Tvar (_, j) -> IntSet.add j acc
  (* A higher-kinded variable is written applied, and is spelled all the same:
     as a template name, or -- a family -- as the plain type it is.  A plain
     head's arguments are not written at all ([E A] is [T1]), so where
     [plain] says so they spell nothing. *)
  | Miniml.Tapp (j, l) ->
    let acc = IntSet.add j acc in
    if plain j then acc else List.fold_left (spelled_tvars_of ~plain) acc l
  | Miniml.Tarr (a, b) ->
    spelled_tvars_of ~plain (spelled_tvars_of ~plain acc a) b
  (* An inductive's indices are not written ([Tglob] conversion keeps its
     parameters only): [getE T] is the enum [GetE]. *)
  | Miniml.Tglob (r, l, _) ->
    let l =
      match r with
      | GlobRef.IndRef (kn, _) -> (
        match Table.get_ind_num_param_vars_opt kn with
        | Some n -> safe_firstn n l
        | None -> l )
      | _ -> l
    in
    (* Nor are the arguments a mapping's text does not place: [itree E R] is
       [std::shared_ptr<ITree<R>>], and [E] cannot be read off it. *)
    let l = List.filteri (fun i _ -> Ml_type_util.type_arg_is_written r i) l in
    List.fold_left (spelled_tvars_of ~plain) acc l
  | Miniml.Tmeta {contents = Some t} -> spelled_tvars_of ~plain acc t
  | _ -> acc

(** The variables [ml_ty]'s declaration takes as template names.

    {!Ml_type_util.higher_kinded_ml_tvars} less those the declaration only
    ever applies, in its parameters and nowhere else: each such application is
    relaxed there to a fresh deduced parameter
    ({!Plan_templates.relax_applied_param}), and the variable left a plain
    [typename] -- [fused_trigger]'s [e : F T] is declared [_P0 e], and [F]
    [typename T1 = void].  So its arguments are no more spelled than a plain
    family's, and its position takes a box like any other. *)
let declared_higher_kinded_tvars ml_ty =
  let relaxed j =
    let bare = ref false and applied = ref false in
    let rec scan t =
      match resolve_tmeta t with
      | Miniml.Tvar (_, j') when j' = j -> bare := true
      | Miniml.Tapp (j', l) ->
        if j' = j then applied := true;
        List.iter scan l
      | Miniml.Tarr (a, b) -> scan a; scan b
      | Miniml.Tglob (_, l, _) -> List.iter scan l
      | _ -> ()
    in
    List.iter
      (fun d ->
        match expand_ml_fun_alias d with Miniml.Tarr _ -> () | d -> scan d )
      (ml_domains ml_ty);
    !applied && (not !bare)
    && not (IntSet.mem j (collect_tvars_set IntSet.empty (ml_return_type ml_ty)))
  in
  IntSet.filter (fun j -> not (relaxed j))
    (Ml_type_util.higher_kinded_ml_tvars [ml_ty])

(** The type variables of [id] a C++ compiler could read off the call's value
    arguments. *)
let deducible_tvars_of_glob id =
  match find_type_opt id with
  | None -> None
  | Some ml_ty_orig ->
    let hk = declared_higher_kinded_tvars ml_ty_orig in
    let plain j = not (IntSet.mem j hk) in
    Some
      (List.fold_left
         (fun acc d ->
           (* A definitional class is an alias for a function type -- [Id_ C
              obj] -- and an argument there is a callable just the same. *)
           match expand_ml_fun_alias d with
           | Miniml.Tarr _ -> acc
           | _ -> spelled_tvars_of ~plain acc d )
         IntSet.empty
         (List.map resolve_tmeta (ml_domains ml_ty_orig)) )

(** Infer the ML type of a body expression from its structure, or [None] where
    the structure does not say.

    This reads a type off a typed AST -- [MLcons] and [MLcase] carry theirs,
    and a global's is in the table -- rather than guessing one back out of an
    untyped C++ expression.  Its answer annotates a [CPPlambda]'s return type,
    so the frame a loopified call builds is typed instead of falling back on
    [decltype(lambda)].

    Instantiation goes through {!Mlutil.Var_types.apply}, by the callee's
    variables: a second substituter here would be a second oracle, free to
    disagree. *)
let rec infer_ml_body_type (a : ml_ast) : ml_type option =
  match a with
  | MLapp (MLglob ({callee = r; _} as use), args) ->
    ( match find_type_opt r with
    | Some ty ->
      (* Instantiate type schema variables with actual type arguments -- the
         ones the call site wrote, by variable, or, where it wrote none, the
         ones its arguments imply. *)
      let ty =
        if not (Mlutil.Var_types.is_empty (Mlutil.written_type_args use)) then
          Mlutil.instantiate_written ~reader:"infer_ml_body_type" use ty
        else
          Mlutil.Var_types.apply
            (tvar_instantiation r ty
               (List.filter (function MLdummy _ -> false | _ -> true) args) )
            ty
      in
      strip_tarr_n (count_real_ml_args args) ty
    | None -> None )
  | MLcons (ty, _, _, _) -> Some (resolve_tmeta ty)
  | MLcase (_, _, pv, _) when Array.length pv > 0 ->
    let (_, rty, _, _) = pv.(0) in
    Some (resolve_tmeta rty)
  | MLletin (_, _, _, body, _) -> infer_ml_body_type body
  | MLlam (_, ty, body) ->
    Option.map (fun rty -> Tarr (ty, rty)) (infer_ml_body_type body)
  | MLglob {callee = r; _} -> find_type_opt r
  | MLmagic (_, e, _) -> infer_ml_body_type e
  | _ -> None

(** [tvar_instantiation_found callee_ty args] is the callee's type-variable
    instantiation, read off the arguments' own ML types.

    A call site does not always carry its type arguments: where the use wrote
    none, the callee's schema stays uninstantiated at the written arguments,
    so a codomain like [projT2]'s reads as a bare [Tvar] and
    nothing downstream can tell whether it erases.  The arguments still pin
    the variables down -- matching the declared domain against the type each
    argument actually has recovers them.

    The result pairs each variable found with its type, the variable as
    [callee_ty] spells it, [i] for [Tvar (_, i)]; a variable no argument
    mentions is absent. *)
and tvar_instantiation_found
    ?lex
    ?(constructors = false)
    ?result
    callee_ty
    args =
  (* A binder's type is not on the [MLrel] that names it; it was written down
     where it was bound, which is what [lex], the environment [args] are typed
     in, keeps.  Without one a variable says nothing. *)
  let arg_ml_ty a =
    match infer_ml_body_type a with
    | Some _ as t -> t
    | None -> (
      match (a, lex) with
      | MLrel (i, _), Some lex -> Lexenv.type_opt lex i
      | _ -> None )
  in
  let found = Hashtbl.create 7 in
  (* The first binding stands, unless a later one is free of variables where
     it was not: a dictionary's own type binds a carrier at its instance's
     variables ([itree (E (sum _ _))]), and the handler argument that follows
     says [itree TopE]. *)
  let bind k t =
    let open_ t = not (IntSet.is_empty (collect_tvars_set IntSet.empty t)) in
    match Hashtbl.find_opt found k with
    | None -> Hashtbl.replace found k t
    | Some old when open_ old && not (open_ t) -> Hashtbl.replace found k t
    | Some _ -> ()
  in
  let rec unify formal actual =
    match (resolve_tmeta formal, resolve_tmeta actual) with
    | Miniml.Tvar (_, i), a -> bind i a
    (* A definitional class is the function type it abbreviates: [Case obj C]
       met by the eta-expanded dictionary lambda that fills it. *)
    | (Miniml.Tglob (GlobRef.ConstRef _, _, _) as f), (Miniml.Tarr _ as a)
      when (match expand_ml_fun_alias f with Miniml.Tarr _ -> true | _ -> false) ->
      unify (expand_ml_fun_alias f) a
    | Miniml.Tglob (g1, a1, _), Miniml.Tglob (g2, a2, _)
      when GlobRef.CanOrd.equal g1 g2 && List.length a1 = List.length a2 ->
      List.iter2 unify a1 a2
    (* An actual type spelled through an alias -- [MCFGtop T] for [itree
       MCFGEtop T] -- is what the alias stands for. *)
    | (Miniml.Tglob (g1, _, _) as f), Miniml.Tglob ((GlobRef.ConstRef kn as g2), a2, _)
      when (not (GlobRef.CanOrd.equal g1 g2))
           && Option.has_some (Table.lookup_typedef_unchecked kn) ->
      let body = Option.get (Table.lookup_typedef_unchecked kn) in
      unify f (if a2 = [] then body else Mlutil.type_subst_list a2 body)
    (* Where both sides open with type abstractions, they may abstract
       different numbers of them -- [E ~> M]'s one against a handler written
       [fun T => intr], itself abstracting its own [T] -- and the value
       arguments align only past all of them.  Only where both do: a formal
       value domain against an erased binder is a category's object, kept on
       one side and erased on the other. *)
    | Miniml.Tarr (Miniml.Tdummy _, c1), Miniml.Tarr (Miniml.Tdummy _, c2) ->
      let rec past_abstractions t =
        match resolve_tmeta t with
        | Miniml.Tarr (Miniml.Tdummy _, c) -> past_abstractions c
        | t -> t
      in
      unify (past_abstractions c1) (past_abstractions c2)
    | Miniml.Tarr (d1, c1), Miniml.Tarr (d2, c2) ->
      unify d1 d2 ;
      unify c1 c2
    (* A carrier applied to arguments -- [m A] -- is the shape a class method
       is written in, and its element is exactly the variable a call site
       cannot deduce.  The heads are variables themselves, so they pin nothing
       down against each other; the arguments do. *)
    | Miniml.Tapp (_, a1), Miniml.Tapp (_, a2)
      when List.length a1 = List.length a2 -> List.iter2 unify a1 a2
    (* An applied variable against a concrete application of the same arity: the
       variable stands for the head, which the actual type names, and the
       arguments are what both are applied to. This is the only place a [Type ->
       Type] argument can still be read off -- MiniML erases the argument
       itself, and what is left is the constraint that mentions it.

       Asked for, not assumed: where a class's carrier is what the variable
       stands for, the head alone is the wrong answer. A composed carrier [fun t
       => option (Exp t)] meets an [option (Exp any)] here and the head is
       [option], which is the arity deduction would have guessed and precisely
       what a composition is not. The dictionary routes recover those, and they
       must be left to reach them. *)
    | Miniml.Tapp (k, a1), Miniml.Tglob (g, a2, l)
      when constructors && List.length a1 = List.length a2 ->
      bind k (Miniml.Tglob (g, [], l));
      List.iter2 unify a1 a2
    (* A carrier is a head partially applied: [M T] against [itree TopE T]
       binds [M] to [itree TopE], the arguments the application writes ahead
       of the ones the variable is applied to.  Only where those are families
       -- a head, or one at its erased index: [modul nat (cfg nat)] is as
       much [fun T => modul T (cfg T)] at [nat] as [modul nat] at
       [cfg nat], and a prefix of plain types cannot say which. *)
    | Miniml.Tapp (k, a1), Miniml.Tglob (g, a2, l)
      when constructors && List.length a1 < List.length a2
           && List.for_all
                (fun t ->
                  match resolve_tmeta t with
                  | Miniml.Tglob (_, [], _) -> true
                  | Miniml.Tglob (_, args, _) ->
                    Ml_type_util.is_ml_erased_ty (List.nth args (List.length args - 1))
                  | _ -> false )
                (List.filteri (fun i _ -> i < List.length a2 - List.length a1) a2) ->
      let n_fixed = List.length a2 - List.length a1 in
      bind k (Miniml.Tglob (g, List.filteri (fun i _ -> i < n_fixed) a2, l));
      List.iter2 unify a1 (List.filteri (fun i _ -> i >= n_fixed) a2)
    (* A type alias meets an actual type already written as what it expands to:
       a class with a single field is inlined to that field, so a constraint
       spelled [Sub UBE E] meets an [UBE X -> UBE X]. Expanding puts both in the
       same form, and the alias's arguments are what its own parameters stand
       for. *)
    | Miniml.Tglob (GlobRef.ConstRef kn, cargs, _), actual when constructors ->
      ( match Table.lookup_typedef_unchecked kn with
      | Some body -> unify (Mlutil.type_subst_list cargs body) actual
      | None -> () )
    | _ -> ()
  in
  (* [args] holds the value arguments only, so a [Tdummy] formal -- an erased
     type or proof parameter -- consumes none of them.  What is left once they
     run out is the type of the application -- the codomain, or for a partial
     application the callable still to be applied -- and [result], where the
     position states one, says what it is. *)
  let rec walk ty args =
    match (resolve_tmeta ty, args) with
    | Miniml.Tarr (Miniml.Tdummy _, cod), _ -> walk cod args
    | Miniml.Tarr (dom, cod), a :: rest ->
      ( match arg_ml_ty a with
      | Some t -> unify dom t
      | None -> () ) ;
      walk cod rest
    | ty, [] -> Option.iter (unify ty) result
    | _ -> ()
  in
  walk callee_ty args ;
  Hashtbl.fold (fun i t acc -> (i, t) :: acc) found []

(** {!tvar_instantiation_found} at [r]'s variables, every one up to the last
    one found: a variable no argument mentions keeps itself, so substituting
    leaves it alone. *)
and tvar_instantiation r callee_ty args =
  match Mlutil.reference_scheme r with
  | None -> Mlutil.Var_types.empty
  | Some scheme ->
    let found = tvar_instantiation_found callee_ty args in
    let at v = List.assoc_opt (Scheme.Var.ordinal v) found in
    Mlutil.Var_types.through
      (Mlutil.last_var (List.filter (fun v -> Option.has_some (at v)) (Scheme.Var.all scheme)))
      (fun v ->
        match at v with
        | Some t -> t
        | None -> Miniml.Tvar (Miniml.Schematic, Scheme.Var.ordinal v) )

(** [resolve_from_argument_types tyargs args] resolves the variables after
    the last one the call wrote or resolved ({!Call_tyargs.beyond_extent})
    from what the call's value arguments [args] say they are, where C++ could
    not have deduced them.

    All or nothing: C++ takes a prefix of the parameter list, so a variable
    that cannot be named leaves every later one unnameable too, and naming
    some short of the undeducible one achieves nothing.  Variables the
    compiler can deduce are left to it -- naming a type twice is an
    opportunity to spell it differently, not a safeguard. *)
and resolve_from_argument_types ~lex tyargs args =
  let id = Call_tyargs.callee tyargs in
  match find_type_opt id with
  | None -> tyargs
  | Some callee_ty ->
    let n = IntSet.fold max (collect_tvars_set IntSet.empty callee_ty) 0 in
    let missing =
      List.filter (fun v -> Scheme.Var.ordinal v <= n) (Call_tyargs.beyond_extent tyargs)
    in
    let deducible = Option.default IntSet.empty (deducible_tvars_of_glob id) in
    if List.for_all (fun v -> IntSet.mem (Scheme.Var.ordinal v) deducible) missing then tyargs
    else
      let found = tvar_instantiation_found ~lex callee_ty args in
      Call_tyargs.resolve_all Call_tyargs.Argument_types
        (fun v -> List.assoc_opt (Scheme.Var.ordinal v) found)
        missing tyargs

(** [resolve_from_argument_heads tyargs args] resolves a hole before the last
    variable the call wrote ({!Call_tyargs.interior_holes}) from the head the
    variable meets in a value argument's type.

    MiniML erases a [Type -> Type] argument, but the callee still declares a
    template parameter for it -- and the erasure is contagious: template
    arguments are positional, so the all-or-nothing rule in
    {!Ml_type_util.filter_erased_type_args} drops the concrete arguments
    beside it.  One lost family therefore costs every type argument the call
    could have written, including the ones nothing can deduce.

    The family survives in the type of whatever argument is constrained in it
    -- [Sub UBE E] against a [Sub UBE UBE] -- which is what
    {!tvar_instantiation_found} reads.  [accept v t] may decline the answer
    [t] for [v]. *)
and resolve_from_argument_heads ?(only_alias_args = false) ?(accept = fun _ _ -> true) ~lex
    tyargs args =
  let id = Call_tyargs.callee tyargs in
  match (Call_tyargs.interior_holes tyargs, find_type_opt id) with
  | [], _ | _, None -> tyargs
  | holes, Some callee_ty ->
    (* Only a variable the callee applies: this pass exists because MiniML
       erases a [Type -> Type] argument, and a plain type argument that came
       out erased is erased for a reason a value argument cannot undo. *)
    let applied = Ml_type_util.applied_ml_tvar_arities [callee_ty] in
    (* Nor one a type alias in a domain is applied to: [ReSum_id : Id_ obj C
       -> ...] takes the category's morphism constructor [C], a type-level
       function erased for that reason alone, and the definitional class
       [Id_] -- an alias -- states it through the argument passed at it.
       A class, not any alias: [halist K V], a plain one, is applied to a
       value-indexed family whose argument's type is one instance of it.
       The erasure the rule above protects is a dependent inductive's
       ([sigT]), never an alias's. *)
    let in_dictionary =
      let rec alias_arg v = function
        | Miniml.Tglob ((GlobRef.ConstRef _ as g), l, _)
          when Typeclasses.is_class g ->
          List.exists
            (fun a ->
              (match resolve_tmeta a with
               | Miniml.Tvar (_, j) -> j = v
               | _ -> false)
              || alias_arg v a )
            l
        | Miniml.Tglob (_, l, _) -> List.exists (alias_arg v) l
        | Miniml.Tmeta {contents = Some t} -> alias_arg v t
        | _ -> false
      in
      fun v ->
        List.exists (alias_arg v)
          (List.map resolve_tmeta (ml_domains callee_ty))
    in
    let eligible =
      List.filter
        (fun v ->
          let k = Scheme.Var.ordinal v in
          ((not only_alias_args) && Hashtbl.mem applied k) || in_dictionary k )
        holes
    in
    let found =
      tvar_instantiation_found ~lex ~constructors:true callee_ty args
    in
    Call_tyargs.resolve Call_tyargs.Argument_heads
      (fun v ->
        match List.assoc_opt (Scheme.Var.ordinal v) found with
        | Some t when accept v t -> Some t
        | _ -> None )
      eligible tyargs

(** The instance of [t], the type of a let-bound function, that every use in
    its scope [body] is at, when the uses agree on one that pins each of the
    binding's own variables -- those above [n_outer] -- down to the enclosing
    declaration's.  Extraction generalises a let-bound function's type
    whatever the Rocq annotation says, and a binding used at one instance is
    polymorphic in name only: lifting it makes a template whose variables no
    call can deduce, and whose partial applications erase what they do not
    know.  [None] where the binder is used other than applied, or where the
    uses disagree.  [lex] is the enclosing scope's environment. *)
let sole_instance ~lex ~n_outer t body =
  let exception Not_sole in
  try
    let instances = ref [] in
    Mlutil.ast_iter_rel_applied
      (fun n i args ->
        if Int.equal i (n + 1) then begin
          if args = [] then raise Not_sole;
          let args =
            List.map
              (fun a ->
                if Mlutil.ast_occurs_itvl 1 (n + 1) a then raise Not_sole
                else Mlutil.ast_lift (-(n + 1)) a )
              args
          in
          instances := tvar_instantiation_found ~lex t args :: !instances
        end )
      body;
    let vars = IntSet.elements (collect_tvars_set IntSet.empty t) in
    let outer_only ty = IntSet.for_all (fun k -> k <= n_outer) (collect_tvars_set IntSet.empty ty) in
    let agreed k =
      match List.map (List.assoc_opt k) !instances with
      | Some ty :: rest when List.for_all (function Some ty' -> Mlutil.eq_ml_type ty ty' | None -> false) rest ->
        Some ty
      | _ -> None
    in
    let instance k =
      match agreed k with
      | Some ty when k > n_outer && outer_only ty -> ty
      | Some (Miniml.Tvar (_, k')) when Int.equal k k' -> Miniml.Tvar (Miniml.Schematic, k)
      | None when k <= n_outer -> Miniml.Tvar (Miniml.Schematic, k)
      | _ -> raise Not_sole
    in
    if !instances = [] then None
    else
      let n = List.fold_left max 0 vars in
      Some (List.init n (fun j -> if List.mem (j + 1) vars then instance (j + 1) else Miniml.Tvar (Miniml.Schematic, j + 1)))
  with Not_sole -> None

(** [a], a lambda bound by a let at type [t], with a binder for each value
    arrow of [t] it stops short of, its body applied to them: the lambda a
    {!Bound} let generates.  [convert_ml_type_to_cpp_type] uncurries the
    binding's type fully, so [unit -> State bool unit] is a function of two
    parameters, and [fun u => state_bind ...], whose body is a unary
    function rather than a lambda, would be a lambda of one, which no slot of
    that type holds.  The binders added are anonymous, so they are named as
    every anonymous parameter is ([_x0], [_x1], ...); a lambda abstracting
    every value arrow is itself. *)
let eta_bound_lambda t a =
  match a with
  | MLlam _ ->
    let binders, body = collect_lams a in
    let n_have = List.length (List.filter (fun (_, ty) -> not (erased_by_extraction ty)) binders) in
    (* The domains of the value arrows the lambda does not abstract, outermost
       first. *)
    let new_doms = List.filteri (fun i _ -> i >= n_have) (ml_value_domains t) in
    let d = List.length new_doms in
    if d = 0 then a
    else
      let new_binders = List.map (fun dom -> (Id anonymous_name, dom)) new_doms in
      (* The innermost new binder is [MLrel 1], the outermost [MLrel d]. *)
      let args = List.init d (fun i -> fresh_rel (d - i)) in
      let applied =
        match ast_lift d body with
        | MLapp (f, xs) -> MLapp (f, xs @ args)
        | lifted -> Core_normalize.apply lifted args
      in
      named_lams binders (named_lams (List.rev new_binders) applied)
  | _ -> a

(** How [let x : t := a in b], [a] a lambda, is generated under a head of
    [n_outer] type variables, [lex] being the enclosing scope's environment. *)
type let_lambda =
  | Bound  (** Polymorphic in nothing of its own: bound as a value. *)
  | At_instance of ml_type list
      (** Used at one instance only ({!sole_instance}): bound at it. *)
  | Inlined of ml_ast
      (** A polymorphic alias -- [let alias := @id], abstracting over erased
          type parameters alone -- used at several instances.  It has no C++
          value to bind, only a template no call could deduce, so each use
          calls what it abbreviates: this is [b] with a copy of [a] of its
          own ({!Fresh_occurrences.term}) put in place of each read of [x]
          and the applications reduced, [alias nat 9] becoming [id 9]. *)
  | Lifted  (** Lifted out to a function template of its own. *)

(** The decision {!let_lambda} names, made from the Core term alone: it is
    the one owner of it, applied once in Core
    ({!Core_elaborate.generated_definition}), after which translation meets
    only lambdas it binds or lifts. *)
let let_lambda ~lex ~n_outer t a b =
  if not (Ml_type_util.own_type_variables ~n_outer [t]) then Bound
  else
    match sole_instance ~lex ~n_outer t b with
    | Some inst -> At_instance inst
    | None ->
      let params, _ = collect_lams a in
      if List.exists (fun (_, ty) -> is_runtime_binder_type ty) params then Lifted
      else
        let rec beta_red_app args = function
          | MLlam (_, _, body) -> (
            match args with
            | [] -> MLlam (Dummy, Tdummy Ktype, beta_normalize body)
            | _ :: rest -> beta_red_app rest (ast_pop body) )
          | f ->
            let f = beta_normalize f in
            if args = [] then f else MLapp (f, List.map beta_normalize args)
        and beta_normalize = function
          | MLapp ((MLlam _ as f), args) -> beta_red_app args f
          | t -> ast_map beta_normalize t
        in
        Inlined (beta_normalize (ast_subst_each (fun () -> Fresh_occurrences.term a) b))

(** Check if a GlobRef returns a typeclass type (possibly through Tarr layers). *)
let ref_returns_typeclass r =
  match find_type_opt r with
  | Some ty -> Table.is_typeclass_type (ml_return_type ty)
  | None -> false

(** Check if a function returns a skipped type (e.g., ReSum instances whose
    Class is extracted as a ConstRef, not IndRef, and thus not recognized by
    [is_typeclass]). Such arguments are infrastructure that should be erased. *)
let ref_returns_skipped r =
  match find_type_opt r with Some ty -> ml_ret_is_skipped ty | None -> false

(** Whether a global denotes a typeclass instance. *)
let ref_is_instance r =
  match find_type_opt r with
  | Some ty -> ml_type_is_instance ty
  | None -> false

(** Strip [MLmagic] wrappers recursively — [MLmagic] is a transparent coercion
    in the ML AST and should be ignored by numeral-folding traversals. *)
let rec strip_magic = function MLmagic (_, e, _) -> strip_magic e | e -> e

(** A dictionary as an argument, without what only wraps it: coercions, and
    the lambdas over a singleton class method's erased type arguments that
    an instance passed as a value is eta-expanded with -- [fun _ _ => d],
    whose body never mentions them. *)
let rec strip_dictionary e =
  match strip_magic e with
  | MLlam (_, ty, b) when erased_by_extraction ty && not (Mlutil.ast_occurs 1 b) ->
    strip_dictionary (Mlutil.ast_pop b)
  | e -> e

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
    sources end at an ML type headed by the carrier, and are consumed as one.
    A binder is read in [lex], the environment the call stands in, and the
    constraints of [caller], the declaration it stands in. *)
let dict_carrier_ml_type ~lex ~caller id args =
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
    | Miniml.MLlam (_, _, b) | Miniml.MLmagic (_, b, _) | Miniml.MLapp (b, _) ->
      head_glob b
    | Miniml.MLglob {callee = r; _} -> Some r
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
    | Miniml.MLmagic (_, b, _) -> dict_ml_type ~depth b
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
    | Miniml.MLglob {callee = r; _} ->
      (* The instance's method returns [T1] applied: [TFunctor_box]'s codomain
         is [box B]. *)
      Option.map (fun t -> resolve_tmeta (ml_codomain t)) (find_type_opt r)
    | Miniml.MLrel (i, _) ->
      let i = i - depth in
      let constraint_arg t =
        match Option.map resolve_tmeta t with
        | Some (Miniml.Tglob (_, [_], _) as t) -> Some (strip_class t)
        | _ -> None
      in
      let recorded = constraint_arg (Lexenv.type_opt lex i) in
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
        let* r = caller in
        let* decl_ty = find_type_opt r in
        let doms = ml_domains decl_ty in
        let n = Lexenv.depth lex in
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
let with_dict_carrier ~lex ~caller id value_args ty =
  match dict_carrier_ml_type ~lex ~caller id value_args with
  | Some carrier -> subst_dict_carrier carrier ty
  | None -> ty

let instantiate_at_call ~lex ~caller id tys value_args ty =
  Mlutil.Var_types.apply tys (with_dict_carrier ~lex ~caller id value_args ty)

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
let binder_is_instance lex i =
  (* An instance parameter is not a value argument.  A declaration's
     class-typed parameter is its dictionary, as the binder records where it
     was bound ({!parameter_role}).  One that came from Coq
     at a class Crane skips -- [h : E -< F], whose class [ReSum] is skipped --
     is no parameter of the declaration's either, and is known by that class.
     Skipped is the whole test there: a binder at a class Crane {e kept} is
     an ordinary value wherever it is not a declaration's parameter, and
     reading it as an instance would take the argument away from the call.
     The declaration drops both kinds; without the second the call sites went
     on passing the one the declaration had dropped. *)
  match Lexenv.binder lex i with
  | Some {eb_role = Dictionary; _} -> true
  | Some {eb_type; eb_role = Value; _} -> ml_ret_is_skipped eb_type
  | None -> false

(* Check if an ML arg is a type class instance (a reference to a struct that
   implements a type class).

   [MLmagic] is a transparent coercion -- extraction inserts one around an
   instance whose class is applied to a type CONSTRUCTOR (e.g. [Mon Opt] with
   [Opt : Type -> Type]).  Look through it, or the instance is left in value
   position and the generated call names the instance struct as if it were a
   value. *)
let is_typeclass_instance_arg ~lex ml_arg =
  match strip_dictionary ml_arg with
  | MLglob {callee = r; _} ->
    (* An instance parameterised over types alone carries its parameters in
       the [MLglob]'s type arguments, so its ML type is still an arrow --
       [MList : forall A, Monoid (list A)].  Read the codomain, as the
       application case below does, or such an instance is left in value
       position and the call names the instance struct as if it were one. *)
    ref_is_instance r
  | MLrel (i, _) -> binder_is_instance lex i
  | MLapp (MLglob {callee = r; _}, _) ->
    (* Parameterized instance application, e.g. numList A H. Check if r's
       return type (after stripping Tarr) is a typeclass type, or if it
       returns a skipped type (e.g. ReSum instances where the Class is a
       ConstRef not recognized by is_typeclass). *)
    ref_is_instance r
  | MLcase (case_ty, _scrutinee, branches, _) when Array.length branches = 1 ->
    (* Single-branch case = record field projection.  If the projected
       field's type is itself a typeclass, this is a typeclass instance
       arg — e.g., [base_category(PS)] projects a [PreCategory]-typed
       field from a [PreStableCategory] record.
       Look up the record's field types from the case type rather than
       relying on branch binding types (which may be Tunresolved). *)
    let (binds, _, _, br_body) = branches.(0) in
    ( match br_body with
    | MLrel (j, _) when j >= 1 && j <= List.length binds ->
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

let instance_arg_is_erased ~lex ml_arg =
  (* An instance argument is not a value argument, but only one whose class
     Crane kept is a template argument either: {!collect_typeclass_param_ids}
     mints a concept-constrained parameter per kept class and none for a
     skipped one, so an [E -< F] has no parameter of any kind to be passed at.
     Passing it anyway put the instance in the callee's template argument
     list, where it names no type. *)
  match strip_magic ml_arg with
  | MLglob {callee = r; _} | MLapp (MLglob {callee = r; _}, _) ->
    (* Either the instance's class is infrastructure Crane skips -- [E -< F],
       whose [ReSum] is a [ConstRef] mapped to the empty string -- or the
       instance itself is, as [Monad_itree] is in both ITree modes.  Skipping
       the instance is how a mode says its carrier's operations are named by
       their mappings and not by a dictionary. *)
    ref_returns_skipped r || ref_is_skipped r
  | MLrel (i, _) -> (
    match Lexenv.type_opt lex i with
    | Some ty -> ml_ret_is_skipped ty
    | None -> false )
  | _ -> false

(* The class an instance argument is an instance of, as an ML type, a
   variable's read off its binder in [lex]. *)
let instance_class_ty ~lex ml_arg =
  let of_ref r =
    match Table.find_type r with
    | ty -> ml_return_type ty
    | exception Not_found -> Miniml.Tunknown
  in
  match strip_dictionary ml_arg with
  | MLglob {callee = r; _} | MLapp (MLglob {callee = r; _}, _) -> of_ref r
  | MLrel (i, _) -> (
    match Lexenv.type_opt lex i with
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
let kept_instance_of_projection ~lex x args =
  List.find_opt
    (fun a ->
      is_typeclass_instance_arg ~lex a
      && (not (instance_arg_is_erased ~lex a))
      && List.mem (Some x)
           (record_fields_of_type (instance_class_ty ~lex a)) )
    args

(* The value parameters of class field [use] called through [inst] in
   [lex], as the method declares them.

   Two substitutions, because the projection's type quantifies over the
   class's carrier as well as the method's own variables and the use's
   type arguments carry only the latter -- its leading entry, the
   carrier's, is [Tdummy].  The carrier is what the instance is an instance
   {e at}, the sole argument of its class type; without it every [m A]
   absorbs its argument and says [std::any].  The carrier, the dictionary
   and the erased type arguments all stand in front of the value
   parameters. *)
let projection_value_domains ~lex use inst =
  match Table.find_type use.callee with
  | exception Not_found -> []
  | ty ->
    let ty =
      match resolve_tmeta (instance_class_ty ~lex inst) with
      | Tglob (_, [carrier], _) -> subst_dict_carrier carrier ty
      | _ -> ty
    in
    ml_domains
      (Mlutil.instantiate_written ~reader:"projection_value_domains" use ty)
    |> List.filter (fun t ->
           match resolve_tmeta t with
           | Tdummy _ -> false
           | t -> not (Table.is_typeclass_type t))

(** [static_projection ~lex use args] -- where the call [use args], standing
    in [lex], calls a class field as a static member of the instance it
    projects through, rather than through the field's dispatcher: which
    argument that instance is, the member's value parameters, and the
    operands the call leaves out.  A mapped field is projected so wherever
    its instance was kept ({!kept_instance_of_projection}), and a singleton
    class's method wherever its instance was -- its dictionary is known
    wherever the call is, its projection's only one, and the instance struct
    declaring the method under the dispatcher's own name hides the
    dispatcher from any call inside it.  A mapped field's call leaves
    nothing out; a singleton method's static member takes every operand, so
    a partial application closes over the rest. *)
let static_projection ~lex use args : Elaborated_call.static_projection option =
  let x = use.callee in
  let inst =
    if Table.is_inline_custom x then kept_instance_of_projection ~lex x args
    else if Table.singleton_method_class x <> None then
      List.find_opt (fun a -> is_typeclass_instance_arg ~lex a && not (instance_arg_is_erased ~lex a)) args
    else None
  in
  Option.map
    (fun inst ->
      let domains = projection_value_domains ~lex use inst in
      let missing =
        if Table.is_inline_custom x then []
        else
          let operands = List.filter (fun a -> not (Mlutil.isMLdummy a || a == inst)) args in
          List.filteri (fun i _ -> i >= List.length operands) domains
      in
      let rec position i = function
        | a :: rest -> if a == inst then i else position (i + 1) rest
        | [] -> assert false
      in
      {Elaborated_call.instance = position 0 args; domains; missing} )
    inst
