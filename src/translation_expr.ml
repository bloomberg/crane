(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Expressions: {!gen_expr} lowers a Core expression to a CppIR expression,
    dispatching on its form.  A variable read, a global used as a value, a
    literal and a coercion's crossing ({!gen_crossing}) are lowered here; a
    lambda, an application, a constructor, a match, an effect and a let or
    local fixpoint (as an immediately invoked lambda over statements) go to
    their modules, which recurse back through {!Translation_knot}. *)

open Common
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Core_query
open Translation_support
open Translation_types
open Translation_calls
open Translation_application
open Translation_construct
open Translation_match
open Translation_stmts

(** The type variable the definition whose body is being generated returns
    boxed, its arguments carrying it only as a type index
    ({!Ml_type_util.index_only_result_tvar}): [Some 1] in [eval : expr A ->
    A]. *)
let own_index_only_result () =
  Option.bind (Option.bind (!tctx).input.body_owner find_type_opt) Ml_type_util.index_only_result_tvar

(** Under [CRANE_CHECK_IR], that the variable at de Bruijn index [i] is one
    binder to both of the scopes translation keeps: [env], which names it, and
    the binder environment ({!current_lexenv}), which types it.  The two are
    pushed side by side at every binding, and nothing but the position ties an
    entry of one to an entry of the other, so a binder pushed to one alone, or
    in another order, retypes every variable beneath it.  The renamed C++
    identifier is what both record.  An instance's dictionary is the one
    binder named and not typed: inside its methods it is a template parameter
    of the enclosing struct. *)
let check_binder_scopes env i =
  if Probe.checking () then
    match (get_db_name_opt i env, get_env_binder_opt i) with
    | Some x, Some b when Id.equal x b.eb_id -> ()
    | Some x, None when Common.is_tc_instance_id x -> ()
    | x, b ->
      let name = Option.cata Id.print (Pp.str "nothing") in
      Probe.violation "binder scopes"
        Pp.(
          str "the variable at index " ++ int i ++ str " is " ++ name x ++ str " to the names in scope and "
          ++ name (Option.map (fun b -> b.eb_id) b)
          ++ str " to the binders typed in scope")

(** Generate C++ expression from ML AST. Main expression compiler - handles
    lambdas, applications, constructors, pattern matching, etc. Monadic
    non-function globals are wrapped in CPPfun_call by the Core.Expr.Global case below.

    A [Boxed] slot says that [ml_e] flows into a slot that is really
    [std::any], so any constructor it builds has to use the canonical erased
    shape: every producer of the same Coq type must agree with the fixed
    [any_cast] that reads it back.  A "cons" production keeping
    [deque<Prod<Nat, Nat>>] where the matching "nil" erased to
    [deque<Prod<any, any>>] is what [std::bad_any_cast] at the consumer looks
    like.

    Only constructors read it, but the slot is a property of the whole
    subterm, so it is carried down every position whose value ends up in that
    slot -- an argument, a coercion's operand, a branch result, a tail
    expression, the body of a lambda that is itself the stored value.  A
    position that opens a new slot (a let-bound right-hand side, a
    non-tail statement) does not take it. *)
let rec gen_expr ?(expected_ty : Cpp_ir.Lowered.Type.t option) ?(slot = empty_slot) env
    (ml_e : Core.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match ml_e with
  | Core.Expr.Bound_variable {index = i; occurrence = occ} ->
    check_binder_scopes env i;
    let boxed_read = read_is_boxed i occ in
    let x = try get_db_name i env with Failure _ -> db_fallback_id i in
    let var_expr : Cpp_ir.Lowered.Expr.t = Local x in
    (* Move on a last use of a variable the region owns, as its plan says
       ({!Ownership_ir.use}); a boxed variable is unboxed whole, whatever
       component of it Core reads.  Never move a typeclass instance -- it is a type reference in the concept
       paradigm, not an owned value, and wrapping it produces invalid C++ like
       [std::move(_tcI0)::method()].  Recognised by identity rather than by ML
       type: this binder is synthesised by {!Common.tc_instance_id}, and inside
       a generated instance method it is a template parameter of the enclosing
       struct, with no entry of its own in [env_types]. *)
    let move_candidate =
      (not (Common.is_tc_instance_id x))
      &&
      match Ownership_ir.use ~boxed:boxed_read (!tctx).lexical.move_plan occ with
      | Some ((Share | Clone | Copy) as copy) ->
        (* The copy the plan names is the one the variable's declaration
           makes, where Core says what its type is. *)
        ( if Probe.checking () && Ownership_ir.read_is_typed (!tctx).lexical.move_plan occ then
            match binder_cpp_type i with
            (* [auto] says nothing of the type it deduces. *)
            | Some Cpp_ir.Type.(Auto | Const Auto | Reference (_, (Auto | Const Auto))) -> ()
            | Some declared when Ownership_ir.copy_of_declared declared <> copy ->
              let name : Ownership_ir.Use.t -> string = function
                | Share -> "shares" | Clone -> "clones" | Copy -> "copies" | Move -> "moves" | Borrow -> "borrows"
              in
              Probe.violation "copy mode"
                Pp.(
                  str "the plan " ++ str (name copy) ++ str " " ++ Id.print x ++ str " where its declaration "
                  ++ str (name (Ownership_ir.copy_of_declared declared)) ++ str " it" )
            | Some _ | None -> () );
        false
      | Some use -> use = Move
      | None ->
        Probe.violation "unplanned read"
          Pp.(str "the read of " ++ Id.print x ++ str " is in no plan of the region it is lowered in");
        false
    in
    let result : Cpp_ir.Lowered.Expr.t = if move_candidate then Move var_expr else var_expr in
    if boxed_read then begin
      match expected_ty with
      | Some (Variable (Index (n, _))) when own_index_only_result () = Some n ->
        (* The definition returns this variable boxed, and nothing else spells
           it: its template parameter is the caller's instantiation -- in a
           machine the outermost call's -- not the type of a value read at
           the variable at some other depth. *)
        result
      | Some ty when not (Cpp_ir.Types.prints_as_any ty) && ty <> Void ->
        if resolves_to_any_type ty then result
        else
          (* For a CUSTOM-LIST container target, the erased var is boxed at
             runtime as [deque<...erased...>] (each element fully erased).  A
             direct [any_cast] to the concrete-element container
             ([deque<pair<string,Val>>]) would implicitly re-box the already-
             unwrapped erased container into a fresh [std::any] and then throw
             at runtime, since that any holds a [deque<pair<any,any>>].  Unwrap
             to the ERASED container instead; a downstream consumer that needs
             the concrete-element container (a constructor field via
             [crane_container_cast], or [eta_fun]'s function-argument path)
             converts it.  Scalar targets keep the direct concrete [any_cast]. *)
          (* Does [ty] denote a list container, possibly under a [Tnamespace]
             wrapper?  (A namespaced list — e.g. a functor-qualified
             [Datatypes::List] — must be recognized too, otherwise the fallback
             below emits the target verbatim and leaks an abstract/unresolved
             element type variable, e.g. [any_cast<List<T1>>], inside an erased
             [crane_erase_fn] body which is not a template context.) *)
          let rec ty_is_list : Cpp_ir.Lowered.Type.t -> bool = function
            | In_namespace (_, t) -> ty_is_list t
            | Entity_application (g, _ :: _, _) -> is_list_global g
            | _ -> false
          in
          let unbox_at t = Cpp_erasure.unbox t result in
          if ty_is_list ty then
             (* Canonical erased shape is [deque<std::any>] -- every element
                boxed as a single [std::any] (see [gen_expr_custom_cons]'s
                hollow-container collapse for the producer side of this same
                invariant).  Erasing to [deque<pair<any,any>>] instead (i.e.
                preserving the element's own container structure) would
                disagree with that canonical shape: [crane_container_cast]
                (the consumer this cast feeds) expects a plain [std::any] per
                element so it can unbox each one with [crane_any_cast]
                directly; handing it a [pair<any,any>] element instead makes
                it implicitly re-box that pair into a fresh [std::any] before
                [crane_any_cast] can recover it, which is redundant with (and,
                if the destination shape or printer state ever disagrees,
                incompatible with) the direct-[std::any]-per-element path. *)
             let rec erase_list_elems : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
               | In_namespace (ns_g, t) -> In_namespace (ns_g, erase_list_elems t)
               | Entity_application (g, args, ns) ->
                 Entity_application (g, List.map (fun _ -> Cpp_ir.Type.Any) args, ns)
               | t -> t
             in
             unbox_at (erase_list_elems ty)
           else unbox_at ty
      | _ -> result
    end
    else
      (* A local function that takes more arguments than the slot hands it at
         once -- a [let fix] or a parameter of type [nat -> nat -> nat] where
         a [nat -> (nat -> nat)] is expected -- is curried to the slot, as a
         global named as a value is. *)
      let unfolded = Option.map (fun t -> unfold_cpp_typedef env (strip_cpp_ref_const t)) in
      let expected = unfolded expected_ty in
      let curries t =
        match (expected, unfolded t) with
        | Some (Function ((_ :: _ as exp_dom), _)), Some (Function (dom, _)) -> List.length dom > List.length exp_dom
        | _ -> false
      in
      ( match
        ( expected,
          unfolded
            (planned_binder_type_or_derive ~use:"curried read" ~agree:(fun p l -> curries p = curries l) env i occ) )
      with
      | Some (Function ((_ :: _ as exp_dom), _)), Some (Function (dom, _))
        when List.length dom > List.length exp_dom -> (
        (* The closure reads the function where it is made, and takes it
           there where this read moves it. *)
        match (curry_value_to_expected env ?expected_ty (get_env_type_opt i) var_expr, var_expr) with
        | Lambda l, Local x when move_candidate -> Lambda {l with moved = [x]}
        | e, _ -> e )
      | _ -> result )
  (* A singleton class's dictionary applied, which is the body of the class's
     projection: the method, called on the instance -- a template parameter,
     so a static member -- at the method's own type variables, which here are
     the projection's, numbered past the class's parameters. *)
  | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; occurrence = occ};
                     arguments = args} when singleton_call env i occ <> None ->
    Translation_application.gen_singleton_dictionary_call env ~i ~occ ~args
  (* Every application translation is handed is canonical
     ({!Core_normalize}): no head here is a global already applied, a
     coercion, or a one-branch match, and no numeral literal is spelled
     as a converter's application or as a constructor term. *)
  | (Core.Expr.Apply _ | Core.Expr.Construct _) as e when Probe.checking () && not (Core_normalize.canonical_application e) ->
    Probe.violation "non-canonical application" (Pp.str "a term Core_normalize writes otherwise");
    gen_expr ?expected_ty ~slot env (Core_normalize.spine e)
  | Core.Expr.Apply {callee = Core.Expr.Global ({callee = r; _} as use);
                     arguments = a1 :: l} when is_effect Core_effects.Return use ->
    Translation_effects.gen_return_expr env ~r ~use ~a1 ~l
  (* | Core.Expr.Apply (Core.Expr.Global {callee = h; _}, a1 :: a2 :: l) when is_hoist h -> gen_expr env
     (Core.Expr.Apply (a1, a2::[])) *)
  | Core.Expr.Apply {callee = Core.Expr.Global use;
                     arguments = _ :: _ :: _} as a when is_sequential_effect Core_effects.Bind use ->
    Translation_effects.gen_bind_expr env a
  | Core.Expr.Apply {callee = (Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _); _} as a ->
    (* Nested fix application in expression context (e.g., S((fix aux ...) es)).
       Wrap in an IIFE, delegating to gen_stmts which handles Core.Expr.Apply(Core.Expr.Fixpoint
       ...). *)
    with_escape_analysis (fun () -> with_region a (fun () ->
      Cpp_ir.Build.iife None (gen_stmts env (fun x : Cpp_ir.Lowered.Stmt.t -> Return (Some x)) a) ) )
  (* A class field is projected through the instance wherever the instance
     survived, whatever mapping the field carries, as Core decided it
     ({!Core_elaborate.static_projection_call}). *)
  | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args}
    when Core_elaborate.static_projection_call ~lex:(current_lexenv ()) use args <> None ->
    Translation_application.gen_instance_projection ~expected_ty ~slot env ~use ~args
  (* A closed call building a typeclass instance -- an event injection
     [ReSum_inr] composed from instances and closed lambdas, say -- is the
     same value every time it is evaluated, and evaluating it composes fresh
     closures.  It is built once and kept, as a closed constructor term is
     (see {!Cpp_constants}).  An instance is a pure value, so building it
     once cannot drop an effect; only where it comes out as a call.  Core
     decides which calls those are ({!Core_elaborate.closed_instance_call}). *)
  | Core.Expr.Apply {callee = Core.Expr.Global ({callee = f; _} as use); arguments = args} as e
    when (not slot.building_constant)
         && Core_elaborate.closed_instance_call ~lex:(current_lexenv ()) use args -> (
    let built = gen_expr ?expected_ty ~slot:{slot with building_constant = true} env e in
    match built with
    | Call _ ->
      Cpp_ir.Build.call (Runtime (Crane_rt.Constant (String.lowercase_ascii (Label.to_string (Common.label_of_r f))))) [built]
    | _ -> built )
  | Core.Expr.Apply {callee = f; arguments = args} ->
    Translation_application.gen_application ~expected_ty ~slot env f args
  | Core.Expr.Lambda _ as a ->
    Translation_lambda.gen_lambda ~expected_ty ~slot env a
  | Core.Expr.Global ({callee = x; _} as use) when is_inline_custom x ->
    let tys = Mlutil.written_type_args use in
    let ml_ty = callee_ml_type_exn x in
    let ty = cpp_of_ml env ml_ty in
    ( match ty with
    | Function (dom, cod) ->
      eta_fun ?expected_ty env (Core.Expr.Global use) []
    | _ ->
      mk_cppglob
        ?yields:
          (glob_yields env x (Mlutil.instantiate_written ~reader:"glob_yields" use))
        x
        (template_params_of_ml ~site:Through_tvar env
           (List.map snd (Mlutil.Var_types.bindings tys)) ) )
  | Core.Expr.Global ({callee = x; _} as use) ->
    let tys = Mlutil.written_type_args use in
    let tvars = get_current_type_vars () in
    (* Each argument with the variable it was written for. *)
    let by_var =
      List.map
        (fun (v, ty) ->
          let t = cpp_of_ml env (type_simpl ty) in
          ( Scheme.Var.ordinal v,
            match t with
            | Variable (Index (_, None)) when tvars <> [] -> Cpp_ir.Type.Erased Type
            | _ -> t ) )
        (Mlutil.Var_types.bindings tys)
    in
    (* An erased variable bound by a result: the [i]th of [names] stands for
       variable [i]. *)
    let fill_from (names, m) by_var =
      List.map
        (fun (i, t) ->
          ( i,
            if not (Cpp_ir.Types.prints_as_any t) then t
            else
              match List.nth_opt names (i - 1) with
              | Some v -> (
                match List.find_opt (fun (v', _) -> Id.equal v v') m with
                | Some (_, b) when names_only_scoped_tvars b -> b
                | _ -> t )
              | None -> t ) )
        by_var
    in
    (* A global passed as a function value -- [MonadIter_itree] at a slot
       [MonadIter m] -- has its erased type arguments stated by the callable
       the slot takes. *)
    let by_var =
      match (List.exists (fun (_, t) -> Cpp_ir.Types.prints_as_any t) by_var, slot.call_result) with
      | true, (Some _ as res) -> (
        match instance_family_binding env x tys res with
        | Some (_, names, m) -> fill_from (names, m) by_var
        | None -> by_var )
      | _ -> by_var
    in
    let result_bindings () = callee_result_bindings env x ~explicit:true expected_ty in
    let by_var =
      match expected_ty with
      | Some _ when by_var = [] -> (
        (* None written at all: every variable, if the callable binds each. *)
        match result_bindings () with
        | (_ :: _ as names), (_ :: _ as m) -> (
          let bound =
            List.mapi
              (fun k v ->
                match List.find_opt (fun (v', _) -> Id.equal v v') m with
                | Some (_, b) when names_only_scoped_tvars b -> Some (k + 1, b)
                | _ -> None )
              names
          in
          if List.for_all Option.has_some bound then List.map Option.get bound
          else by_var )
        | _ -> by_var )
      | Some _ when List.exists (fun (_, t) -> Cpp_ir.Types.prints_as_any t) by_var -> (
        match result_bindings () with
        | names, (_ :: _ as m) -> fill_from (names, m) by_var
        | _ -> by_var )
      | _ -> by_var
    in
    let tys_cpp = List.map snd by_var in
    let yields =
      glob_yields env x (Mlutil.instantiate_written ~reader:"glob_yields" use)
    in
    let cglob =
      mk_cppglob ?yields x (written_at_variables x (filter_erased_keyed by_var))
    in
    if naming_calls ~cpp_of:(cpp_of_ml env) x then
      (* A function of no parameters named is called, a call made of this
         use. *)
      made_of (Core.Global_use.occurrence use) (Cpp_ir.Build.call cglob [])
    else
      ( match
          Option.map
            (fun ty ->
              materialise_opaque (cpp_of_ml env (expand_ml_fun_alias ty)))
            (callee_ml_type x)
        with
      (* A declaration whose result erased -- because its Rocq type hides
         the quantifier behind a type alias, or because a type index alone
         pins the result down -- hands back a box whatever the use site's
         instantiation says, so a use site naming concrete types reaches it
         through the adapter {!coerce} builds.  The type the use site wants
         is the slot's when there is one; failing that, a single type
         argument tells what the one quantifier every erased position came
         from was instantiated at. *)
      | Some from
        when (match from with Function (_, cod) -> Cpp_ir.Types.prints_as_any cod | _ -> false)
        ->
        let into =
          match (expected_ty, tys_cpp) with
          | Some into, _ when names_only_scoped_tvars into -> Some into
          | _, [t] when not (Cpp_ir.Types.prints_as_any t) ->
            let rec instantiate : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
              | Any -> t
              | Function (dom, cod) ->
                Function (List.map instantiate dom, instantiate cod)
              | ty -> ty
            in
            Some (instantiate from)
          | _, _ -> None
        in
        (* A signature that erased entirely is not a template and takes no
           explicit type arguments; one that kept some is still called with
           the ones the use site supplied. *)
        let cglob =
          if is_fully_erased_fun_ty from then mk_cppglob x [] else cglob
        in
        (* Converted as a value, so named as one.  A callable parameter that
           kept a type of its own is generalised to [F &&] -- a fully erased
           one is not ({!Gen_functions.gen_dfun}) -- and a template is no
           value a conversion can take whole: an adapter at the declared
           signature, at this use's type arguments, is. *)
        let cglob =
          match from with
          | Function (dom, _)
            when List.exists
                   (fun (f : Cpp_ir.Lowered.Type.t) ->
                     match f with Function _ -> not (is_fully_erased_fun_ty f) | _ -> false )
                   dom ->
            curry_value_to_expected env ~exact:true
              (Option.map expand_ml_fun_alias (instantiated_type use)) cglob
          | _ -> cglob
        in
        ( match into with
        | Some into -> coerce ~from ~into cglob
        | None -> cglob )
      | _ -> curry_to_expected env ?expected_ty use cglob )
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _} when is_custom r ->
    gen_expr_custom_cons ?expected_ty ~slot env ty r ts
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _}
    when ts = []
         &&
         match r with
         | GlobRef.ConstructRef ((kn, _), _) ->
           is_enum_inductive (GlobRef.IndRef (kn, 0))
         | _ -> false ->
    let ind_ref, ctor_name =
      match r with
      | GlobRef.ConstructRef ((kn, i), cidx) ->
        ( GlobRef.IndRef (kn, i),
          Id.of_string (Common.enum_ctor_name_of_ref kn i cidx) )
      | _ ->
        CErrors.anomaly
          (Pp.str "gen_expr: enum constructor expected ConstructRef")
    in
    Enum_value (ind_ref, ctor_name)
  (* A closed constructor term of a shared variant -- a numeral built from
     [xI]/[xO]/[xH], say -- is built once and kept, as ocamlopt keeps a
     structured constant: evaluated again, it is a count bump rather than an
     allocation per node.  The outermost closed term is the constant; the
     runtime makes every block it holds immortal too.  Only where the term
     comes out as its factory call: a conversion into another slot type is
     left as it is.  Core decides which terms those are
     ({!Core_elaborate.shared_constant}). *)
  | Core.Expr.Construct {arguments = ts; _} as e
    when (not slot.building_constant) && Core_elaborate.shared_constant e
         && not (takes_reuse_token e) -> (
    let built = gen_expr ?expected_ty ~slot:{slot with building_constant = true} env e in
    match built with
    | Call (_, Type_member (Entity_application (n, _, _), _), _)
      when Table.is_shared_variant n && ts <> [] ->
      Cpp_ir.Build.call (Runtime (Crane_rt.Constant (constant_name e))) [built]
    | _ -> built )
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _} as construction ->
    Translation_construct.gen_construction ~expected_ty ~slot env ~ty ~r ~ts construction
  | Core.Expr.Match {scrutinee_type = typ;
                     scrutinee = t;
                     branches = pv;
                     occurrence = case_occ} when Core_elaborate.match_kind typ pv case_occ = Match_kind.Custom ->
    Translation_match.gen_custom_match_expr env ~typ ~t ~pv ~case_occ
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = t; branches = pv; occurrence = case_occ}
    when Match_kind.is_record (Core_elaborate.match_kind typ pv case_occ) ->
    Translation_match.gen_record_projection ~expected_ty ~slot env ml_e ~typ ~t ~pv ~case_occ
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = t; branches = pv; occurrence = case_occ} when lang () == Cpp ->
    gen_cpp_case typ t env pv case_occ
  | Core.Expr.Let {binder_type = ty; _} as a ->
    with_escape_analysis (fun () -> with_region a (fun () ->
      with_iife_return_type expected_ty (fun () ->
        Cpp_ir.Build.iife None (gen_stmts env (fun x : Cpp_ir.Lowered.Stmt.t -> Return (Some x)) a) ) ) )
  | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ as a ->
    (* Bare fixpoint in expression context — wrap in IIFE, delegate to
       gen_stmts. *)
    with_escape_analysis (fun () -> with_region a (fun () ->
      Cpp_ir.Build.iife None (gen_stmts env (fun x : Cpp_ir.Lowered.Stmt.t -> Return (Some x)) a) ) )
  | Core.Expr.String s -> Literal (String s)
  | Core.Expr.UInt63 x -> Literal (Uint63 x)
  | Core.Expr.Numeral {inductive = ind; value = n} -> (
    match Table.get_numeral_info ind with
    | Some info -> render_numeral info n
    | None -> CErrors.anomaly Pp.(str "a literal of " ++ Printer.pr_global ind ++ str ", which has no numeral mapping") )
  | Core.Expr.Float64 f -> Literal (Float f)
  | Core.Expr.Persistent_array {elements = elems; default = def} ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    Persistent_array (elems, def)
  | Core.Expr.Coerce {source_type = from; target_type = into; value = t; occurrence = occ} ->
    gen_crossing ?expected_ty ~slot env ~coercion:(Some (from, into)) ~boxed:false t occ
  | Core.Expr.Boxed_value {value = t; occurrence = occ} ->
    gen_crossing ?expected_ty ~slot env ~coercion:None ~boxed:true t occ
  | Core.Expr.Lambda_group_barrier {value = t; occurrence = occ} ->
    gen_crossing ?expected_ty ~slot env ~coercion:None ~boxed:false t occ
  | Core.Expr.Erased_value _ ->
    (* An erased proof or type reaching an expression position: a dead one,
       an absurd branch.  Where it is a value a constructor stores it is the
       empty box instead, see {!gen_stored_value}. *)
    Abort ("unreachable", abort_ty expected_ty)
  | Core.Expr.Runtime_error msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    Abort (msg, abort_ty expected_ty)
  | Core.Expr.Axiom_value s -> Abort ("unrealized axiom: " ^ s, abort_ty expected_ty)
  | _ -> CErrors.anomaly (Pp.str "gen_expr: unhandled ML AST node")

(** A term crossing a type gap erasure opened: an [Core.Expr.Coerce] with its
    [coercion] types, an [Core.Expr.Boxed_value] ([boxed]), or an [Core.Expr.Lambda_group_barrier] (neither). *)
and gen_crossing ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~slot env ~coercion ~boxed t occ :
    Cpp_ir.Lowered.Expr.t =
  let expected_ty = planned_position occ ~live:expected_ty in
  (* A value crossing into a slot that is really [std::any] has to be built
     at the canonical erased shape -- every component boxed -- because the
     consumer recovers it with a fixed [any_cast] and cannot know the
     concrete component types.  Extraction recorded both sides of this
     boundary, so ask for that shape whenever [into] is the erased one and
     [from] is not.  See {!Ml_type_util.slot_repr}. *)
  let into_box_kind =
    match coercion with
    | Some (from, into)
      when
      (* The destination this value is actually being built into outranks
         the coercion's inferred target: a call site that names a concrete
         parameter type -- an instance's associated type, say -- has pinned
         the slot down, while the recorded [into] is a type variable this
         scope cannot resolve and so reads as erased. *)
      (match expected_ty with
          | Some t -> Cpp_ir.Types.prints_as_any t
          | None -> true)
      && Cpp_ir.Types.prints_as_any (cpp_of_ml env into)
      && not (Cpp_ir.Types.prints_as_any (cpp_of_ml env from)) ->
      Some (box_kind_of_cpp_type (cpp_of_ml env into))
    | Some _ | None -> None
  in
  (* A lambda is written against the slot it fills -- its binders and
     arity are the slot's -- and a coercion cannot reshape a callable after
     the fact. *)
  let inner =
    gen_expr
      ?expected_ty:(match t with Core.Expr.Lambda _ -> expected_ty | _ -> None)
      ~slot:
        (match into_box_kind with Some kind -> into_box kind slot | None -> slot)
      env t
  in
  (* What extraction recorded about the term's own side of the boundary.
     Not materialised: this is an inferred type, so a [Topaque] here stays
     [Topaque] and licenses nothing. *)
  let recorded_from =
    match coercion with
    (* A binder whose C++ type is decided outranks the coercion's recorded
       source, for the reason given for [Core.Expr.Boxed_value] below: [md] destructured out
       of a typed pattern is a [List<metadata<std::any>>], whatever erased
       carrier application the coercion recorded for it. *)
    | Some (from, _) -> (
      match t with
      | Core.Expr.Bound_variable {index = i; occurrence = occ} -> (
        (* Read below only for whether it is a box, so the plan and
           lowering need agree on no more than whether the binder is
           decided at a type that is not one. *)
        let decided = function Some ty -> not (Cpp_ir.Types.prints_as_any ty) | None -> false in
        match planned_binder_type ~use:"coerced from" ~agree:(fun p l -> decided p = decided l) i occ with
        | Some ty when not (Cpp_ir.Types.prints_as_any ty) -> Some ty
        | _ -> Some (cpp_of_ml env from) )
      | _ -> Some (cpp_of_ml env from) )
    (* [Core.Expr.Boxed_value] is extraction's reading of the Coq typing.  A binder whose
       C++ type was decided at its binding site outranks it: a type-class
       method returning [M A] is opaque in Coq, but Crane emits the
       instance's [M] as a template, so the value here has the concrete type
       the binder was assigned and there is no box to open. *)
    | None when boxed -> (
      match t with
      | Core.Expr.Bound_variable {index = i; occurrence = occ} -> (
        match planned_binder_type ~use:"boxed from" ~agree:( = ) i occ with
        | Some ty -> Some ty
        | None -> Some Cpp_ir.Type.Any )
      | _ -> Some Cpp_ir.Type.Any )
    | None -> None
  in
  ( match expected_ty with
    | Some ty when not (Cpp_ir.Types.prints_as_any ty) && ty <> Void
                  && not (match ty with Entity_application (g, _, _) -> Table.is_erased_type_const g | _ -> false) ->
      (* The position's type, as the expressions below write it. *)
      let ty_ir = ty in
      let rec is_cpp_erased_var_rec = function
        | Core.Expr.Bound_variable {index = i; occurrence = occ} -> read_is_boxed i occ
        | Core.Expr.Coerce {value = t'; _}
        | Core.Expr.Boxed_value {value = t'; _}
        | Core.Expr.Lambda_group_barrier {value = t'; _} ->
          is_cpp_erased_var_rec t'
        | _ -> false
      in
      let is_cpp_erased_var = is_cpp_erased_var_rec t in
      (* Namespace-collapsing erase: a namespaced leaf like [R] must become
         plain [std::any], not the malformed [typename R::std::any] the shared
         [erase_type_to_any] produces for a [Tnamespace]-wrapped [Core.Type.Global_app].
         This unwraps the erased var to its runtime representation
         ([deque<std::any>] for a custom list of [R]); a downstream consumer
         that needs the CONCRETE element container (e.g. a constructor field
         of type [deque<R>]) converts it with [crane_container_cast] at its
         own site (mirroring [eta_fun]'s function-argument path). *)
      if is_cpp_erased_var then
        (* Canonical erased shape is [deque<std::any>] (a bare [std::any]
           per element, not a structure-preserving [pair<any,any>]) -- see
           the matching fix in the [Core.Expr.Bound_variable] case above. *)
        let erase_top_args : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
          | Entity_application (g, args, ns) when args <> [] ->
            Entity_application (g, List.map (fun _ -> Cpp_ir.Type.Any) args, ns)
          | In_namespace (ns_g, Entity_application (g, args, ns)) when args <> [] ->
            In_namespace (ns_g, Entity_application (g, List.map (fun _ -> Cpp_ir.Type.Any) args, ns))
          | t -> t
        in
        coerce ~from:Any ~into:(erase_top_args ty) inner
      else if ml_expr_is_erased env t then
        (* Extraction's oracle reads a type-class method's [M A] as erased,
           but the binder it is bound to was assigned an opaque type --
           an admission that the shape could not be resolved, not a box.
           Say so rather than assert [Tany]: {!coerce} recovers from a box
           and must not invent one. *)
        let opaque = Some (Cpp_ir.Type.Obligation Opaque_type) in
        let rec binder_is_opaque = function
          | Core.Expr.Bound_variable {index = i; occurrence = occ} ->
            planned_binder_type ~use:"opaque binder"
              ~agree:(fun p l -> (p = opaque) = (l = opaque))
              i occ
            = opaque
          | Core.Expr.Coerce {value = t'; _}
          | Core.Expr.Boxed_value {value = t'; _}
          | Core.Expr.Lambda_group_barrier {value = t'; _} ->
            binder_is_opaque t'
          | _ -> false
        in
        coerce
          ~from:(if binder_is_opaque t then Cpp_ir.Type.Obligation Opaque_type else Cpp_ir.Type.Any)
          ~into:ty inner
      else
        (* [ml_expr_is_erased] only recognises a handful of shapes and says
           [false] for the rest.  Extraction already unified the two sides
           here, so fall back on what it recorded rather than on the
           oracle's silence. *)
        ( match recorded_from with
          (* Only the boxed dimension: extraction's [from] describes the
             Coq-level type, and the pointer- and converting-constructor
             dimensions at this boundary have already been settled by the
             sub-expression that produced [inner]. *)
          (* Unless the value is a component just read out of an erased
             pair and the type the context has in mind is itself a pair:
             that read already handed back the component's own box, so the
             context's type describes the enclosing pair, not the component,
             and recovering here would name the wrong one.  When the context
             wants a non-pair, it is talking about the component, and the
             box does have to be opened. *)
          | Some from
            when Cpp_ir.Types.prints_as_any from
                 && not
                      ( reads_erased_pair_component env t
                      &&
                      match ty with
                      | Entity_application (g, _, _) -> is_prod_global g
                      | _ -> false ) ->
            coerce ~from ~into:(boxed_shape_of ty_ir) inner
          | Some _
            when ( match coercion with
                 | Some (from, _) -> absurd_coercion from ty
                 | None -> false ) -> (
            match coercion with
            (* Absurd only at some instantiations: [tt] read at the index [T1]
               of [Inc : incE unit] is dead unless [T1] is [unit] -- or the
               box an erased handler instantiates it at.  Which, C++ decides
               once it substitutes [T1]. *)
            | Some (from, _) when contains_tvar ty ->
              Cpp_ir.Build.iife (Some ty)
                [ If_constexpr
                    { test = Convertible (ty, Reference (Lvalue, Const (cpp_of_ml env from)));
                      then_ = [Return (Some (Convert (ty, inner)))];
                      else_ = [Throw dead_branch_message] } ]
            | _ -> Abort (dead_branch_message, ty) )
          | _ -> inner )
    | _ -> inner )
