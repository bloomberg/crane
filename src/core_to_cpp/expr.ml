(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Expressions: {!gen_expr_typed} lowers a Core expression to a CppIR expression,
    dispatching on its form.  The last of the lowering modules
    ({!Knot} lists the order), driven by {!Lower_expr}.  A variable read, a global used as a value, a
    literal and a coercion's crossing ({!gen_crossing}) are lowered here; a
    lambda, an application, a constructor, a match, an effect and a let or
    local fixpoint (as an immediately invoked lambda over statements) go to
    their modules, which recurse back through {!Knot}. *)

open Base.Common
open Names
open Base.Core_util
open Base.Table
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query

(** Whether [e] is a lambda once its coercions are expanded. *)
let is_lambda (e : Cpp_ir.Lowered.Expr.t) = match Cpp_passes.Coercions.head e with Lambda _ -> true | _ -> false
open Application
open Construction
open Match
open Stmts
module Typed = Cpp_ir.Typed


(** The type variable the definition whose body is being generated returns
    boxed, its arguments carrying it only as a type index
    ({!Base.Type_util.index_only_result_tvar}): [Some 1] in [eval : expr A ->
    A]. *)
let own_index_only_result cx =
  Option.bind (Option.bind cx.ctx.input.body_owner find_type_opt) Base.Type_util.index_only_result_tvar

(** Under [CRANE_CHECK_IR], that the variable at de Bruijn index [i] is one
    binder to both of the scopes translation keeps: [env], which names it, and
    the binder environment ({!current_lexenv}), which types it.  The two are
    pushed side by side at every binding, and nothing but the position ties an
    entry of one to an entry of the other, so a binder pushed to one alone, or
    in another order, retypes every variable beneath it.  The renamed C++
    identifier is what both record.  An instance's dictionary is the one
    binder named and not typed: inside its methods it is a template parameter
    of the enclosing struct. *)
let check_binder_scopes cx env i =
  if Base.Probe.checking () then
    match (get_db_name_opt i env, get_env_binder_opt cx i) with
    | Some x, Some b when Id.equal x b.id -> ()
    | Some x, None when Base.Common.is_tc_instance_id x -> ()
    | x, b ->
      let name = Option.cata Id.print (Pp.str "nothing") in
      Base.Probe.violation "binder scopes"
        Pp.(
          str "the variable at index " ++ int i ++ str " is " ++ name x ++ str " to the names in scope and "
          ++ name (Option.map (fun b -> b.id) b)
          ++ str " to the binders typed in scope")

(** [unit_parameter_adapter x cglob] is the callable value of the global
    function [x], named [cglob], where its declaration left a [unit]
    parameter out ({!Base.Type_util.declaration_drops_binder}): a lambda taking one
    parameter per value domain of [x]'s type, as a slot of that type calls
    it, and forwarding the ones the declaration kept.  [None] where the
    declaration keeps every parameter, or is not one Crane writes. *)
let unit_parameter_adapter cx x (cglob : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t option =
  if Base.Table.is_custom x || Base.Table.is_projection x || Option.has_some (Unit_plan.Cpp_names.lookup_method_this_pos x) then None
  else
    match callee_core_type cx x with
    | None -> None
    | Some ty ->
      let doms =
        List.filter (fun d -> not (Base.Table.is_typeclass_type d)) (Base.Type_util.core_value_domains ty)
      in
      if not (List.exists Base.Type_util.declaration_drops_binder doms) then None
      else
        let params =
          List.mapi
            (fun j d ->
              ( ( (Reference (Lvalue, Const Auto) : Cpp_ir.Lowered.Type.t),
                  Some (Id.of_string (Printf.sprintf "_wa%d" j)) ),
                Base.Type_util.declaration_drops_binder d ) )
            doms
        in
        let args =
          List.filter_map
            (fun ((_, id), dropped) -> if dropped then None else Some (Local (Option.get id) : Cpp_ir.Lowered.Expr.t))
            params
        in
        let call = Cpp_ir.Build.call cglob args in
        let body : Cpp_ir.Lowered.Stmt.t list =
          if Monadic.core_type_is_void_call ty then [Expression call] else [Return (Some call)]
        in
        Some (Cpp_ir.Build.lambda (List.map fst params) None body ~capture:Stored)

(** [gen_expr slot env core_e] -- the CppIR expression for the
    Core expression [core_e], generated against the type [slot] states
    ([Slot.into]), inside a body returning [slot.ret].  A global that is called when named
    ({!Suspension.naming_calls}: a definition that only throws, emitted as a
    zero-parameter function) becomes a call of no arguments in the
    [Core.Expr.Global] case.

    A [Boxed] slot says that [core_e] flows into a slot that is really
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
let rec gen_expr_typed cx (slot : Slot.slot) env (core_e : Core.Expr.t) : Typed.t =
  Typed_checks.typed_lowering cx core_e (gen_form cx slot env core_e)

(** The typed lowering of [core_e], by its form. *)
and gen_form cx (slot : Slot.slot) env (core_e : Core.Expr.t) : Typed.t =
  let ret = slot.Slot.ret and expected_ty = Slot.expected slot in
  let form = Typed_checks.of_built cx env core_e in
  (* A form module that types its result; where it could not, as [form]. *)
  let typed_form (x : Typed.t) = if Cpp_ir.Value_type.unstated x.ty then form x.expr else x in
  match core_e with
  (* [unit] has one value, so a read of a [unit] binder is that value: the
     binder may have no C++ parameter at all ({!Base.Type_util.declaration_drops_binder}). *)
  | Core.Expr.Bound_variable {index = i; _}
    when (match get_env_type_opt cx i with Some t -> core_type_is_unit t | None -> false) ->
    Typed.v ~ty:(Binders.read_value_type cx env i) (Monadic.mk_tt_expr ())
  | Core.Expr.Bound_variable {index = i; occurrence = occ} ->
    check_binder_scopes cx env i;
    let boxed_read = Binders.read_is_boxed cx i occ in
    let x = try get_db_name i env with Failure _ -> db_fallback_id i in
    let var_expr : Cpp_ir.Lowered.Expr.t = Local x in
    (* Move on a last use of a variable the region owns, as its plan says
       ({!Ownership_ir.Region.use}); a boxed variable is unboxed whole, whatever
       component of it Core reads.  Never move a typeclass instance -- it is a type reference in the concept
       paradigm, not an owned value, and wrapping it produces invalid C++ like
       [std::move(_tcI0)::method()].  Recognised by identity rather than by Core
       type: this binder is synthesised by {!Base.Common.tc_instance_id}, and inside
       a generated instance method it is a template parameter of the enclosing
       struct, with no entry of its own in [env_types]. *)
    let move_candidate =
      (not (Base.Common.is_tc_instance_id x))
      &&
      match Ownership_ir.Region.use ~boxed:boxed_read cx.ctx.lexical.move_plan occ with
      | Some ((Share | Clone | Copy) as copy) ->
        (* The copy the plan names is the one the variable's declaration
           makes, where Core says what its type is. *)
        ( if Base.Probe.checking () && Ownership_ir.Region.read_is_typed cx.ctx.lexical.move_plan occ then
            match Binders.binder_cpp_type cx i with
            (* [auto] says nothing of the type it deduces. *)
            | Some Cpp_ir.Type.(Auto | Const Auto | Reference (_, (Auto | Const Auto))) -> ()
            | Some declared when Ownership_ir.Region.copy_of_declared declared <> copy ->
              let name : Ownership_ir.Region.Use.t -> string = function
                | Share -> "shares" | Clone -> "clones" | Copy -> "copies" | Move -> "moves" | Borrow -> "borrows"
              in
              Base.Probe.violation "copy mode"
                Pp.(
                  str "the plan " ++ str (name copy) ++ str " " ++ Id.print x ++ str " where its declaration "
                  ++ str (name (Ownership_ir.Region.copy_of_declared declared)) ++ str " it" )
            | Some _ | None -> () );
        false
      | Some use -> use = Move
      | None ->
        Base.Probe.violation "unplanned read"
          Pp.(str "the read of " ++ Id.print x ++ str " is in no plan of the region it is lowered in");
        false
    in
    let result : Cpp_ir.Lowered.Expr.t = if move_candidate then Move var_expr else var_expr in
    (* A boxed read is a box, whatever the binder's type converts to. *)
    let read_ty : Cpp_ir.Lowered.Value_type.t =
      match Binders.read_value_type cx env i with
      | Typed t when boxed_read && not (Cpp_ir.Types.prints_as_any t) -> Typed Any
      | Deduced Untranslated when boxed_read -> Typed Any
      (* A binder no C++ type was decided for whose Core type is opaque
         holds the box an erased value is represented by: only a binder
         declared opaque is an admission. *)
      | Typed (Obligation Opaque_type)
        when (match Option.map Binders.strip_param_wrappers (Binders.binder_cpp_type cx i) with
              | None | Some Auto -> true | Some _ -> false) -> Typed Any
      | v -> v
    in
    let read = Typed.v ~ty:read_ty result in
    if boxed_read then begin
      match expected_ty with
      | Some (Variable (Index (n, _))) when own_index_only_result cx = Some n ->
        (* The definition returns this variable boxed, and nothing else spells
           it: its template parameter is the caller's instantiation -- in a
           machine the outermost call's -- not the type of a value read at
           the variable at some other depth. *)
        read
      | Some ty when not (Cpp_ir.Types.prints_as_any ty) && ty <> Void ->
        if Types.resolves_to_any_type cx ty then read
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
          (* Does [ty] denote a list container, possibly under an [In_namespace]
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
          let unbox_at t = Cpp_ir.Typed.of_node ~fallback:Cpp_ir.Typed.unannotated (Coerce.unbox t result) in
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
      | _ -> read
    end
    else
      (* A local function that takes more arguments than the slot hands it at
         once -- a [let fix] or a parameter of type [nat -> nat -> nat] where
         a [nat -> (nat -> nat)] is expected -- is curried to the slot, as a
         global named as a value is. *)
      let unfolded = Option.map (fun t -> Types.unfold_cpp_typedef cx env (strip_cpp_ref_const t)) in
      let expected = unfolded expected_ty in
      let curries t =
        match (expected, unfolded t) with
        | Some (Function ((_ :: _ as exp_dom), _)), Some (Function (dom, _)) -> List.length dom > List.length exp_dom
        | _ -> false
      in
      ( match
        ( expected,
          unfolded
            (Binders.planned_binder_type_or_derive cx ~use:"curried read"
               ~agree:(fun p l -> curries p = curries l) env i occ) )
      with
      | Some (Function ((_ :: _ as exp_dom), _)), Some (Function (dom, _))
        when List.length dom > List.length exp_dom -> (
        (* The closure reads the function where it is made, and takes it
           there where this read moves it. *)
        match (Coerce.eta_global cx env ?expected_ty (get_env_type_opt cx i) var_expr,
          var_expr) with
        | e, Local x when move_candidate && is_lambda e -> Typed_checks.adapted_to expected (Coerce.moving x e)
        | e, _ when e == var_expr -> Typed.rewrap (fun _ -> e) read
        | e, _ -> Typed_checks.adapted_to expected e )
      (* And the converse: a function the variable holds curried -- a
         parameter a type variable stands at, a fold's accumulator -- read
         where the slot takes its arguments at once, a local fixpoint's
         parameter of type [nat -> nat -> nat]. *)
      | Some (Function _ as into), Some (Function _ as from) -> (
        match (Coerce.into_slot ~origin:Rg (Typed.typed from var_expr) (Exactly into), var_expr) with
        | e, Local x when move_candidate && is_lambda e -> Typed_checks.adapted_to (Some into) (Coerce.moving x e)
        | e, _ when is_lambda e -> Typed_checks.adapted_to (Some into) e
        | _ -> read )
      | _ -> read )
  (* A singleton class's dictionary applied, which is the body of the class's
     projection: the method, called on the instance -- a template parameter,
     so a static member -- at the method's own type variables, which here are
     the projection's, numbered past the class's parameters. *)
  | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; occurrence = occ};
                     arguments = args} when singleton_call cx env i occ <> None ->
    typed_form @@ Application.gen_singleton_dictionary_call cx (Slot.at ~ret ()) env ~i ~occ ~args
  (* Every application translation is handed is canonical
     ({!Core_passes.Spines}): no head here is a global already applied, a
     coercion, or a one-branch match, and no numeral literal is spelled
     as a converter's application or as a constructor term. *)
  | (Core.Expr.Apply _ | Core.Expr.Construct _) as e when Base.Probe.checking ()
    && not (Core_passes.Spines.canonical_application e) ->
    Base.Probe.violation "non-canonical application" (Pp.str "a term Core_normalize writes otherwise");
    gen_expr_typed cx slot env (Core_passes.Spines.spine e)
  | Core.Expr.Apply {callee = Core.Expr.Global ({callee = r; _} as use);
                     arguments = a1 :: l} when Monadic.is_effect cx Core_plan.Effects.Return use ->
    form @@ Effects.gen_return_expr cx (Slot.at ~ret ()) env ~r ~use ~a1 ~l
  (* | Core.Expr.Apply (Core.Expr.Global {callee = h; _}, a1 :: a2 :: l) when is_hoist h -> gen_expr env
     (Core.Expr.Apply (a1, a2::[])) *)
  | Core.Expr.Apply {callee = Core.Expr.Global use;
                     arguments = _ :: _ :: _} as a
    when Monadic.is_sequential_effect cx Core_plan.Effects.Bind use ->
    form @@ Effects.gen_bind_expr cx (Slot.at ~ret ()) env a
  | Core.Expr.Apply {callee = (Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _); _} as a ->
    (* Nested fix application in expression context (e.g., S((fix aux ...) es)).
       Wrap in an IIFE, delegating to gen_stmts which handles Core.Expr.Apply(Core.Expr.Fixpoint
       ...). *)
    form @@ with_escape_analysis cx ~ret (fun ret -> with_region cx ~ret a (fun () ->
      Match_types.value_iife cx env (infer_core_body_type a) (fun into -> gen_stmts cx (Slot.at ~ret ()) env (Destination.Return into) a) ) )
  (* A class field is projected through the instance wherever the instance
     survived, whatever mapping the field carries, as Core decided it
     ({!Core_plan.Elaborate.static_projection_call}). *)
  | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args}
    when Core_plan.Elaborate.static_projection_call ~walk:(elaborations cx) ~lex:(current_lexenv cx ()) use args <> None ->
    typed_form @@ Application.gen_instance_projection cx slot env ~use ~args
  (* A closed call building a typeclass instance -- an event injection
     [ReSum_inr] composed from instances and closed lambdas, say -- is the
     same value every time it is evaluated, and evaluating it composes fresh
     closures.  It is built once and kept, as a closed constructor term is
     (see {!Cpp_passes.Constants}).  An instance is a pure value, so building it
     once cannot drop an effect; only where it comes out as a call.  Core
     decides which calls those are ({!Core_plan.Elaborate.closed_instance_call}). *)
  | Core.Expr.Apply {callee = Core.Expr.Global ({callee = f; _} as use); arguments = args} as e
    when (not slot.Slot.building_constant)
         && Core_plan.Elaborate.closed_instance_call ~walk:(elaborations cx) ~lex:(current_lexenv cx ()) use args -> (
    let built = gen_expr_typed cx (Slot.at ~ret ?expected_ty ~slot:{slot with Slot.building_constant = true} ()) env e in
    (* Kept, it is the value it builds. *)
    match Cpp_passes.Coercions.head built.expr with
    | Call _ ->
      Typed.rewrap
        (fun b ->
          Cpp_ir.Build.call
            (Runtime (Cpp_ir.Crane_rt.Constant (String.lowercase_ascii (Label.to_string (Base.Common.label_of_r f))))) [b] )
        built
    | _ -> built )
  | Core.Expr.Apply {callee = f; arguments = args} ->
    typed_form @@ Application.gen_application cx slot env f args
  | Core.Expr.Lambda _ as a ->
    typed_form @@ Lambda.gen_lambda cx slot env a
  | Core.Expr.Global ({callee = x; _} as use) when is_inline_custom x ->
    let tys = Base.Core_util.written_type_args use in
    let core_ty = callee_core_type_exn cx x in
    let ty = Types.cpp_of_core cx env core_ty in
    ( match ty with
    | Function (dom, cod) ->
      Typed_checks.adapted_or_node ~fallback:Cpp_ir.Typed.unannotated expected_ty (eta_fun cx (Slot.at ~ret ?expected_ty ()) env (Core.Expr.Global use) []).expr
    | _ ->
      let yields = Calls.glob_yields cx env x (Base.Core_util.instantiate_written ~reader:"glob_yields" use) in
      Typed.v ~ty:(match yields with Some t -> Typed t | None -> Deduced Foreign_text) @@ mk_cppglob
        ?yields
        x
        (Types.template_params_of_core cx ~site:Cpp_ir.Types.Declared env
           (List.map snd (Base.Core_util.Var_types.bindings tys)) ) )
  | Core.Expr.Global ({callee = x; _} as use) ->
    let tys = Base.Core_util.written_type_args use in
    let tvars = get_current_type_vars cx in
    (* Each argument with the variable it was written for. *)
    let by_var =
      List.map
        (fun (v, ty) ->
          let t = Types.cpp_of_core cx env (type_simpl ty) in
          ( Core.Scheme.Var.ordinal v,
            match t with
            | Variable (Index (_, None)) when tvars <> [] -> Cpp_ir.Type.Erased Type
            | _ -> t ) )
        (Base.Core_util.Var_types.bindings tys)
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
                | Some (_, b) when Types.names_only_scoped_tvars cx b -> b
                | _ -> t )
              | None -> t ) )
        by_var
    in
    (* A global passed as a function value -- [MonadIter_itree] at a slot
       [MonadIter m] -- has its erased type arguments stated by the callable
       the slot takes. *)
    let by_var =
      match (List.exists (fun (_, t) -> Cpp_ir.Types.prints_as_any t) by_var, slot.Slot.call_result) with
      | true, (Some _ as res) -> (
        match Calls.instance_family_binding cx env x tys res with
        | Some (_, names, m) -> fill_from (names, m) by_var
        | None -> by_var )
      | _ -> by_var
    in
    let result_bindings () = Calls.callee_result_bindings cx env x ~explicit:true expected_ty in
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
                | Some (_, b) when Types.names_only_scoped_tvars cx b -> Some (k + 1, b)
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
      Calls.glob_yields cx env x (Base.Core_util.instantiate_written ~reader:"glob_yields" use)
    in
    let cglob =
      mk_cppglob ?yields x (Calls.written_at_variables cx x (filter_erased_keyed by_var))
    in
    let instantiated = Calls.instantiated_type cx use in
    (* A custom constant with no Core type is the text it maps to: C++
       alone knows its type. *)
    let or_foreign (v : Cpp_ir.Lowered.Value_type.t) : Cpp_ir.Lowered.Value_type.t =
      if Cpp_ir.Value_type.unstated v && is_custom x then Deduced Foreign_text else v
    in
    if Suspension.naming_calls cx ~cpp_of:(Types.cpp_of_core cx env) x then
      (* A function of no parameters named is called, a call made of this
         use. *)
      Typed.v ~ty:(or_foreign (Typed_checks.core_value_type cx env instantiated))
        (made_of (Core.Global_use.occurrence use) (Cpp_ir.Build.call cglob []))
    else
      let named = Typed.v ~ty:(or_foreign (Typed_checks.global_value_type cx env x instantiated)) cglob in
      ( match
          Option.map
            (fun ty ->
              materialise_opaque (Types.cpp_of_core cx env (expand_core_fun_alias ty)))
            (callee_core_type cx x)
        with
      (* A declaration whose result erased -- because its Rocq type hides
         the quantifier behind a type alias, or because a type index alone
         pins the result down -- hands back a box whatever the use site's
         instantiation says, so a use site naming concrete types reaches it
         through the adapter {!Coerce.coerce} builds.  The type the use site wants
         is the slot's when there is one; failing that, a single type
         argument tells what the one quantifier every erased position came
         from was instantiated at. *)
      | Some from
        when (match from with Function (_, cod) -> Cpp_ir.Types.prints_as_any cod | _ -> false)
        ->
        let into =
          match (expected_ty, tys_cpp) with
          | Some into, _ when Types.names_only_scoped_tvars cx into -> Some into
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
           one is not ({!Functions.gen_dfun}) -- and a template is no
           value a conversion can take whole: an adapter at the declared
           signature, at this use's type arguments, is. *)
        let named = if cglob == named.expr then named else Typed.v ~ty:Typed.unannotated cglob in
        let cglob =
          match from with
          | Function (dom, _)
            when List.exists
                   (fun (f : Cpp_ir.Lowered.Type.t) ->
                     match f with Function _ -> not (is_fully_erased_fun_ty f) | _ -> false )
                   dom ->
            Coerce.eta_global cx env ~exact:true (Option.map expand_core_fun_alias instantiated) cglob
          | _ -> cglob
        in
        let named =
          if cglob == named.expr then named
          else Typed_checks.adapted_to (Option.map (Types.cpp_of_core cx env) instantiated) cglob
        in
        ( match into with
        | Some into -> Typed_checks.adapted ~before:named (Some into) (Coerce.coerce cx ~from ~into cglob)
        | None -> named )
      | _ -> (
        match unit_parameter_adapter cx x cglob with
        | Some adapter -> Cpp_ir.Typed.of_node ~fallback:Cpp_ir.Typed.unannotated adapter
        | None -> Typed_checks.adapted ~before:named expected_ty (Calls.curry_to_expected cx env ?expected_ty use cglob) ) )
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _} when is_custom r ->
    ( match gen_expr_custom_cons cx slot env ty r ts with
    (* A nullary constructor is its name, typed at the instantiation it was
       built at, which may group a function type as its slot does. *)
    | Entity (_, _, Some {custom_yields = Some t; _}) as e -> (
      match form e with
      | {ty = Typed t0; _} when t0 <> t && Cpp_ir.Types.same_arrows_unqualified t0 t -> Typed.v ~ty:(Typed t) e
      | x -> x )
    | e -> form e )
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
          Id.of_string (Base.Common.enum_ctor_name_of_ref kn i cidx) )
      | _ ->
        CErrors.anomaly
          (Pp.str "gen_expr: enum constructor expected ConstructRef")
    in
    Typed.v ~ty:(Typed_checks.core_value_type cx env (Some ty)) (Enum_value (ind_ref, ctor_name))
  (* A closed constructor term of a shared variant -- a numeral built from
     [xI]/[xO]/[xH], say -- is built once and kept, as ocamlopt keeps a
     structured constant: evaluated again, it is a count bump rather than an
     allocation per node.  The outermost closed term is the constant; the
     runtime makes every block it holds immortal too.  Only where the term
     comes out as its factory call: a conversion into another slot type is
     left as it is.  Core decides which terms those are
     ({!Core_plan.Elaborate.shared_constant}). *)
  | Core.Expr.Construct {arguments = ts; _} as e
    when (not slot.Slot.building_constant) && Core_plan.Elaborate.shared_constant ~walk:(elaborations cx) e
         && not (takes_reuse_token cx e) -> form @@ (
    let built = (gen_expr_typed cx (Slot.at ~ret ?expected_ty ~slot:{slot with Slot.building_constant = true} ()) env e).expr in
    match Cpp_passes.Coercions.head built with
    | Call (_, Type_member (Entity_application (n, _, _), _), _)
      when Base.Table.is_shared_variant n && ts <> [] ->
      Cpp_ir.Build.call (Runtime (Cpp_ir.Crane_rt.Constant (constant_name e))) [built]
    | _ -> built )
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = ts; _} as construction ->
    form @@ Construction.gen_construction cx slot env ~ty ~r ~ts construction
  | Core.Expr.Match {scrutinee_type = typ;
                     scrutinee = t;
                     branches = pv;
                     occurrence = case_occ}
                       when Core_plan.Elaborate.match_kind ~walk:(elaborations cx) typ pv case_occ = Core_plan.Match_kind.Custom ->
    form @@ Match.gen_custom_match_expr cx (Slot.at ~ret ~slot ()) env ~typ ~t ~pv ~case_occ
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = t; branches = pv; occurrence = case_occ}
    when Core_plan.Match_kind.is_record (Core_plan.Elaborate.match_kind ~walk:(elaborations cx) typ pv case_occ) ->
    let x = Match.gen_record_projection cx slot env core_e ~typ ~t ~pv ~case_occ in
    ( match (x, Match.read_class_method cx typ pv case_occ) with
    (* A class method named, not called: a function's name. *)
    | Scope _, Some m -> Typed.v ~ty:(Typed_checks.global_value_type cx env m (Typed_checks.core_type_of cx core_e)) x
    | _ -> form x )
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = t; branches = pv; occurrence = case_occ} when lang () == Cpp ->
    form @@ gen_cpp_case cx (Slot.at ~ret ~slot ()) typ t env pv case_occ
  | Core.Expr.Let {binder_type = ty; _} as a ->
    (* The lambda returns the let's value, at the position's type, and its
       region is planned at that return type too: planned under the
       enclosing function's, a coercion at the let's tail would be planned
       against a position lowering does not give it. *)
    form @@ with_escape_analysis cx ~ret (fun _ -> (let ret = expected_ty in
      with_region cx ~ret a (fun () ->
        (* Returning a closure from one path and another closure, or a
           function-typed local, from the next, the lambda deduces no
           common type: it is declared at the let's own, or at the expected
           type where that only regroups its arrows.  Otherwise the expected
           type is what the caller converts to, which need not be a type the
           lambda's returns share. *)
        Match_types.value_iife ?ret:expected_ty cx env (infer_core_body_type a) (fun into ->
            gen_stmts cx (Slot.at ~ret ~slot ()) env (Destination.Return into) a ) ) ) )
  | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ as a ->
    (* Bare fixpoint in expression context: wrap in IIFE, delegate to
       gen_stmts. *)
    form @@ with_escape_analysis cx ~ret (fun ret -> with_region cx ~ret a (fun () ->
      Match_types.value_iife cx env (infer_core_body_type a) (fun into -> gen_stmts cx (Slot.at ~ret ()) env (Destination.Return into) a) ) )
  | Core.Expr.String s -> Typed.v ~ty:(Typed_checks.primitive_type cx env "strings.pstring.type") (Literal (String s))
  | Core.Expr.UInt63 x -> Typed.v ~ty:(Typed_checks.primitive_type cx env "num.int63.type") (Literal (Uint63 x))
  | Core.Expr.Numeral {inductive = ind; value = n} ->
    Cpp_ir.Typed.of_node ~fallback:(Typed_checks.core_value_type cx env (Some (Typed_checks.inductive_type ind))) @@ (
    match Base.Table.get_numeral_info ind with
    | Some info -> Cpp_build.render_numeral info n
    | None ->
      CErrors.anomaly Pp.(str "a literal of " ++ Printer.pr_global ind ++ str ", which has no numeral mapping") )
  | Core.Expr.Float64 f -> Typed.v ~ty:(Typed_checks.primitive_type cx env "num.float.type") (Literal (Float f))
  | Core.Expr.Persistent_array {elements = elems; default = def} ->
    form @@ let elems = Array.map (fun e -> (gen_expr_typed cx (Slot.at ~ret ()) env e).expr) elems in
    let def = (gen_expr_typed cx (Slot.at ~ret ()) env def).expr in
    Persistent_array (elems, def)
  | Core.Expr.Coerce {source_type = from; target_type = into; value = t; occurrence = occ} ->
    form @@ gen_crossing cx slot env ~coercion:(Some (from, into)) ~boxed:false t occ
  | Core.Expr.Boxed_value {value = t; occurrence = occ} ->
    form @@ gen_crossing cx slot env ~coercion:None ~boxed:true t occ
  | Core.Expr.Lambda_group_barrier {value = t; occurrence = occ} ->
    form @@ gen_crossing cx slot env ~coercion:None ~boxed:false t occ
  | Core.Expr.Erased_value _ ->
    (* An erased proof or type reaching an expression position: a dead one,
       an absurd branch.  Where it is a value a constructor stores it is the
       empty box instead, see {!gen_stored_value}. *)
    Cpp_ir.Typed.v ~ty:Never @@ Abort ("unreachable", Cpp_build.abort_ty expected_ty)
  | Core.Expr.Runtime_error msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    Cpp_ir.Typed.v ~ty:Never @@ Abort (msg, Cpp_build.abort_ty expected_ty)
  | Core.Expr.Axiom_value s -> Cpp_ir.Typed.v ~ty:Never @@ Abort ("unrealized axiom: " ^ s, Cpp_build.abort_ty expected_ty)
  | _ -> CErrors.anomaly (Pp.str "gen_expr: unhandled ML AST node")

(** A term crossing a type gap erasure opened: a [Core.Expr.Coerce] with its
    [coercion] types, a [Core.Expr.Boxed_value] ([boxed]), or a
    [Core.Expr.Lambda_group_barrier] (neither), lowered against the position
    type {!Position_plan} planned for its occurrence [occ]. *)

and gen_crossing cx (slot : Slot.slot) env ~coercion ~boxed t occ :
    Cpp_ir.Lowered.Expr.t =
  let ret = slot.Slot.ret and expected_ty = Slot.expected slot in
  let expected_ty = Binders.planned_position cx occ ~live:expected_ty in
  (* A value crossing into a slot that is really [std::any] has to be built
     at the canonical erased shape -- every component boxed -- because the
     consumer recovers it with a fixed [any_cast] and cannot know the
     concrete component types.  Extraction recorded both sides of this
     boundary, so ask for that shape whenever [into] is the erased one and
     [from] is not.  See {!Base.Type_util.slot_repr}. *)
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
      && Cpp_ir.Types.prints_as_any (Types.cpp_of_core cx env into)
      && not (Cpp_ir.Types.prints_as_any (Types.cpp_of_core cx env from)) ->
      Some (Types.box_kind_of_cpp_type (Types.cpp_of_core cx env into))
    | Some _ | None -> None
  in
  (* A lambda is written against the slot it fills -- its binders and
     arity are the slot's -- and a coercion cannot reshape a callable after
     the fact. *)
  let inner_typed =
    gen_expr_typed cx (Slot.at ~ret ?expected_ty:(match t with Core.Expr.Lambda _ -> expected_ty | _ -> None) ~slot:
        (match into_box_kind with Some kind -> Slot.into_box kind slot | None -> slot) ())
      env t
  in
  let inner = inner_typed.expr in
  (* What the inner value is, as lowering typed it: a box where its type is
     one under any alias (a value-indexed family's [dt<>], a box variable),
     an abort at the type it prints at. *)
  let from : Cpp_ir.Lowered.Type.t option =
    match (inner, inner_typed.ty) with
    | Abort (_, t), _ -> Some t
    | _, Typed t ->
      let al = Coerce.aliases_in cx in
      let n = Coerce.normal al t in
      let family_box =
        (* An alias template of a box ([payload_ty<T1>] for [using
           payload_ty = crane::obj]): the box, whatever its arguments. *)
        let rec head (t : Cpp_ir.Lowered.Type.t) =
          match t with
          | In_namespace (_, t) | Const t | Reference (_, t) -> head t
          | t -> t
        in
        match head t with
        | Entity_application (g, _ :: _, ns) ->
          Types.resolves_to_any_type cx (Entity_application (g, [], ns))
        | _ -> false
      in
      if Base.Type_util.names_erased_alias n || al.boxed_source n || family_box then Some Any else Some t
    | _ -> None
  in
  let boxed_from = match from with Some f -> Erasure.classify_erasure cx (Some f) = `Boxed | None -> false in
  (* [inner] put in a slot of type [into]: unboxed where it is a box, and
     otherwise, where [concrete], adapted from its own type. *)
  let cross ~concrete ~into =
    match from with
    | Some _ when boxed_from -> Coerce.coerce cx ~from:Any ~into inner
    | Some from when concrete -> Coerce.coerce cx ~from ~into inner
    | _ -> inner
  in
  (* Whether extraction recorded the term's own side of the boundary as
     erased: a box, or a type-class method's [M A] read at an opaque type.
     A binder whose C++ type is decided outranks the record: [md]
     destructured out of a typed pattern is a [List<metadata<std::any>>],
     whatever erased carrier application the coercion recorded for it; a
     type-class method returning [M A] is opaque in Coq, but its instance's
     [M] is a template, so the binder has the concrete type it was
     assigned. *)
  let recorded =
    let decided agree i occ use = Binders.planned_binder_type cx ~use ~agree i occ in
    let of_core core_from = Some (Types.cpp_of_core cx env core_from) in
    let ty =
      match (coercion, t) with
      | Some (core_from, _), Core.Expr.Bound_variable {index = i; occurrence = occ} -> (
        let is_decided = function Some ty -> not (Cpp_ir.Types.prints_as_any ty) | None -> false in
        match decided (fun p l -> is_decided p = is_decided l) i occ "coerced from" with
        | Some ty when not (Cpp_ir.Types.prints_as_any ty) -> Some ty
        | _ -> of_core core_from )
      | Some (core_from, _), _ -> of_core core_from
      | None, Core.Expr.Bound_variable {index = i; occurrence = occ} when boxed -> (
        match decided ( = ) i occ "boxed from" with Some ty -> Some ty | None -> Some Cpp_ir.Type.Any )
      | None, _ when boxed -> Some Cpp_ir.Type.Any
      | None, _ -> None
    in
    match ty with
    | Some ty when Cpp_ir.Types.prints_as_any ty ->
      if Erasure.classify_erasure cx (Some ty) = `Opaque then `Opaque else `Box
    | _ -> `None
  in
  let refined into =
    match inner_typed.ty with
    | Typed f -> Coerce.crossing_index_plan ~deduced:slot.Slot.deduced ~from:f ~into
    | _ -> None
  in
  ( match expected_ty with
    | Some ty when not (Cpp_ir.Types.prints_as_any ty) && ty <> Void
                  && not (match ty with Entity_application (g, _, _) -> Base.Table.is_erased_type_const g | _ -> false) ->
      let rec is_cpp_erased_var_rec = function
        | Core.Expr.Bound_variable {index = i; occurrence = occ} -> Binders.read_is_boxed cx i occ
        | Core.Expr.Coerce {value = t'; _}
        | Core.Expr.Boxed_value {value = t'; _}
        | Core.Expr.Lambda_group_barrier {value = t'; _} ->
          is_cpp_erased_var_rec t'
        | _ -> false
      in
      (* Namespace-collapsing erase: a namespaced leaf like [R] must become
         plain [std::any], not the malformed [typename R::std::any] the shared
         [erase_type_to_any] produces for an [In_namespace]-wrapped type.
         This unwraps the erased var to its runtime representation
         ([deque<std::any>] for a custom list of [R]); a downstream consumer
         that needs the CONCRETE element container (e.g. a constructor field
         of type [deque<R>]) converts it with [crane_container_cast] at its
         own site (mirroring [eta_fun]'s function-argument path). *)
      if is_cpp_erased_var_rec t then
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
        cross ~concrete:true ~into:(erase_top_args ty)
      else if Erasure.core_expr_is_erased cx env t then
        (* Extraction's oracle reads the value as erased: recovered where
           lowering typed it a box, left alone where opaque (an admission
           that the shape could not be resolved, not a box). *)
        cross ~concrete:true ~into:ty
      else if
        (* Extraction recorded the value's own side as erased; [from] says
           whether it is a box to open.  A side recorded opaque is an
           admission, not a box: the position recovering it is the one
           that knows its shape. *)
        recorded <> `None
        (* Unless the value is a component just read out of an erased
           pair and the type the context has in mind is itself a pair:
           that read already handed back the component's own box, so the
           context's type describes the enclosing pair, not the component,
           and recovering here would name the wrong one.  When the context
           wants a non-pair, it is talking about the component, and the
           box does have to be opened. *)
        && not
             ( Erasure.reads_erased_pair_component cx env t
             && match ty with Entity_application (g, _, _) -> is_prod_global g | _ -> false )
      then (if recorded = `Opaque then inner else cross ~concrete:true ~into:(Erasure.boxed_shape_of ty))
      else (
        match coercion with
        (* Absurd only at some instantiations: [tt] read at the index [T1]
           of [Inc : incE unit] is dead unless [T1] is [unit] -- or the
           box an erased handler instantiates it at.  Which, C++ decides
           once it substitutes [T1]. *)
        | Some (from, _) when Coerce.absurd_coercion cx from ty && contains_tvar ty ->
          Cpp_ir.Build.iife (Some ty)
            [ If_constexpr
                { test = Convertible (ty, Reference (Lvalue, Const (Types.cpp_of_core cx env from)));
                  then_ = [Return (Some (Convert (ty, inner)))];
                  else_ = [Throw Cpp_build.dead_branch_message] } ]
        | Some (from, _) when Coerce.absurd_coercion cx from ty -> Abort (Cpp_build.dead_branch_message, ty)
        (* A value at the index its match refined, or at the box a callee
           erased the index to ({!Coerce.crossing_index_plan}). *)
        | Some _ when Option.has_some (refined ty) ->
          Coerce.built (Option.get (refined ty)) inner_typed (Exactly ty)
        (* Only the boxed dimension: the pointer- and converting-constructor
           dimensions at this boundary have already been settled by the
           sub-expression that produced [inner]. *)
        | _ -> cross ~concrete:false ~into:ty )
    | _ -> inner )
