(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The template heads of generated declarations: which parameters are
    template-template parameters and at what arity, which applications a
    head takes back off, which defaults a parameter no signature mentions
    gets, and which parameters are phantom.  Decided from a declaration's
    types and signature, before anything is rendered -- the target plan's
    template-parameter kinds and callable plans -- and again as the
    declaration is generated, which must agree; {!Gen_functions},
    {!Gen_inductives} and {!Cpp_ind} ask, and the printer writes what the
    head says.  The rewrites a relaxation makes of the declaration under its
    head are {!Head_relaxation}'s. *)

open Miniml
open Names
open Util
open Ml_type_util

(** A C++ type, and a template parameter list, as a head is planned in. *)
type head_type = Cpp_ir.Lowered.Type.t

type head_params = Cpp_ir.Lowered.phase Cpp_ir.Template.parameters

(** A value parameter's or return type's spelling of the template parameter
    [id]: its head names it under either spelling a variable may have. *)
let head_tvar_is id (t : head_type) = Cpp_ir.Type.is_variable_named id t

(** Whether [t] names the template parameter [id] anywhere, a carrier
    abstraction's head included. *)
let head_tvar_named id (t : head_type) = Cpp_ir.Children.exists_type (head_tvar_is id) t

let head_type_exists (p : head_type -> bool) (t : head_type) = Cpp_ir.Children.exists_type p t

(** The name a variable goes by, whether or not its head was resolved. *)
let head_tvar_name : head_type -> Id.t option = function
  | Variable (Index (_, Some n) | Named n) -> Some n
  | Variable (Index (i, None)) -> Some (Common.tvar_id i)
  | _ -> None

(** Arity of every type variable that [cty] applies to arguments, keyed by
    template parameter name.  A Rocq parameter of kind [Type -> Type] reaches
    C++ as the head of an [Apply], and a plain [typename] cannot be applied,
    so such a parameter has to be declared [template <typename> class]. *)
let applied_tvar_arities (cty : head_type) =
  let arities = Hashtbl.create 4 in
  head_type_exists
    (fun t ->
      ( match t with
      | Apply (Variable (Named n), args) ->
        Hashtbl.replace arities n (List.length args)
      | Apply (Variable (Index (i, name)), args) ->
        (* The head may or may not have been resolved to its parameter name;
           key on both spellings so the caller's list matches either way. *)
        let arity = List.length args in
        Option.iter (fun n -> Hashtbl.replace arities n arity) name;
        Hashtbl.replace arities (Common.tvar_id i) arity
      | _ -> () );
      false )
    cty
  |> ignore;
  arities

(** Re-declare as template template parameters those entries of [temps] that
    [cty] applies to arguments; see {!applied_tvar_arities}.

    [ml_ty], when given, vetoes the promotion for a variable whose ML type does
    not demand the higher kind ({!Ml_type_util.higher_kinded_ml_tvars}: applied
    to something erasure left behind, or written where a generated constructor
    expects a template name).  Being applied is not on its own a reason to be
    higher-kinded -- when neither holds, the application
    can be taken back off, which {!deapply_plain_tvars} then does -- and the
    C++ type read here has not been through the relaxations, so it is not the
    place to look for the occurrence that would justify the higher kind. *)
let with_applied_tvars ?ml_ty (cty : head_type) (temps : head_params) : head_params =
  let arities = applied_tvar_arities cty in
  let arities =
    match ml_ty with
    | None -> arities
    | Some ty ->
      let hk = Ml_type_util.higher_kinded_ml_tvars [ty] in
      let veto = ref [] in
      head_type_exists
        (fun t ->
          ( match t with
          | Apply (Variable (Index (i, name)), _) when not (IntSet.mem i hk) ->
            veto := Common.tvar_id i :: !veto;
            Option.iter (fun n -> veto := n :: !veto) name
          | _ -> () );
          false )
        cty
      |> ignore;
      List.iter (Hashtbl.remove arities) !veto;
      (* A variable handed bare to a position another constructor declares
         [template <typename> class] is higher-kinded whether or not anything
         applies it, and no application can be taken back off to make it not
         be.  Added after the veto, which speaks only about applications. *)
      List.iter
        (fun (i, arity) -> Hashtbl.replace arities (Common.tvar_id i) arity)
        (Ml_type_util.hkt_arg_ml_tvar_arities [ty]);
      arities
  in
  if Hashtbl.length arities = 0 then temps
  else
    List.map
      (fun (tt, id) ->
        (* A phantom parameter is already spelled with a default, which a
           template template parameter cannot carry; leave it alone -- nothing
           in the signature will apply it either.

           Unless something does.  A variable handed to a position another
           constructor declares [template <typename> class] is written in the
           signature, at that position, and the phantom pass does not see it:
           translation spells such an argument as a bare template name, and
           the traversal that decides what is rendered reads the application
           it replaced.  Kept phantom, the declaration contradicts its own
           parameter's type -- [Sub<UBE, T1>] wants a template where [T1] is
           a [typename] -- so the arity wins over the default. *)
        match ((tt : _ Cpp_ir.Template.Parameter_kind.t), Hashtbl.find_opt arities id) with
        | (Typename | Typename_default Void), Some arity -> (Cpp_ir.Template.Parameter_kind.Template arity, id)
        | _ -> (tt, id) )
      temps

(** Template parameter list for a declaration whose parameters [vars] are used
    by the types [tys] -- an inductive's constructor fields, or the body of a
    type alias -- with the kinds of its positions.  The arities are read off
    the ML types rather than the converted C++ ones because the parameter list
    has to be fixed before the types are converted.  [applied], when given,
    is the rendered C++ body of a type alias, read instead of [tys] for the
    arities and for which parameters are phantom.  Returns the parameter list
    and its {!Tparam_kinds.t}; records nothing ({!hkt_templates} records). *)
let template_kinds ?(applied : head_type option) vars tys =
  (* Read from the rendered type where there is one: the ML body still applies
     a variable that erasure removed, and the parameter list has to agree with
     what the users of this name can see.  See
     {!Ml_type_util.rendered_tvar_arities_ir}. *)
  let arities =
    match applied with
    | Some a ->
      (* The alias's own rendering, under the same rule as an inductive's
         payloads below: applied only at erased or variable arguments --
         [IFun E F := forall T, E T -> F T], whose [T] erases -- is a family,
         and a family is a plain parameter. *)
      let arities = Ml_type_util.rendered_tvar_arities_ir a in
      let demanded = Hashtbl.create 4 in
      let rec scan : head_type -> unit = function
        | Apply (Variable (Index (i, _)), tys) ->
          if
            List.exists
              (fun (t : head_type) ->
                not (Cpp_ir.Types.prints_as_any t || match t with Variable _ -> true | _ -> false) )
              tys
          then Hashtbl.replace demanded i ();
          List.iter scan tys
        | Entity_application (_, tys, _) | Variant (_, tys) -> List.iter scan tys
        | Function (tys, ty) -> List.iter scan (ty :: tys)
        | Const ty | In_namespace (_, ty) | Reference (_, ty) | Shared_pointer ty -> scan ty
        | Apply (ty, tys) -> List.iter scan (ty :: tys)
        | _ -> ()
      in
      scan a;
      Hashtbl.filter_map_inplace
        (fun i ar -> if Hashtbl.mem demanded i then Some ar else None)
        arities;
      arities
    | None ->
      (* An inductive's parameter applied only at variables is an event
         family: [VisF : E X -> ...] applies it at the constructor's own
         existential, [inl1 : E1 X -> sum1 E1 E2 X] at the type's index
         parameter.  A family's C++ struct already has its index erased, so
         the parameter is a plain [typename] whose argument is that struct,
         and [E X] is written [E].  Only an application at a real type --
         [F (Free F A)] -- asks for a template name. *)
      let rec survives = function
        | Miniml.Tvar _ | Miniml.Tunknown | Miniml.Tdummy _ -> false
        | Miniml.Tmeta {contents = Some t} -> survives t
        | Miniml.Tmeta {contents = None} | Miniml.Topen _ -> false
        | _ -> true
      in
      let demanded = Hashtbl.create 4 in
      let rec scan = function
        | Miniml.Tapp (i, args) ->
          if List.exists survives args then Hashtbl.replace demanded i ();
          List.iter scan args
        | Miniml.Tglob (_, args, _) -> List.iter scan args
        | Miniml.Tarr (a, b) -> scan a; scan b
        | Miniml.Tmeta {contents = Some t} -> scan t
        | _ -> ()
      in
      List.iter scan tys;
      let arities = Ml_type_util.applied_ml_tvar_arities tys in
      Hashtbl.filter_map_inplace
        (fun i a -> if Hashtbl.mem demanded i then Some a else None)
        arities;
      arities
  in
  (* A parameter the rendered type never spells is phantom, whatever its Rocq
     kind was.  An erased event family is the case in point:
     [semantic_function := list nat -> itree E nat] writes no [E] in C++ at
     all, so declaring [E] a [template <typename> class] would demand a
     template of every use site for a position that holds nothing.  It is a
     plain parameter defaulted to [void], and {!Table.is_phantom_type_param}
     is what makes the use sites agree. *)
  let rendered = Option.map Ml_type_util.get_rendered_tvar_indices_ir applied in
  let rendered_in_cpp i =
    match rendered with None -> true | Some l -> List.mem i l
  in
  let temps : head_params =
    List.mapi
      (fun i n ->
        if not (rendered_in_cpp (i + 1)) then (Cpp_ir.Template.Parameter_kind.Typename_default Void, n)
        else
          match Hashtbl.find_opt arities (i + 1) with
          | Some arity -> (Template arity, n)
          | None -> (Typename, n) )
      vars
  in
  (* A default may only stand in the trailing run of defaulted parameters:
     [template <typename obj = void, typename c>] does not parse.  A phantom
     followed by a required parameter stays phantom -- no use writes an
     instantiation in it -- but has to be written, so it loses its default. *)
  let temps : head_params =
    let rec go : head_params -> head_params * bool = function
      | [] -> ([], true)
      | (tt, n) :: rest ->
        let rest, all_defaulted = go rest in
        ( match tt with
        | Typename_default _ when not all_defaulted -> (Typename, n) :: rest
        | Typename_default _ -> (tt, n) :: rest
        | _ -> (tt, n) :: rest ),
        all_defaulted
        && (match tt with Typename_default _ -> true | _ -> false)
    in
    fst (go temps)
  in
  let positions_of p =
    List.filteri (fun i _ -> p i) (List.mapi (fun i _ -> i) temps)
  in
  (* Applied in the definition and still plain: a family position. *)
  let applied_at_all =
    match applied with
    | Some a -> Ml_type_util.rendered_tvar_arities_ir a
    | None -> Ml_type_util.applied_ml_tvar_arities tys
  in
  ( temps,
    { Tparam_kinds.template_templates =
        List.filter_map
          (fun i ->
            match List.nth temps i with
            | Cpp_ir.Template.Parameter_kind.Template arity, _ -> Some (i, arity)
            | _ -> None )
          (List.mapi (fun i _ -> i) temps);
      families =
        positions_of (fun i ->
            Hashtbl.mem applied_at_all (i + 1) && not (Hashtbl.mem arities (i + 1)) );
      phantoms = positions_of (fun i -> not (rendered_in_cpp (i + 1))) } )

(** {!template_kinds}' parameter list, its kinds recorded so that {e uses} of
    [r] pass a bare template name where one is declared
    ({!Table.is_hkt_ind_param}). *)
let hkt_templates ?applied r vars tys =
  let temps, kinds = template_kinds ?applied vars tys in
  Tparam_kinds.record r kinds;
  temps

(** Relax a signature whose return type applies a template template parameter
    (see {!with_applied_tvars}).  In [F B fn(G g, F A x)] the variable [B] is
    named only by the return type, and C++ deduces nothing from a return type,
    so the call is ill-formed as written.  [B] is however pinned by the
    signature of the callback [g] that produces it, so [B] is redeclared last
    with that result as its default ([typename B = std::invoke_result_t<G &,
    A &>]) -- last because a default may only name parameters declared before
    it, and the callback is one of those.

    Returns the relaxed head and no rewrite: the declaration keeps its
    spelling.  Like every relaxation below, [decl] is read as a signature
    and the result is [(temps, rewrite)] ({!relax_function_head}). *)
let relax_applied_return (temps : head_params) (signature : Callable_abi.signature) =
  (* Only a template template parameter is applied here: a family is a plain
     parameter, written applied until {!deapply_plain_tvars} takes the
     application off, and its return type deduces as any other. *)
  let hk =
    List.filter_map
      (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) -> match tt with Template _ -> Some id | _ -> None)
      temps
  in
  let applies_tvar t =
    head_type_exists
      (function
        | Apply (head, _) -> List.exists (fun id -> head_tvar_is id head) hk
        | _ -> false )
      t
  in
  match signature with
  | {ret = cod0; params} when applies_tvar cod0 ->
    let is_tvar = head_tvar_is in
    let names = head_tvar_named in
    let undeducible id = not (List.exists (fun ty -> names id ty) params) in
    (* The result of the callback whose declared codomain is [id], spelled so
       that C++ can compute it from the callback's deduced type. *)
    let invoke_result id =
      List.find_map
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), fid) ->
          match tt with
          | Callable_declared (doms, cod) when is_tvar id cod ->
            Some
              (External
                 ( "std::invoke_result_t",
                   Reference (Lvalue, External (Id.to_string fid, []))
                   :: List.map (fun d -> (Reference (Lvalue, d) : head_type)) doms
                 ) : head_type)
          | _ -> None )
        temps
    in
    (* [id] is pinned by a callback rather than by an argument, so instead of
       naming it in the signature the declaration gives it that callback's
       result as its default and the return type keeps its own spelling.  The
       default names parameters declared after [id], so [id] moves to the end
       of the list; nothing supplies this signature's arguments explicitly, so
       the order is free. *)
    let computed : head_params =
      List.filter_map
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) ->
          match tt with
          | Typename when undeducible id ->
            Option.map (fun r -> (Cpp_ir.Template.Parameter_kind.Typename_default r, id)) (invoke_result id)
          | _ -> None )
        temps
    in
    let temps =
      List.filter
        (fun (_, id) -> not (List.exists (fun (_, j) -> Id.equal id j) computed))
        temps
      @ computed
    in
    (temps, None)
  | _ -> (temps, None)

(** Relax a signature whose return type applies a template template parameter
    that nothing deduces.

    [case_] returns [M X] for a caller-chosen [M : Type -> Type], and [M] is
    named by no argument: [template <typename> class T3] with the return type
    [T3<T4>] is a parameter the call site cannot supply and the compiler
    cannot infer.  {!relax_applied_return} answers the same question for a
    plain [typename] by giving it a default, but a [template <typename> class]
    parameter takes a template as its default, not a type, so there is nothing
    to default it to.

    What does pin the answer is the callback that produces it.  The handler
    [f] passed for [E ~> M] is a function object polymorphic in [X], so
    [std::invoke_result_t<F0 &, T1<T4> &>] is [M X] at the very instantiation
    this call needs.  The return type is rewritten to that, [T3] is dropped,
    and the callbacks that named it in their [requires] drop the constraint --
    [std::is_invocable_r_v<T3<std::any>, F0 &, T1<std::any> &>] was never a
    claim about this call anyway, since [std::any] stands in for the [X] the
    body chooses. *)
let relax_tt_applied_return (temps : head_params) (signature : Callable_abi.signature) =
  let kind_of id =
    List.find_map (fun (tt, i) -> if Id.equal i id then Some tt else None) temps
  in
  match signature with
  | {ret = Apply (head, [ret_arg]); params} -> (
    match head_tvar_name head with
    | Some id
      when kind_of id = Some (Cpp_ir.Template.Parameter_kind.Template 1)
           && not (List.exists (fun ty -> head_tvar_named id ty) params) ->
      (* The callback whose codomain is this application, and the argument it
         is applied to there -- [T3<std::any>], whose [std::any] stands for
         the [X] that the return type instantiates at [ret_arg]. *)
      let producer =
        List.find_map
          (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), fid) ->
            match tt with
            | Callable_declared (doms, Apply (h, [carrier])) when head_tvar_is id h ->
              Some (fid, doms, carrier)
            | _ -> None )
          temps
      in
      ( match producer with
      | None -> (temps, None)
      | Some (fid, doms, carrier) ->
        let at_ret_arg t =
          Cpp_ir.Types.map (fun t -> if t = carrier then ret_arg else t) t
        in
        let ret : head_type =
          External
            ( "std::invoke_result_t",
              Reference (Lvalue, External (Id.to_string fid, []))
              :: List.map (fun d -> (Reference (Lvalue, at_ret_arg d) : head_type)) doms )
        in
        let temps : head_params =
          List.filter_map
            (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), i) ->
              match tt with
              | _ when Id.equal i id -> None
              | Callable_declared (doms, cod) when List.exists (head_tvar_named id) (cod :: doms)
                -> Some (Cpp_ir.Template.Parameter_kind.Typename, i)
              | _ -> Some (tt, i) )
            temps
        in
        (temps, Some (Head_relaxation.Computed_return ret)) )
    | _ -> (temps, None) )
  | _ -> (temps, None)

(** Relax a signature in which a parameter's type is the only place a template
    template parameter is applied.

    [cast (e : E Y)] makes [E] a [template <typename> class] because [E Y] is
    the type of a parameter, and then nothing can supply it: an event family
    like [FailE], whose index Crane erases, reaches C++ as a plain struct, and
    a caller polymorphic in an [E] of its own passes a [typename].  Nor does
    the signature need [E] applied -- the parameter has one type, and C++
    deduces a type from the argument it is given.  So the parameter is given a
    template parameter of its own and [E] goes back to being a [typename],
    which is what its call sites spell.

    Only a variable applied {e nowhere else} qualifies.  Where the return type
    or a callback's [requires] also names it, the application is a claim about
    the shape of the instantiation -- [hk_map] returns [T1<T3>] for the very
    [T1] its argument came in at -- and a parameter deduced on its own would
    not carry it. *)
let relax_applied_param (temps : head_params) (signature : Callable_abi.signature) =
  let occurrences p ty =
    let n = ref 0 in
    ignore (head_type_exists (fun t -> if p t then incr n; false) ty);
    !n
  in
  let applies id : head_type -> bool = function Apply (h, _) -> head_tvar_is id h | _ -> false in
  match signature with
  | {ret; params} ->
    (* Last first, as the applications are named in that order. *)
    let param_tys = List.rev params in
    (* A position that takes the variable as a bare template name --
       [Sum1<T1, T2, T4>], whose first two arguments are templates -- states
       its kind outright: what is supplied there {e is} a template, so the
       parameter cannot be relaxed into a [typename] deduced from an
       argument. *)
    let passed_as_template id =
      List.exists
        (head_type_exists (function Type_constructor t -> head_tvar_named id t | _ -> false))
        (ret :: param_tys)
    in
    (* A variable applied in the parameters and named nowhere else: not by the
       return type, not by another template parameter's constraint, and not
       bare among the parameters either. *)
    let only_applied_in_params id =
      let total = List.fold_left (fun a t -> a + occurrences (head_tvar_is id) t) 0 in
      let applied =
        List.fold_left (fun a t -> a + occurrences (applies id) t) 0
      in
      applied param_tys > 0
      && total param_tys = applied param_tys
      && (not (passed_as_template id))
      && (not (head_tvar_named id ret))
      && not
           (List.exists
              (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), i) ->
                (not (Id.equal i id))
                &&
                match tt with
                | Callable_declared (doms, cod) -> List.exists (head_tvar_named id) (cod :: doms)
                | Typename_default d -> head_tvar_named id d
                | _ -> false )
              temps )
    in
    let relaxed =
      List.filter
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) ->
          match tt with
          | Template _ -> only_applied_in_params id
          | _ -> false )
        temps
    in
    if relaxed = [] then (temps, None)
    else begin
      (* One fresh parameter per application, named apart from the ones the
         signature already has. *)
      let taken = List.map snd temps in
      let fresh = ref [] in
      let next_name () =
        let rec pick k =
          let id = Generated_name.indexed "P" k in
          if List.exists (Id.equal id) taken then pick (k + 1) else id
        in
        pick (List.length !fresh)
      in
      (* One name per distinct application, not per occurrence: two positions
         spelled [T1<std::any>] came from the one ML type and denote the one
         C++ type, and giving them separate deduced parameters would let a
         call deduce them apart.  Sharing is also what lets the body be
         rewritten: it spells the application the same way the parameter did,
         and the name it must now use is the name that parameter took. *)
      let seen = ref [] in
      (* Keyed by the variable and the arguments it is applied to, not by the
         type node: the same application is spelled with whatever [Tvar]
         rigidity the position it was built in gave it. *)
      let key (t : head_type) =
        match t with
        | Apply (h, args) -> (
          match List.find_opt (fun (_, id) -> head_tvar_is id h) relaxed with
          | Some (_, id) -> Some (id, args)
          | None -> None )
        | _ -> None
      in
      let deduced t =
        match key t with
        | None -> None
        | Some k -> (
          match List.assoc_opt k !seen with
          | Some id -> Some id
          | None ->
            let id = next_name () in
            fresh := !fresh @ [(Cpp_ir.Template.Parameter_kind.Typename, id)];
            seen := (k, id) :: !seen;
            Some id )
      in
      (* Named in the order the parameters spell the applications. *)
      List.iter
        (fun ty ->
          ignore
            (Cpp_ir.Types.map
               (fun t ->
                 match deduced t with Some id -> (Variable (Named id) : head_type) | None -> t )
               ty ) )
        param_tys;
      let temps : head_params =
        List.map
          (fun (tt, id) ->
            if List.exists (fun (_, i) -> Id.equal i id) relaxed then
              (Cpp_ir.Template.Parameter_kind.Typename, id)
            else (tt, id) )
          temps
        @ !fresh
      in
      (temps, Some (Head_relaxation.Param_applications {relaxed = List.map snd relaxed; deduced = !seen}))
    end

(** Take the application back off a type variable that was left a plain
    [typename].

    A variable is declared [template <typename> class] only when the signature
    has to name it with no argument list ({!with_applied_tvars}).  When it does
    not, an occurrence like [T1<std::any>] is the application of a plain type
    to a type -- which does not parse -- and the honest spelling is [T1]: the
    index is erased, so the family applied at it is the event struct itself and
    there is nothing for the argument list to say.  Applied at an argument the
    declaration binds, it is [crane::rebind_t<T1, A>] ({!Head_relaxation.rebind_plain_var_lowered}):
    the variable may just as well be a type constructor given at its erased
    element, and then the argument is the element.

    The head and the rewrite of a declaration under it. *)
let deapplied_head (temps : head_params) =
  let plain =
    List.filter_map
      (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) -> match tt with Template _ -> None | _ -> Some id)
      temps
  in
  let in_scope = List.map snd temps in
  (* The parameters' own types too: a callable parameter's constraint
     ([is_invocable_r_v<T3, F1 &, T1<T2> &>]) and a default. *)
  let deapplied = Head_relaxation.deapplied_lowered ~plain ~in_scope in
  ( Cpp_ir.Map.template_parameters (Cpp_ir.Map.make ~expr:Fun.id ~stmt:Fun.id ~type_:deapplied ()) temps,
    Head_relaxation.Deapplied {plain; in_scope} )

(** [decl] under the head [temps], its plain variables deapplied
    ({!deapplied_head}). *)
let deapply_plain_tvars temps decl = Head_relaxation.apply (snd (deapplied_head temps)) decl

(** {!deapply_plain_tvars} for a generated struct in CppIR -- an
    inductive's, or an instance's -- whose template parameters are its own. *)
let deapply_plain_struct_tvars (decl : Cpp_ir.Lowered.Decl.t) =
  let rec tparams : Cpp_ir.Lowered.Decl.t -> _ = function
    | Struct s -> Some s.type_params
    | Template (temps, _, _) -> Some temps
    | Namespace (_, ds) -> List.find_map tparams ds
    | _ -> None
  in
  match tparams decl with
  | Some temps ->
    let plain =
      List.filter_map
        (fun ((k : Cpp_ir.Lowered.phase Cpp_ir.Template.Parameter_kind.t), id) ->
          match k with Template _ -> None | _ -> Some id )
        temps
    in
    Head_relaxation.deapply_struct ~plain ~in_scope:(List.map snd temps) decl
  | None -> decl

(** Whether a callable parameter's declared constraint states nothing the
    caller can be held to, and so is dropped rather than printed.

    A rank-2 callback has no result to claim: the body applies it at a type of
    its own choosing, and the [std::any] standing in for that type is not what
    comes back -- a handler for [forall X, E X -> M X] returns [M nat] where the
    constraint would demand [M std::any].  The result is recovered where it is
    used, by {!relax_tt_applied_return} or by the deduction the call itself
    performs.  A dropped clause is no use of the variables it names. *)
let constraint_is_vacuous (dom : head_type list) (cod : head_type) =
  List.exists
    (fun t -> head_type_exists (function Any | Obligation Opaque_type -> true | _ -> false) t)
    (cod :: List.filter (function (Function _ : head_type) -> true | _ -> false) dom)

(** Default every template parameter the signature that came out of the
    relaxations no longer mentions.

    A relaxation answers a template parameter the call site cannot supply by
    spelling the position it appeared in differently -- a callback becomes an
    [F], an application becomes a parameter of its own.  What it leaves behind
    is the variable itself: declared, mentioned nowhere, and so neither
    deducible nor, for a [template <typename> class], writable at all.  Given
    a [void] default it costs the call site nothing.  It is defaulted rather
    than dropped because a call site that spells template arguments spells
    them by position.

    A constraint counts as a mention, including a callback's.  It is not a use
    the compiler can deduce from, but it is what states the arity and result a
    callback must have, and a call site that spells its type arguments -- which
    is the only way such a parameter is ever given a value -- is relying on it
    to reject the ones that do not fit.  Defaulting the variable away would
    take the check with it.  A clause the printer drops as vacuous is not a
    mention, for the same reason: it is not there.

    Only the signature is read, and what the reading skips it also rewrites.
    A mention is counted in the arguments a type actually writes, so an
    occurrence sitting where nothing is written does not save the variable --
    and must not survive it either, or the declaration would default a
    parameter it goes on to spell.  Those occurrences are erased to [std::any].

    The body's occurrences go the same way, with one exception: the target
    type of an [any_cast].  Everywhere else an erased spelling is a vaguer
    spelling of the same thing, and vaguer is what the variable has become.
    An [any_cast] target is not a spelling but a run-time equality test
    against the type the value was stored as, so erasing an argument inside
    one does not widen the cast, it changes which cast is performed:
    [std::pair<std::any, nat>] read of a pair stored with concrete components
    throws, while compiling perfectly clean.  The defaulted parameter is still
    declared, and a call site that knows what the value was stored as writes
    it -- which is the only way such a parameter is ever given a value, and
    the reason it is defaulted rather than dropped. *)
let default_unmentioned_temps (temps : head_params) (signature : Callable_abi.signature) =
  (* Stricter than {!head_tvar_is}, which lets an unresolved head answer to its
     index as well as to its name: a relaxation names its parameters [F1],
     [_P0] without renumbering them, so a variable that kept index 1 would
     otherwise answer for [T1] and no parameter would ever look unmentioned. *)
  let is_tvar id : head_type -> bool = function
    | Variable (Index (_, Some n) | Named n) -> Id.equal n id
    | Variable (Index (i, None)) -> Id.equal (Common.tvar_id i) id
    | _ -> false
  in
  (* Only the arguments a type actually writes count: an argument in a
     position nothing writes is no more deducible than one that is not there. *)
  let prune = Ml_type_util.prune_unwritten_args_ir in
  let has_tvar id ty = head_type_exists (is_tvar id) (prune ty) in
  let mentions id =
    let has = has_tvar id in
    (* A constraint on another parameter is a mention too: dropping the
       variable out of the deduction would leave the clause naming it. *)
    let in_temps =
      List.exists
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), _) ->
          match tt with
          | Typename_default d -> has d
          | Concept (_, args) -> List.exists has args
          | Callable_declared (dom, cod) ->
            (not (constraint_is_vacuous dom cod))
            && (List.exists has dom || has cod)
          | _ -> false )
        temps
    in
    has signature.ret || in_temps || List.exists has signature.params
  in
  let unmentioned =
    List.filter_map
      (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) ->
        match tt with
        | (Typename | Template _) when not (mentions id) -> Some id
        | _ -> None )
      temps
  in
  if unmentioned = [] then (temps, None)
  else
    let temps : head_params =
      List.map
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) ->
          match tt with
          | (Typename | Template _) when List.exists (Id.equal id) unmentioned
            ->
            (Cpp_ir.Template.Parameter_kind.Typename_default Void, id)
          | _ -> (tt, id) )
        temps
    in
    (temps, Some (Head_relaxation.Unmentioned unmentioned))

(** [apply_signature r s] -- the signature [s] as the relaxation [r]
    rewrites it ({!Head_relaxation.apply_signature}). *)
let apply_signature r ({params; ret} : Callable_abi.signature) : Callable_abi.signature =
  let params, ret = Head_relaxation.apply_signature r ~params ~ret in
  {params; ret}

(** A function's head, relaxed: what the relaxations above decide from the
    head [temps] and the declared [signature], the signature they leave, and
    the rewrites that carry their decisions through the declaration, its
    body included ({!Head_relaxation.apply}).  Each relaxation decides from
    the signature the previous ones left, in order:
    {!relax_applied_return}, {!relax_tt_applied_return},
    {!relax_applied_param}, {!deapplied_head}, {!default_unmentioned_temps}. *)
let relax_function_head (temps : head_params) (signature : Callable_abi.signature) =
  let temps, signature, relaxations =
    List.fold_left
      (fun (temps, signature, relaxations) relax ->
        match relax temps signature with
        | temps, None -> (temps, signature, relaxations)
        | temps, Some r -> (temps, apply_signature r signature, relaxations @ [r]) )
      (temps, signature, [])
      [ relax_applied_return;
        relax_tt_applied_return;
        relax_applied_param;
        (fun temps _ -> let temps, r = deapplied_head temps in (temps, Some r));
        default_unmentioned_temps ]
  in
  (temps, signature, relaxations)

(** Build template parameter list with phantom detection.

    Type variables represented concretely in the generated signature (i.e.
    {!Ml_type_util.primary_tvar_indices}) are emitted as plain [typename T].
    All others (phantom tvars from erased HKT positions or custom-template
    positions that the C++ compiler cannot deduce) are emitted with a [void]
    default ([typename T = void]), except the leading run every call site
    spells out ({!Ml_type_util.explicit_tvar_prefix}), which stays required.
    Applied variables then become template template parameters
    ({!with_applied_tvars}).

    We never {i remove} tvars from the list: only default them.  Removing
    would shift the de Bruijn index-to-name mapping used throughout the
    pipeline (see {!Translation.convert_ml_type_to_cpp_type}).

    @param force_required  Set of tvar indices that must be required (plain
      [typename T]) even if they don't appear in the C++ function type.
      Used for type INDEX tvars that are stripped from the C++ type but needed
      for [any_cast] in function bodies.
    @param also_declared  Set of tvar indices the ML type has but the C++
      type may not spell; each is declared, as a defaulted phantom unless
      it is primary.
    @param ml_ty  The ML type of the declaration, passed to
      {!with_applied_tvars} to veto higher kinds it does not demand. *)
let phantom_aware_temps
    ?(force_required = IntSet.empty) ?(also_declared = IntSet.empty) ?ml_ty (cty : head_type)
    tvars : head_params =
  (* The leading phantoms are spelled out at every call site
     ({!Ml_type_util.explicit_tvar_prefix}), so they need no default.  A
     default there would let a call that supplies nothing silently pick
     [void] instead of failing to compile. *)
  let undefault n (temps : head_params) : head_params =
    List.mapi
      (fun i ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) ->
        match tt with
        | Typename_default Void when i < n -> (Cpp_ir.Template.Parameter_kind.Typename, id)
        | _ -> (tt, id) )
      temps
  in
  undefault (explicit_tvar_prefix_ir ~force_required cty)
  @@ with_applied_tvars ?ml_ty cty
  @@
  match cty with
  | Function (dom, cod) ->
    let tvars_indexed = get_tvars_indexed_ir cty in
    let primary = primary_tvar_indices_ir dom cod in
    let primary = IntSet.union primary force_required in
    (* [also_declared] is every variable the ML type has, which is not every
       variable the C++ type spells: an erased one is written nowhere in the
       signature, yet the body and the call sites still number their arguments
       by the ML type.  Declared as a defaulted phantom, the numbering lines up
       and nothing is demanded of a use site that supplies nothing. *)
    let extra =
      IntSet.fold (fun i acc ->
        if List.exists (fun (j, _) -> j = i) tvars_indexed then acc
        else (i, Common.tvar_id i) :: acc
      ) (IntSet.union force_required also_declared) []
    in
    let all_tvars_indexed =
      List.sort (fun (x, _) (y, _) -> Int.compare x y)
        (tvars_indexed @ extra)
    in
    List.map
      (fun (i, id) ->
        if IntSet.mem i primary then
          (Cpp_ir.Template.Parameter_kind.Typename, id)
        else
          (Typename_default Void, id) )
      all_tvars_indexed
  | _ -> List.map (fun id -> (Cpp_ir.Template.Parameter_kind.Typename, id)) tvars
