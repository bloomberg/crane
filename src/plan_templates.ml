(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The template heads of generated declarations: which parameters are
    template-template parameters and at what arity, which applications a
    head takes back off, which defaults a parameter no signature mentions
    gets, and which parameters are phantom.  Decided while a declaration is
    generated, from its types; {!Gen_decls} asks, and the printer writes what
    the head says. *)

open Miniml
open Minicpp
open Names
open Util
open Ml_type_util

(** Arity of every type variable that [cty] applies to arguments, keyed by
    template parameter name.  A Rocq parameter of kind [Type -> Type] reaches
    C++ as the head of a {!Tapply}, and a plain [typename] cannot be applied,
    so such a parameter has to be declared [template <typename> class]. *)
let applied_tvar_arities cty =
  let arities = Hashtbl.create 4 in
  exists_cpp_type
    (fun t ->
      ( match t with
      | Tapply (Tvar (Tv_named n), args) ->
        Hashtbl.replace arities n (List.length args)
      | Tapply (Tvar (Tv_index (i, name)), args) ->
        (* The head may or may not have been resolved to its parameter name;
           key on both spellings so the caller's list matches either way. *)
        let arity = List.length args in
        Option.iter (fun n -> Hashtbl.replace arities n arity) name;
        Hashtbl.replace arities (tvar_id i) arity
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
let with_applied_tvars ?ml_ty cty temps =
  let arities = applied_tvar_arities cty in
  let arities =
    match ml_ty with
    | None -> arities
    | Some ty ->
      let hk = Ml_type_util.higher_kinded_ml_tvars [ty] in
      let veto = ref [] in
      exists_cpp_type
        (fun t ->
          ( match t with
          | Tapply (Tvar (Tv_index (i, name)), _) when not (IntSet.mem i hk) ->
            veto := tvar_id i :: !veto;
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
        (fun (i, arity) -> Hashtbl.replace arities (tvar_id i) arity)
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
        match (tt, Hashtbl.find_opt arities id) with
        | (TTtypename | TTtypename_default Tvoid), Some arity ->
          (TTtemplate arity, id)
        | _ -> (tt, id) )
      temps

(** Template parameter list for a declaration whose parameters [vars] are used
    by the types [tys] -- an inductive's constructor fields, or the body of a
    type alias.  The arities are read off the ML types rather than the
    converted C++ ones because the parameter list has to be fixed before the
    types are converted.  Registers the template template positions so that
    {e uses} of [r] pass a bare template name; see {!Table.is_hkt_ind_param}. *)
let hkt_templates ?applied r vars tys =
  (* Read from the rendered type where there is one: the ML body still applies
     a variable that erasure removed, and the parameter list has to agree with
     what the users of this name can see.  See
     {!Ml_type_util.rendered_tvar_arities}. *)
  let arities =
    match applied with
    | Some a ->
      (* The alias's own rendering, under the same rule as an inductive's
         payloads below: applied only at erased or variable arguments --
         [IFun E F := forall T, E T -> F T], whose [T] erases -- is a family,
         and a family is a plain parameter. *)
      let arities = Ml_type_util.rendered_tvar_arities a in
      let demanded = Hashtbl.create 4 in
      let rec scan = function
        | Tapply (Tvar (Tv_index (i, _)), tys) ->
          if
            List.exists
              (fun t ->
                not (prints_as_any t || match t with Tvar _ -> true | _ -> false) )
              tys
          then Hashtbl.replace demanded i ();
          List.iter scan tys
        | Tglob (_, tys, _) | Tvariant (_, tys) -> List.iter scan tys
        | Tfun (tys, ty) -> List.iter scan (ty :: tys)
        | Tconst ty | Tnamespace (_, ty) | Tref (_, ty) | Tshared_ptr ty -> scan ty
        | Tapply (ty, tys) -> List.iter scan (ty :: tys)
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
        | Miniml.Tmeta {contents = None} -> false
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
  let rendered = Option.map Ml_type_util.get_rendered_tvar_indices applied in
  let rendered_in_cpp i =
    match rendered with None -> true | Some l -> List.mem i l
  in
  let temps =
    List.mapi
      (fun i n ->
        if not (rendered_in_cpp (i + 1)) then (TTtypename_default Tvoid, n)
        else
          match Hashtbl.find_opt arities (i + 1) with
          | Some arity -> (TTtemplate arity, n)
          | None -> (TTtypename, n) )
      vars
  in
  (* A default may only stand in the trailing run of defaulted parameters:
     [template <typename obj = void, typename c>] does not parse.  A phantom
     followed by a required parameter stays phantom -- no use writes an
     instantiation in it -- but has to be written, so it loses its default. *)
  let temps =
    let rec go = function
      | [] -> ([], true)
      | (tt, n) :: rest ->
        let rest, all_defaulted = go rest in
        ( match tt with
        | TTtypename_default _ when not all_defaulted -> (TTtypename, n) :: rest
        | TTtypename_default _ -> (tt, n) :: rest
        | _ -> (tt, n) :: rest ),
        all_defaulted
        && (match tt with TTtypename_default _ -> true | _ -> false)
    in
    fst (go temps)
  in
  let positions_of p =
    List.filteri (fun i _ -> p i) (List.mapi (fun i _ -> i) temps)
  in
  Table.add_hkt_ind_params r
    (List.filter_map
       (fun i ->
         match List.nth temps i with
         | TTtemplate arity, _ -> Some (i, arity)
         | _ -> None )
       (List.mapi (fun i _ -> i) temps) );
  Table.add_phantom_type_params r
    (positions_of (fun i -> not (rendered_in_cpp (i + 1))));
  (* Applied in the definition and still plain: a family position. *)
  let applied_at_all =
    match applied with
    | Some a -> Ml_type_util.rendered_tvar_arities a
    | None -> Ml_type_util.applied_ml_tvar_arities tys
  in
  Table.add_family_ind_params r
    (positions_of (fun i ->
         Hashtbl.mem applied_at_all (i + 1) && not (Hashtbl.mem arities (i + 1))));
  temps

(** Relax a signature whose return type applies a template template parameter
    (see {!with_applied_tvars}).  In [F B fn(G g, F A x)] the variable [B] is
    named only by the return type, and C++ deduces nothing from a return type,
    so the call is ill-formed as written.  [B] is however pinned by the
    signature of the callback [g] that produces it, so [B] is redeclared last
    with that result as its default ([typename B = std::invoke_result_t<G &,
    A &>]) -- last because a default may only name parameters declared before
    it, and the callback is one of those. *)
let relax_applied_return temps decl =
  (* Only a template template parameter is applied here: a family is a plain
     parameter, written applied until {!deapply_plain_tvars} takes the
     application off, and its return type deduces as any other. *)
  let hk =
    List.filter_map
      (fun (tt, id) -> match tt with TTtemplate _ -> Some id | _ -> None)
      temps
  in
  let applies_tvar t =
    exists_cpp_type
      (function
        | Tapply (head, _) -> List.exists (fun id -> tvar_is id head) hk
        | _ -> false )
      t
  in
  match decl with
  | Dfun {df_ret = cod0; df_shape = Ddef (params, _); _} when applies_tvar cod0 ->
    let is_tvar = tvar_is in
    let names = tvar_named in
    let undeducible id = not (List.exists (fun (_, ty) -> names id ty) params) in
    (* The result of the callback whose declared codomain is [id], spelled so
       that C++ can compute it from the callback's deduced type. *)
    let invoke_result id =
      List.find_map
        (fun (tt, fid) ->
          match tt with
          | TTfun (doms, cod) when is_tvar id cod ->
            Some
              (Tid_external
                 ( "std::invoke_result_t",
                   Tref (Lvalue, Tid_external (Id.to_string fid, []))
                   :: List.map (fun d -> Tref (Lvalue, d)) doms
                 ) )
          | _ -> None )
        temps
    in
    (* [id] is pinned by a callback rather than by an argument, so instead of
       naming it in the signature the declaration gives it that callback's
       result as its default and the return type keeps its own spelling.  The
       default names parameters declared after [id], so [id] moves to the end
       of the list; nothing supplies this signature's arguments explicitly, so
       the order is free. *)
    let computed =
      List.filter_map
        (fun (tt, id) ->
          match tt with
          | TTtypename when undeducible id ->
            Option.map (fun r -> (TTtypename_default r, id)) (invoke_result id)
          | _ -> None )
        temps
    in
    let temps =
      List.filter
        (fun (_, id) -> not (List.exists (fun (_, j) -> Id.equal id j) computed))
        temps
      @ computed
    in
    (temps, decl)
  | _ -> (temps, decl)

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
let relax_tt_applied_return temps decl =
  let kind_of id =
    List.find_map (fun (tt, i) -> if Id.equal i id then Some tt else None) temps
  in
  match decl with
  | Dfun ({df_ret = Tapply (head, [ret_arg]); df_shape = Ddef (params, _); _} as f)
    -> (
    match tvar_name head with
    | Some id
      when kind_of id = Some (TTtemplate 1)
           && not (List.exists (fun (_, ty) -> tvar_named id ty) params) ->
      (* The callback whose codomain is this application, and the argument it
         is applied to there -- [T3<std::any>], whose [std::any] stands for
         the [X] that the return type instantiates at [ret_arg]. *)
      let producer =
        List.find_map
          (fun (tt, fid) ->
            match tt with
            | TTfun (doms, Tapply (h, [carrier])) when tvar_is id h ->
              Some (fid, doms, carrier)
            | _ -> None )
          temps
      in
      ( match producer with
      | None -> (temps, decl)
      | Some (fid, doms, carrier) ->
        let at_ret_arg t =
          map_cpp_type (fun t -> if t = carrier then ret_arg else t) t
        in
        let ret =
          Tid_external
            ( "std::invoke_result_t",
              Tref (Lvalue, Tid_external (Id.to_string fid, []))
              :: List.map (fun d -> Tref (Lvalue, at_ret_arg d)) doms )
        in
        let temps =
          List.filter_map
            (fun (tt, i) ->
              match tt with
              | _ when Id.equal i id -> None
              | TTfun (doms, cod) when List.exists (tvar_named id) (cod :: doms)
                -> Some (TTtypename, i)
              | _ -> Some (tt, i) )
            temps
        in
        (temps, Dfun {f with df_ret = ret}) )
    | _ -> (temps, decl) )
  | _ -> (temps, decl)

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
let relax_applied_param temps decl =
  let occurrences p ty =
    let n = ref 0 in
    ignore (exists_cpp_type (fun t -> if p t then incr n; false) ty);
    !n
  in
  let applies id = function Tapply (h, _) -> tvar_is id h | _ -> false in
  match decl with
  | Dfun ({df_ret = ret; df_shape = Ddef (params, body); _} as f) ->
    let param_tys = List.map snd params in
    (* A variable applied in the parameters and named nowhere else: not by the
       return type, not by another template parameter's constraint, and not
       bare among the parameters either. *)
    (* A position that takes the variable as a bare template name --
       [Sum1<T1, T2, T4>], whose first two arguments are templates -- states
       its kind outright: what is supplied there {e is} a template, so the
       parameter cannot be relaxed into a [typename] deduced from an
       argument. *)
    let passed_as_template id =
      List.exists
        (exists_cpp_type (function Ttyctor t -> tvar_named id t | _ -> false))
        (ret :: param_tys)
    in
    let only_applied_in_params id =
      let total = List.fold_left (fun a t -> a + occurrences (tvar_is id) t) 0 in
      let applied =
        List.fold_left (fun a t -> a + occurrences (applies id) t) 0
      in
      applied param_tys > 0
      && total param_tys = applied param_tys
      && (not (passed_as_template id))
      && (not (tvar_named id ret))
      && not
           (List.exists
              (fun (tt, i) ->
                (not (Id.equal i id))
                &&
                match tt with
                | TTfun (doms, cod) -> List.exists (tvar_named id) (cod :: doms)
                | TTtypename_default d -> tvar_named id d
                | _ -> false )
              temps )
    in
    let relaxed =
      List.filter
        (fun (tt, id) ->
          match tt with
          | TTtemplate _ -> only_applied_in_params id
          | _ -> false )
        temps
    in
    if relaxed = [] then (temps, decl)
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
      let key t =
        match t with
        | Tapply (h, args) -> (
          match List.find_opt (fun (_, id) -> tvar_is id h) relaxed with
          | Some (_, id) -> Some (id, args)
          | None -> None )
        | _ -> None
      in
      let lookup t =
        Option.bind (key t) (fun k -> List.assoc_opt k !seen)
      in
      let deduced t =
        match key t with
        | None -> None
        | Some k -> (
          match List.assoc_opt k !seen with
          | Some id -> Some id
          | None ->
            let id = next_name () in
            fresh := !fresh @ [(TTtypename, id)];
            seen := (k, id) :: !seen;
            Some id )
      in
      let deduce ty =
        map_cpp_type
          (fun t ->
            match deduced t with Some id -> Tvar (Tv_named id) | None -> t )
          ty
      in
      let params = List.map (fun (n, ty) -> (n, deduce ty)) params in
      (* The body annotates the very types the parameters do -- a pattern
         match names the scrutinee's constructor struct -- so a relaxation
         that renames a parameter's type has to rename the body's too, or the
         body goes on applying a variable the signature no longer declares as
         a template. *)
      let body =
        let ft =
          map_cpp_type (fun t ->
              match lookup t with Some id -> Tvar (Tv_named id) | None -> t )
        in
        let rec fe e = Minicpp.map_expr fe fs ft e
        and fs st = Minicpp.map_stmt fe fs ft st in
        List.map fs body
      in
      let temps =
        List.map
          (fun (tt, id) ->
            if List.exists (fun (_, i) -> Id.equal i id) relaxed then
              (TTtypename, id)
            else (tt, id) )
          temps
        @ !fresh
      in
      (temps, Dfun {f with df_shape = Ddef (params, body)})
    end
  | _ -> (temps, decl)

(** Take the application back off a type variable that was left a plain
    [typename].

    A variable is declared [template <typename> class] only when the signature
    has to name it with no argument list ({!with_applied_tvars}).  When it does
    not, an occurrence like [T1<std::any>] is the application of a plain type
    to a type -- which does not parse -- and the honest spelling is [T1]: the
    index is erased, so the family applied at it is the event struct itself and
    there is nothing for the argument list to say.  Applied at an argument the
    declaration binds, it is [crane::rebind_t<T1, A>] ({!Minicpp.rebind_plain_var}):
    the variable may just as well be a type constructor given at its erased
    element, and then the argument is the element. *)
let deapply_plain_tvars temps decl =
  let plain =
    List.filter_map
      (fun (tt, id) -> match tt with TTtemplate _ -> None | _ -> Some id)
      temps
  in
  let in_scope = List.map snd temps in
  let rec ft t =
    map_cpp_type
      (function
        | Tapply (head, args) when List.exists (fun id -> tvar_is id head) plain -> (
          (* Named as it is declared: a head converted without names is
             otherwise spelled [std::any]. *)
          let head =
            match head with
            | Tvar (Tv_index (i, None)) ->
              Tvar (Tv_index (i, List.find_opt (fun id -> tvar_is id head) plain))
            | _ -> head
          in
          Minicpp.rebind_plain_var ~in_scope head args )
        (* A carrier abstraction's body is written too, through a holder;
           [map_cpp_type] leaves it alone. *)
        | Ttyctor body -> Ttyctor (ft body)
        | t -> t )
      t
  in
  (* A lambda whose parameter deduced a template parameter only through the
     application just taken off no longer does. *)
  let settle = function
    | CPPlambda l -> CPPlambda (Minicpp.settle_lambda_tparams l)
    | e -> e
  in
  (* The parameters' own types too: a callable parameter's constraint
     ([is_invocable_r_v<T3, F1 &, T1<T2> &>]) and a default. *)
  let temps = Minicpp.map_tparams ft temps in
  match decl with
  | Dfun ({df_ret = ret; df_shape = Ddef (params, body); _} as f) ->
    let rec fe e = settle (Minicpp.map_expr fe fs ft e)
    and fs st = Minicpp.map_stmt fe fs ft st in
    ( temps,
      Dfun
        { f with
          df_ret = ft ret;
          df_shape =
            Ddef (List.map (fun (n, ty) -> (n, ft ty)) params, List.map fs body)
        } )
  | Dfun ({df_ret = ret; df_shape = Ddecl params; _} as f) ->
    ( temps,
      Dfun
        { f with
          df_ret = ft ret;
          df_shape = Ddecl (List.map (fun (n, ty) -> (n, ft ty)) params) } )
  | Dasgn (n, ty, e) ->
    let rec fe e = settle (Minicpp.map_expr fe fs ft e)
    and fs st = Minicpp.map_stmt fe fs ft st in
    (temps, Dasgn (n, ft ty, fe e))
  | Dstruct _ | Dnspace _ | Dtemplate _ ->
    (* An inductive's own fields and members, for the same reason: a family
       parameter [hkt_templates] left plain is applied in its payloads. *)
    let rec fe e = settle (Minicpp.map_expr fe fs ft e)
    and fs st = Minicpp.map_stmt fe fs ft st in
    (temps, Minicpp.map_decl fe fs ft decl)
  | _ -> (temps, decl)

(** {!deapply_plain_tvars} for a generated struct -- an inductive's, or an
    instance's -- whose template parameters are its own. *)
let deapply_plain_struct_tvars decl =
  let rec tparams = function
    | Dstruct ds -> Some ds.ds_tparams
    | Dtemplate (temps, _, _) -> Some temps
    | Dnspace (_, ds) -> List.find_map tparams ds
    | _ -> None
  in
  match tparams decl with
  | Some temps -> snd (deapply_plain_tvars temps decl)
  | None -> decl

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
let default_unmentioned_temps temps decl =
  (* Stricter than {!tvar_is}, which lets an unresolved head answer to its
     index as well as to its name: a relaxation names its parameters [F1],
     [_P0] without renumbering them, so a variable that kept index 1 would
     otherwise answer for [T1] and no parameter would ever look unmentioned. *)
  let is_tvar id = function
    | Tvar (Tv_index (_, Some n) | Tv_named n) -> Id.equal n id
    | Tvar (Tv_index (i, None)) -> Id.equal (tvar_id i) id
    | _ -> false
  in
  (* Only the arguments a type actually writes count: an argument in a
     position nothing writes is no more deducible than one that is not there. *)
  let prune = Ml_type_util.prune_unwritten_args in
  let has_tvar id ty = exists_cpp_type (is_tvar id) (prune ty) in
  let mentions id =
    let has = has_tvar id in
    (* A constraint on another parameter is a mention too: dropping the
       variable out of the deduction would leave the clause naming it. *)
    let in_temps =
      List.exists
        (fun (tt, _) ->
          match tt with
          | TTtypename_default d -> has d
          | TTconcept (_, args) -> List.exists has args
          | TTfun (dom, cod) ->
            (not (Minicpp.tt_constraint_is_vacuous dom cod))
            && (List.exists has dom || has cod)
          | _ -> false )
        temps
    in
    match decl with
    | Dfun {df_ret; df_shape} ->
      has df_ret || in_temps
      || ( match df_shape with
         | Ddef (params, _) -> List.exists (fun (_, t) -> has t) params
         | Ddecl params -> List.exists (fun (_, t) -> has t) params )
    | _ -> true
  in
  let unmentioned =
    List.filter_map
      (fun (tt, id) ->
        match tt with
        | (TTtypename | TTtemplate _) when not (mentions id) -> Some id
        | _ -> None )
      temps
  in
  if unmentioned = [] then (temps, decl)
  else
    let is_unmentioned t =
      let head = match t with Ttyctor h | Tapply (h, _) -> h | h -> h in
      List.exists (fun id -> is_tvar id head) unmentioned
    in
    let erase = map_cpp_type (fun t -> if is_unmentioned t then Tany else t) in
    let erase_params l = List.map (fun (id, t) -> (id, erase t)) l in
    let decl =
      match decl with
      | Dfun ({df_shape; _} as f) ->
        let df_shape =
          match df_shape with
          | Ddef (params, body) ->
            let rec fe e =
              match e with
              (* The cast's target is left alone; its operand is not. *)
              | CPPany_cast (ty, e') -> CPPany_cast (ty, fe e')
              | CPPany_cast_tolerant (ty, e') -> CPPany_cast_tolerant (ty, fe e')
              | e -> Minicpp.map_expr fe fs erase e
            and fs s = Minicpp.map_stmt fe fs erase s in
            Ddef (erase_params params, List.map fs body)
          | Ddecl params -> Ddecl (erase_params params)
        in
        Dfun {f with df_ret = erase f.df_ret; df_shape}
      | d -> d
    in
    let temps =
      List.map
        (fun (tt, id) ->
          match tt with
          | (TTtypename | TTtemplate _) when List.exists (Id.equal id) unmentioned
            ->
            (TTtypename_default Tvoid, id)
          | _ -> (tt, id) )
        temps
    in
    (temps, decl)

(** Build template parameter list with phantom detection.

    Type variables represented concretely in the generated signature (i.e.
    {!primary_tvar_indices}) are emitted as plain [typename T].  All others —
    phantom tvars from erased HKT positions or custom-template positions that
    the C++ compiler cannot deduce — are emitted with a [void] default
    ([typename T = void]).

    We never {i remove} tvars from the list: only default them.  Removing
    would shift the de Bruijn index-to-name mapping used throughout the
    pipeline (see {!convert_ml_type_to_cpp_type}).

    @param force_required  Set of tvar indices that must be required (plain
      [typename T]) even if they don't appear in the C++ function type.
      Used for type INDEX tvars that are stripped from the C++ type but needed
      for [any_cast] in function bodies. *)
let phantom_aware_temps
    ?(force_required = IntSet.empty) ?(also_declared = IntSet.empty) ?ml_ty cty
    tvars =
  (* The leading phantoms are spelled out at every call site
     ({!Ml_type_util.explicit_tvar_prefix}), so they need no default.  A
     default there would let a call that supplies nothing silently pick
     [void] instead of failing to compile. *)
  let undefault n temps =
    List.mapi
      (fun i (tt, id) ->
        match tt with
        | TTtypename_default Tvoid when i < n -> (TTtypename, id)
        | _ -> (tt, id) )
      temps
  in
  undefault (explicit_tvar_prefix ~force_required cty)
  @@ with_applied_tvars ?ml_ty cty
  @@
  match cty with
  | Tfun (dom, cod) ->
    let tvars_indexed = get_tvars_indexed cty in
    let primary = primary_tvar_indices dom cod in
    let primary = IntSet.union primary force_required in
    (* [also_declared] is every variable the ML type has, which is not every
       variable the C++ type spells: an erased one is written nowhere in the
       signature, yet the body and the call sites still number their arguments
       by the ML type.  Declared as a defaulted phantom, the numbering lines up
       and nothing is demanded of a use site that supplies nothing. *)
    let extra =
      IntSet.fold (fun i acc ->
        if List.exists (fun (j, _) -> j = i) tvars_indexed then acc
        else (i, tvar_id i) :: acc
      ) (IntSet.union force_required also_declared) []
    in
    let all_tvars_indexed =
      List.sort (fun (x, _) (y, _) -> Int.compare x y)
        (tvars_indexed @ extra)
    in
    List.map
      (fun (i, id) ->
        if IntSet.mem i primary then
          (TTtypename, id)
        else
          (TTtypename_default Tvoid, id) )
      all_tvars_indexed
  | _ -> List.map (fun id -> (TTtypename, id)) tvars
