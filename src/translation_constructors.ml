(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Where each value argument of a constructor is generated: the C++ type
    it is generated against and the slot it fills, decided from the
    constructor, its annotation and the position it is built at.
    {!Translation.gen_expr} lowers a constructor by these, and
    {!Position_plan} plans the coercions it stores by them. *)

open Common
open Miniml
open Minicpp
open Names
open Util
open Translation_state
open Ml_type_util
open Translation_support
open Translation_types
open Core_query

(** [slot], noting that a constructor built here goes straight into an erased
    ([std::any]) result -- the enclosing function's C++ return type is opaque,
    as for a definition whose return type is value-dependent.  The value must
    then use the canonical erased shape: a consumer of such a slot recovers it
    with a fixed [any_cast] and cannot know the concrete type arguments.  That
    is the requirement a [Boxed] slot expresses for a value flowing into an
    erased field or parameter, and it holds for a mapped constructor
    ([std::make_optional<std::any>]) as for one of Crane's own. *)
let into_erased_return slot =
  match Option.map slot_repr_of_cpp_type (current_cpp_return_type ()) with
  | Some (Boxed kind) -> into_box kind slot
  | Some Native | None -> slot

(** [refined_by_slot slot ty]: the annotation carries this producer's own instantiation, and a stored
   closure whose arrows extraction never unified leaves it erased -- a
   [rose (option (nat -> nat))] node is annotated at
   [rose<optional<function<any(any)>>>] while the consumer names the
   concrete one.  Where the position states the same inductive, its
   arguments are the ones both sides agree on, so take them for the
   positions the annotation erased.  Not in a [Boxed] slot: there the
   erased instantiation {i is} the canonical one. *)
let refined_by_slot slot (ty : ml_type) =
  match (resolve_tmeta ty, Option.map resolve_tmeta slot.expected_ml_ty) with
  | Miniml.Tglob (n, tys, sc), Some (Miniml.Tglob (n', exp_tys, _))
    when (not (boxed slot))
         && globref_equal n n'
         && List.length tys = List.length exp_tys
         && List.exists (ml_type_contains_erased ~in_arrows:true) tys ->
    Miniml.Tglob
      ( n,
        List.map2
          (fun local outer ->
            if ml_type_contains_erased ~in_arrows:true local then outer
            else local )
          tys exp_tys,
        sc )
  | _ -> ty

(** [list_propagated_args ty ts] -- the arguments [ts] of a list constructor
    of type [ty], each nested constructor of the same list at the element
    type the arguments resolve, so that the nested [nil] of
    [cons(1, cons(2, nil))] is a [List<nat>], not a [List<std::any>]; any
    other constructor's, unchanged. *)
let list_propagated_args (ty : ml_type) ts =
  match ty with
  | Tglob (n, tys_orig, schema_opt) ->
    (* Only run type propagation for list constructors *)
    let is_list =
      try String.equal (Common.pp_global_name Type n) "list"
      with _ -> false
    in
    if not is_list then
      ts
    else (* Filter out index type args - only keep parameters *)
      let tys_filt =
        match n with
        | GlobRef.IndRef (kn, _) ->
          ( match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars -> safe_firstn num_param_vars tys_orig
          | None -> tys_orig )
        | _ -> tys_orig
      in
      (* Resolve Tunresolved from element types *)
      let has_unknown =
        List.exists
          (fun (t : ml_type) ->
            match t with
            | Tunknown -> true
            | _ -> false )
          tys_filt
      in
      if
        has_unknown
        &&
        match ts with
        | [] -> false
        | _ -> true
      then
        let tys_resolved =
          List.map
            (fun (t : ml_type) ->
              match t with
              | Tunknown ->
                let first_elem =
                  List.find_opt
                    (fun a ->
                      match a with
                      | MLdummy _ -> false
                      | _ -> true )
                    ts
                in
                ( match first_elem with
                | Some (MLmagic (_, MLcons (elem_ty, _, _, _), _)) -> elem_ty
                | Some (MLcons (elem_ty, _, _, _)) -> elem_ty
                | _ -> t )
              | _ -> t )
            tys_filt
        in
        (* Propagate resolved type to nested constructors *)
        let resolved_ty = Miniml.Tglob (n, tys_resolved, schema_opt) in
        let rec update_nested_ty ast =
          match ast with
          | MLcons (arg_typ, arg_c, arg_ts, arg_occ) ->
            ( match arg_typ with
            | Miniml.Tglob (arg_ref, arg_tys, _)
              when GlobRef.CanOrd.equal arg_ref n
                   && List.exists
                        (fun t ->
                          match t with
                          | Miniml.Tunknown -> true
                          | _ -> false )
                        arg_tys ->
              MLcons (resolved_ty, arg_c, List.map update_nested_ty arg_ts, arg_occ)
            | _ ->
              MLcons (arg_typ, arg_c, List.map update_nested_ty arg_ts, arg_occ) )
          | MLmagic (m, inner, mocc) -> MLmagic (m, update_nested_ty inner, mocc)
          | other -> other
        in
        List.map update_nested_ty ts
      else
        ts
  | _ -> ts

(** [temps_from_slot env ~expected_ty ind temps]: where the position
   ([expected_ty], else the return type in force) already spells [ind], it -- not the
   constructor's own type annotation -- says how the type arguments are
   written.  An element type that reached the slot through one of the
   callee's type variables keeps the currying the declaration wrote it
   at: once a function type has been substituted for a type variable,
   its arrows are indistinguishable from the callee's own, so converting
   the annotation cannot recover the shape. *)
(* Refine, never respell.  The position says what an argument the
   annotation left erased is -- and equally what one it erased too
   deeply is, since two producers for one declared field must agree
   about which of its arguments are [std::any].  What it may not do is
   overrule a concrete argument with a different concrete one: inside a
   bind's action the expected type is the enclosing declaration's
   result, not the action's, and a constructor whose type parameter none
   of its arguments constrains would then be built at [EOU<Dv>] where
   the action is an [EOU<bool>].

   Currying is not a respelling: an element type that reached the slot
   through one of the callee's type variables keeps the arity the
   declaration wrote it at, which converting the annotation cannot know
   -- the arrows of a function substituted into a type variable are
   indistinguishable from the callee's own.  Two spellings that curry
   to the same type are therefore one type, and the position's is the
   one a template argument position requires.  So is an alias and what
   it expands to: the position names [List<entry<T1>>] where the
   annotation has the pair behind it, and the name is what the
   declaration wrote. *)
let temps_from_slot env ~expected_ty ind temps =
  let erased_anywhere = exists_cpp_type prints_as_any in
  (* With no slot of its own, a constructor is the value the enclosing
     function returns, as Step 2b below reads it -- [go (RetF x)] in
     [trigger]'s continuation, whose family its annotation erased --
     and only an erased position is ever taken from it. *)
  let slot_ty =
    match expected_ty with
    | Some _ -> expected_ty
    | None -> (
      match current_cpp_return_type () with
      | Some (Tshared_ptr t) -> Some t
      | t -> t )
  in
  match
    Option.map
      (fun t -> unfold_cpp_typedef env (Ml_type_util.unqualify_ty t))
      slot_ty
  with
  | Some (Tglob (ind', args, _))
    when globref_equal ind' ind && List.length args = List.length temps ->
    List.map2
      (fun local outer ->
        (* Compared after unfolding throughout, not only at the head:
           the same type is written [entry<T1>] in one place and the
           pair behind it in the other, and one of the two spellings
           carries the namespace the declaration is read in. *)
        let rec expand t =
          let t' =
            match unfold_cpp_typedef env t with
            | Tnamespace (_, inner) -> inner
            | t' -> t'
          in
          if t' = t then t else expand t'
        in
        let norm t = map_cpp_type expand t in
        let same_type a b =
          same_arrows (norm a) (norm b)
        in
        if
          erased_anywhere local || erased_anywhere outer
          || same_type local outer
        then outer
        else local )
      temps args
  | _ -> temps

(** [erase_past_type_arg ts temps]: in dependent types, if a constructor arg [ts] at position i is
   [MLdummy Ktype] (a type-valued argument — e.g. [x : A] where
   [A : Type]), any template param at a later position j > i must
   also be erased to [std::any].
   Rationale: later params often have types that are functions of
   the erased type variable (e.g. [P x] for [sigT A P]).  When A
   is erased, [P x] is equally abstract and the concrete type
   inferred from the value argument (e.g. [bool] from [true : bool])
   would produce an incompatible template instantiation
   ([SigT<std::any, Bool0>] vs. the declared
   [SigT<std::any, List<std::any>>]).  {!index_erase_type} is the
   same erasure the type side applies to those positions in
   {!convert_ml_type_to_cpp_type}, so the two agree by construction. *)
let erase_past_type_arg ts_updated temps =
  let rec first_ktype_dummy i = function
    | [] -> max_int
    | (MLdummy Ktype | MLmagic (_, MLdummy Ktype, _)) :: _ -> i
    | _ :: rest -> first_ktype_dummy (i + 1) rest
  in
  let cutoff = first_ktype_dummy 0 ts_updated in
  List.mapi (fun i t -> if i > cutoff then index_erase_type t else t) temps

(** A constructor of an inductive that is neither a record nor custom, as
    it is built: its annotation, refined by its slot ([rc_ty]); its
    arguments, with a nested list constructor at the element type they
    resolve ([rc_args]); the annotation's type arguments
    ([rc_ty_ml_tparams]); the C++ type arguments its fields are
    instantiated at ([rc_ctor_temps]); and its fields' declared types,
    erased ones dropped ([rc_field_types]). *)
type regular = {
  rc_ty : ml_type;
  rc_args : ml_ast list;
  rc_ty_ml_tparams : ml_type list;
  rc_ctor_temps : cpp_type list;
  rc_field_types : ml_type list;
}

(** [regular env ~expected_ty ty r ts] -- the constructor [r] of annotation
    [ty] ({!refined_by_slot}) applied to [ts], built at [expected_ty] under
    the return type in force. *)
let regular env ~expected_ty (ty : ml_type) r ts =
  let ts_updated = list_propagated_args ty ts in
  let temps_from_slot = temps_from_slot env ~expected_ty in
  let erase_past_type_arg = erase_past_type_arg ts_updated in
  let ty_ml_tparams = match resolve_tmeta ty with
    | Tglob (_, tys_orig, _) -> tys_orig
    | _ -> []
  in
  let ctor_temps = match ty with
    | Tglob (n, tys_orig, _) ->
      let tys_filt = match n with
        | GlobRef.IndRef (kn, _) ->
          ( match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars -> safe_firstn num_param_vars tys_orig
          | None -> tys_orig )
        | _ -> tys_orig
      in
      (* At the flat arity the constructor's own instantiation is written
         at: the fields are instantiated from these, and a tail built at a
         curried element type spells a list its head does not convert
         to. *)
      (* The fields are instantiated at the arguments the call is
         printed with, so a position the call erases is erased here too. *)
      let temps =
        erase_past_type_arg
          (temps_from_slot n (template_params_of_ml ~site:Declared env tys_filt))
      in
      if Table.has_dependent_params n then
        let expected_temps =
          expected_type_args_from_return env ?slot:expected_ty n
            ~arity:(List.length temps)
        in
        match expected_temps with
        | Some exp_tys ->
          List.mapi (fun i t ->
            let exp_t = normalize_erased_types (List.nth exp_tys i) in
            let is_fully_erased_fun = match exp_t with
              | Tfun (ps, r) ->
                List.for_all (fun p -> p = Tany) ps && r = Tany
              | _ -> false
            in
            if t <> exp_t && (prints_as_any exp_t || is_fully_erased_fun)
            then Tany
            else if t <> exp_t then exp_t
            else if is_fully_erased_fun then Tany
            else t
          ) temps
        | None -> temps
      else temps
    | _ -> []
  in
  let field_types_raw = match Table.get_ctor_ip_types_opt r with
    | Some ft -> ft
    | None -> [] in
  let field_types =
    List.filter (fun t -> not (Mlutil.isTdummy t)) field_types_raw in
  { rc_ty = ty; rc_args = ts_updated; rc_ty_ml_tparams = ty_ml_tparams; rc_ctor_temps = ctor_temps;
    rc_field_types = field_types }

(** [regular_field env ~is_boxed c ~slot i e] -- the C++ type the [i]th
    argument [e] of the constructor [c], built into [slot], is generated
    against, and the slot it fills.  [is_boxed i occ] says whether the read
    of the variable [i] at [occ] holds a box. *)
let regular_field env ~is_boxed c ~slot i e =
  let ty = c.rc_ty and ctor_temps = c.rc_ctor_temps and ty_ml_tparams = c.rc_ty_ml_tparams in
  let field_types = c.rc_field_types in
  let ft_opt = List.nth_opt field_types i in
  (* A constructor field with a CONCRETE type receiving an argument that
     is an erased ([std::any]) pattern variable (e.g. a leaf destructured
     from a deeply-erased [pair<any,any>] via [any_cast]) needs a final
     [any_cast<concrete>] — otherwise the bare [std::any] is forwarded
     straight into a concrete-typed factory parameter and fails to
     compile.  Thread the field's concrete C++ type as the expected type
     so the erased-[MLrel] path (see [gen_expr]'s [MLrel] case) inserts
     the cast.  [Tvar] fields are left to
     [wrap_if_needed_for_field], which handles the erased-field cases. *)
  (* The field's declared type with this constructor call's own type
     arguments substituted in — the [P] of [sigT A P] becomes the
     concrete C++ type the field holds at this call site. *)
  let instantiated_field_cpp_ty ft =
    subst_cpp_tvars
      (fun i -> if i >= 1 then List.nth_opt ctor_temps (i - 1) else None)
      (cpp_of_ml env ft)
  in
  let expected_for_arg =
    match ft_opt with
    | Some ft ->
      let is_erased_rel =
        match e with
        | MLrel (j, occ) | MLmagic (_, MLrel (j, occ), _) ->
          is_boxed j occ
        | _ -> false
      in
      ( match ft with
      | (Miniml.Tvar (_, _))
        when (match unfold_cpp_typedef env (instantiated_field_cpp_ty ft) with
              | Tglob (_, args, _) ->
                args <> [] && List.exists has_tany_in_type args
              | _ -> false) ->
        (* An element type the slot has already erased.  A nested
           constructor has to be built at that same instantiation --
           [SigT<any, any>], not [SigT<any, Nat>] -- or the value it
           produces does not convert into the container holding it. *)
        Some (unfold_cpp_typedef env (instantiated_field_cpp_ty ft))
      (* A boxed variable at a type-parameter field -- [Ret x] with [x]
         the erased existential of the continuation it is in -- is
         recovered at the field's instantiation. *)
      | Miniml.Tvar (_, _)
        when is_erased_rel
             && not (prints_as_any (instantiated_field_cpp_ty ft)) ->
        Some (instantiated_field_cpp_ty ft)
      (* A value constructed straight into a type-parameter field --
         [retf ((m, (ls, g')), r)] -- is spelled here for the first
         time, and the field's instantiation, where the destination
         wrote it in full, is the type to build it at: its own
         annotation may erase a class variable the field writes. *)
      | Miniml.Tvar (_, _)
        when (match strip_magic e with MLcons _ -> true | _ -> false)
             && (let ct = instantiated_field_cpp_ty ft in
                 (not (has_tany_in_type ct)) && names_only_scoped_tvars ct) ->
        Some (instantiated_field_cpp_ty ft)
      | Miniml.Tvar (_, _) -> None
      | Miniml.Tapp _ ->
        (* A field that applies one of the inductive's [template
           <typename> class] parameters ([F A]).  Nothing in the
           argument names the instantiation -- a [None] has no value to
           read it off -- so it can only come from this call's own type
           arguments.  The substitution is done on the ML type: only
           there does applying [option] to [nat] reduce, since the C++
           side of a custom-extracted [option] is a template string. *)
        let ct = cpp_of_ml env (Mlutil.type_subst_list ty_ml_tparams ft) in
        if prints_as_any ct || has_tany_in_type ct then None else Some ct
      | _ when is_erased_rel ->
        let ct = cpp_of_ml env ft in
        if prints_as_any ct then None else Some ct
      | Miniml.Tglob (g, _, _)
        when (match resolve_tmeta ty with
             | Miniml.Tglob (n_ind, _, _) -> globref_equal g n_ind
             | _ -> false)
             || ( match strip_magic e with
                | MLcons (_, GlobRef.ConstructRef ((kn, i), _), _, _) ->
                  globref_equal g (GlobRef.IndRef (kn, i))
                | _ -> false ) ->
        (* The recursive spine: every cell of a list is the same C++
           type, so the tail is built at the instantiation this cell
           was, not at the one its own annotation converts to.  So is
           a constructor built straight into a field of its own type
           -- [go (RetF r)] -- whose annotation may have lost an
           argument MiniML erases, a family, that the field states.
           A family variable is written applied at an erased index
           ([T1<std::any>], taken back off where it is declared
           plain), and that erasure is no reason to refuse the field:
           only an erased argument outside such an application is.
           The spine keeps its stricter test, which it was written
           with. *)
        let rec erased_outside_family_apps t =
          match t with
          | Tapply (Tvar _, _) -> false
          (* A family position holds the family's own struct, written
             at an erased index ([Sum1<AE, BE, std::any>]) by the same
             convention: only the family itself erased counts. *)
          | Tglob (fg, args, _) ->
            List.exists Fun.id
              (List.mapi
                 (fun i a ->
                   if Table.is_family_ind_param fg i then prints_as_any a
                   else erased_outside_family_apps a)
                 args)
          | Tapply (_, args) ->
            List.exists erased_outside_family_apps args
          | Tfun (ps, r) ->
            List.exists erased_outside_family_apps (r :: ps)
          | Tshared_ptr t | Tconst t | Tref (_, t) | Tnamespace (_, t) ->
            erased_outside_family_apps t
          | t -> prints_as_any t
        in
        (* A family position written as a family variable applied at
           the erased index ([T1<std::any>]) holds the variable itself,
           as the declaration spells it. *)
        let rec plain_families t =
          match t with
          | Tnamespace (n, t) -> Tnamespace (n, plain_families t)
          | Tglob (fg, args, ns) ->
            Tglob
              ( fg,
                List.mapi
                  (fun i a ->
                    if Table.is_family_ind_param fg i then
                      let rec unapply = function
                        | Tapply (h, _) -> unapply h
                        | Tnamespace (n, t) -> Tnamespace (n, unapply t)
                        | t -> t
                      in
                      unapply a
                    else plain_families a)
                  args,
                ns )
          | t -> t
        in
        let ct = plain_families (instantiated_field_cpp_ty ft) in
        let spine =
          match resolve_tmeta ty with
          | Miniml.Tglob (n_ind, _, _) -> globref_equal g n_ind
          | _ -> false
        in
        if (if spine then has_tany_in_type ct
            else erased_outside_family_apps ct)
        then None
        else Some ct
      | _ ->
        (* A field whose instantiated C++ type is a curried function
           (e.g. [A -> A] at [A = nat -> nat]) must keep its currying:
           without the expected type, [gen_expr]'s [MLlam] case would
           flatten the nested binders into one multi-parameter lambda,
           which does not convert to [std::function<F(F)>]. *)
        let ct = instantiated_field_cpp_ty ft in
        ( match (ft, ct) with
        | _, Tfun (_, Tfun _) when not (prints_as_any ct) -> Some ct
        (* A lambda built into a function-typed field -- [VisF]'s
           continuation -- is written against the field: its result
           is what the body's constructors are built at. *)
        | _, Tfun (_, cod)
          when (match strip_magic e with MLlam _ -> true | _ -> false)
               && not (prints_as_any cod) ->
          Some ct
        | _ -> (
          (* The same rule the bare-parameter case above states, for a
             field that names a type of its own: where the field's
             spelling erases some of its arguments and keeps others,
             that spelling is the only statement of which are which,
             and the value has to be built at it. *)
          let u = unfold_cpp_typedef env ct in
          match u with
          | Tglob (_, (_ :: _ as args), _)
            when List.exists prints_as_any args
                 && not (List.for_all prints_as_any args) ->
            Some u
          | _ -> None ) ) )
    | None -> None
  in
  (* When a function value is stored into an erased ([std::any])
     constructor field (e.g. the action [unit -> semty s] stored in a
     heterogeneous [sigT] list), the function's return value is, at
     runtime, boxed inside a single [std::any].  Consumers recover it
     with a fixed [any_cast] shape, so ALL of a given Coq type's
     producers must erase to the SAME canonical C++ representation.  For
     [list (nat*nat)] the empty ("nil") production erases to
     [deque<pair<any,any>>] (its element type is already opaque in the
     ML annotation), whereas a non-empty ("cons") production built from
     concrete pair values would otherwise stay [deque<Prod<Nat,Nat>>] --
     a different C++ type for the same Coq type, causing
     [std::bad_any_cast] at the consumer.  Generate the body with
     a [Boxed] slot so cons productions deep-erase their element
     type to match nil.  See the mirror in the record-constructor path. *)
  (* The same field type on the ML side.  A field's declared type says
     nothing on its own -- a bare parameter ([A]) or an applied one
     ([F A]) names the inductive's variables, not this value's types --
     but substituting the constructor's own type arguments turns it
     into the [option (nat -> nat)] the argument is actually built at,
     which is finer than the slot's expectation (that one states the
     whole inductive, not this field).  An applied parameter is taken
     unconditionally, as it always resolved that way; for any other
     field the substitution is only an improvement when it left neither
     erasure nor a stray type variable behind.  Otherwise the slot is
     the better guess, but only for a field of the inductive's own
     type -- the recursive spine, where the slot does state the field.
     Any other field is not what the slot states, and a constructor
     built in it would take the enclosing one's type for its own. *)
  let expected_ml_for_arg =
    match ft_opt with
    | Some ft -> (
      let inst = Mlutil.type_subst_list ty_ml_tparams ft in
      match ft with
      | Miniml.Tapp _ -> Some inst
      | _
        when (not (ml_type_contains_erased ~in_arrows:true inst))
             && not (Ml_type_util.ml_type_contains_tvar inst) ->
        Some inst
      | Miniml.Tglob (g, _, _)
        when ( match resolve_tmeta ty with
             | Miniml.Tglob (n_ind, _, _) -> globref_equal g n_ind
             | _ -> false ) ->
        slot.expected_ml_ty
      | _ -> None )
    | None -> slot.expected_ml_ty
  in
  let slot = { slot with expected_ml_ty = expected_ml_for_arg } in
  ( expected_for_arg,
    if field_stores_erased_fn_value ~field_cpp_ty:(Option.map instantiated_field_cpp_ty ft_opt) field_types i e
    then into_box Var_box slot
    else slot )

(** [record_promoted_map ty]: the promoted variables in scope, narrowed to
    the ones the record of annotation [ty] mentions.  A record struct erases
    the promoted variables it does not take as parameters to [std::any], so
    a lambda assigned to one of its fields has to spell them that way too,
    and the scope forgets how to resolve them; the ones it mentions are
    parameters of the struct ({!ind_promoted_type_args}), spelled resolved. *)
let record_promoted_map (ty : ml_type) =
  let mentioned =
    match ty with Tglob (n, _, _) -> Table.promoted_type_params n | _ -> []
  in
  List.filter (fun (v, _) -> List.exists (Id.equal v) mentioned) (!tctx).promoted_var_map

(** [record_field_types r]: the declared types of the fields of the record
    constructor [r]. A record's erased fields (a promoted [Type] field such as [dyn]'s
      [dty]) carry no argument, so the declared field types are aligned
      with the arguments only once the [Tdummy] entries are dropped --
      otherwise every field from the first erased one on is read off by
      the type of its predecessor. *)
let record_field_types r =
  match Table.get_ctor_ip_types_opt r with
  | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
  | None -> []

(** [record_declared_field_cpp_ty env ty ft]: the type the struct declares a field at: a record that renders no
   template parameter erases every type variable left in its field
   types (see [gen_ind_header_v2]), so that -- not the conversion that
   keeps the variable -- is the type an argument reaches the field
   at. *)
let record_declared_field_cpp_ty env (ty : ml_type) ft =
  let tvars = get_current_type_vars () in
  match ty with
  | Tglob ((GlobRef.IndRef (kn, _) as n), _, _) ->
    let t =
      convert_ml_type_to_cpp_type env ~ns:(Ref.User.Set.singleton n) tvars ft
    in
    if Table.get_ind_num_param_vars_opt kn = Some 0 then
      Ml_type_util.tvar_erase_type t
    else t
  | _ -> cpp_of_ml env ft

(** [record_field env ~is_boxed ty r ~slot i e]: the C++ type the [i]th
    field [e] of the record constructor [r] of annotation [ty], built into
    [slot], is generated against, and the slot it fills.  [is_boxed i occ]
    says whether the read of the variable [i] at [occ] holds a box. *)
let record_field env ~is_boxed (ty : ml_type) r ~slot i e =
  let field_types_rec = record_field_types r in
  let declared_field_cpp_ty = record_declared_field_cpp_ty env ty in
  (* A record field with a CONCRETE type receiving an argument that is an
     erased ([std::any]) pattern variable (e.g. a leaf destructured from a
     deeply-erased [pair<any,any>]) needs a final [any_cast<concrete>] —
     otherwise the bare [std::any] is aggregate-brace-initialized into a
     concrete field and fails to compile.  Thread the field's concrete C++
     type as the expected type so the erased-[MLrel] path (see [gen_expr]'s
     [MLrel] case) inserts the cast.  This mirrors the equivalent handling
     for value-type (variant) constructors in [gen_and_wrap]. *)
  let expected_for_field i e =
    match List.nth_opt field_types_rec i with
    | Some ft ->
      let is_erased_rel =
        match e with
        | MLrel (j, occ) | MLmagic (_, MLrel (j, occ), _) ->
          is_boxed j occ
        | _ -> false
      in
      ( match ft with
      | Miniml.Tvar (_, _) -> None
      | _ when is_erased_rel ->
        let ct = cpp_of_ml env ft in
        if prints_as_any ct then None else Some ct
      (* A lambda is split by the field's type, as one passed to a
         parameter is by the parameter's, where that type returns a
         function -- [nat -> pred nat] is the curried
         [crane::fn<pred<Nat>(Nat)>], an alias hiding the second arrow
         -- and [gen_expr]'s [MLlam] case would otherwise gather every
         binder into one lambda, which does not convert to it. *)
      | _ when (match strip_magic e with MLlam _ -> true | _ -> false) -> (
        let rec codomain = function
          | Tconst t | Tref (_, t) -> codomain t
          | Tfun (_, cod) -> Some cod
          | t -> (
            match unfold_cpp_typedef env t with
            | Tfun _ as f when f <> t -> codomain f
            | _ -> None )
        in
        match ty with
        | Miniml.Tglob (_, tys, _) -> (
          let ct = cpp_of_ml env (Mlutil.type_subst_list tys ft) in
          match codomain ct with
          | Some cod
            when Option.has_some (codomain cod) && (not (prints_as_any ct)) && names_only_scoped_tvars ct ->
            Some ct
          | _ -> None )
        | _ -> None )
      (* A call is the field's value: its result is the field's type at
         this record's arguments -- [tfmap f (g_exp g)] into [g_exp :
         option (exp T)] at an erased [T] is an
         [std::optional<exp<std::any>>], which fills the carrier a
         bare-variable codomain cannot. *)
      | _ when (match strip_magic e with MLapp _ -> true | _ -> false) -> (
        match ty with
        | Miniml.Tglob (_, tys, _) ->
          let ct = cpp_of_ml env (Mlutil.type_subst_list tys ft) in
          if prints_as_any ct || not (names_only_scoped_tvars ct) then None
          else Some ct
        | _ -> None )
      | _ -> None )
    | None -> None
  in
  (* A field the struct declares at an erased instantiation -- a
     [sigT] whose witness type the record erased, so
     [SigT<std::any, std::any>] -- accepts only a value built at that
     same instantiation.  Each producer would otherwise build its own
     ([SigT<std::any, List<std::any>>] for a list payload), which is a
     different C++ type and does not initialise the field.  Generating
     the argument in a [Boxed] slot boxes its components, so every
     producer arrives at the one shape the field is declared at. *)
  let field_declared_erased i =
    match List.nth_opt field_types_rec i with
    | Some ft -> (
      (* The alias has to come off first: [texp<std::any>] looks fully
         erased at its own one argument and is not -- the [std::pair] it
         stands for keeps a concrete second component. *)
      match
        Ml_type_util.unqualify_ty
          (unfold_cpp_typedef env (declared_field_cpp_ty ft))
      with
      | Tglob (_, (_ :: _ as args), _) as d
        when List.for_all
               (fun a ->
                 prints_as_any a || Ml_type_util.is_cpp_dummy_type a )
               args
             && List.exists prints_as_any args ->
        Some d
      | _ -> None )
    | None -> None
  in
  let arg_slot = {slot with in_ctor_arg = true} in
  ( (match expected_for_field i e with Some _ as t -> t | None -> field_declared_erased i),
    if field_stores_erased_fn_value ~field_cpp_ty:None field_types_rec i e then into_box Var_box arg_slot
    else arg_slot )

(** [custom_refined_annotation env ~expected_ty ~slot ty r ts]: the
    annotation [ty] of the custom constructor [r] applied to [ts], built at
    [expected_ty] into [slot], its type arguments recovered from the
    arguments, the slot and the position where the annotation leaves them
    unknown. *)
let custom_refined_annotation env ~expected_ty ~slot (ty : ml_type) r ts =
  (* Extraction leaves a type argument [Tunresolved] where it could not read the
     type off the term -- the element of [Some 1] passed at a parameter of an
     inductive that applies its own higher-kinded parameter ([F nat]).  The
     constructor's own field types say which type argument each value argument
     pins down, so recover it from the argument.  Left as [Tunresolved] the
     argument erases to [std::any], and the erased instantiation
     ([optional<std::any>]) does not match the field's declared one.

     Not when this value is itself being built into an erased slot: there the
     erased instantiation is the canonical one, and pinning the argument down
     is exactly what makes the consumer's fixed [any_cast] throw. *)
  let ty =
    match ty with
    | Miniml.Tglob (n, tys, sc)
      when List.exists (fun t -> t = Miniml.Tunknown) tys
           && (not (boxed slot))
           (* Nor when the destination is (or contains) [std::any]: there the
              erased shape is the canonical one every producer has to agree
              on, and grounding this one is what makes the consumer's fixed
              [any_cast] throw. *)
           && (not
                 ( match expected_ty with
                 | Some t -> has_tany_in_type (unfold_cpp_typedef env t)
                 | None -> false ))
           && not
                ( match current_cpp_return_type () with
                | Some t -> resolves_to_any_type t
                | None -> false ) ->
      let field_tys =
        match Table.get_ctor_ip_types_opt r with
        | Some l -> List.filter (fun t -> not (Mlutil.isTdummy t)) l
        | None -> []
      in
      let recovered = Array.of_list tys in
      List.iteri
        (fun i ft ->
          match (ft, List.nth_opt ts i) with
          | (Miniml.Tvar (_, k)), Some arg
            when k >= 1
                 && k <= Array.length recovered
                 && recovered.(k - 1) = Miniml.Tunknown ->
            ( match ml_ast_type_hint arg with
            | Some arg_ty -> recovered.(k - 1) <- arg_ty
            | None -> () )
          | _ -> () )
        field_tys;
      (* A nullary constructor ([None]) carries no argument to read the type
         off, so the only remaining witness is the slot it is being built
         into -- the field type of an enclosing constructor, instantiated. *)
      ( match Option.map resolve_tmeta slot.expected_ml_ty with
      | Some (Miniml.Tglob (exp_n, exp_tys, _))
        when GlobRef.CanOrd.equal n exp_n
             && List.length exp_tys >= Array.length recovered ->
        (* Aligned at the right: a type constructor that reached the slot
           partially applied ([F] at [F A]) keeps the placeholder arguments it
           was carrying in front of the ones applied to it. *)
        (* Only a type this scope can write is worth taking.  That is not the
           same as a ground one: [list (A * B)] in a declaration that binds
           [A] and [B] is as writable as [list nat], and refusing it leaves a
           nullary constructor at [list<pair<any, any>>] inside a function
           whose every neighbour spells [T1] and [T2].  What must be refused
           is a variable from {e another} scope -- a slot read off an
           abstract carrier ([m_carrier M]) -- which would not compile. *)
        let rec is_writable = function
          | Miniml.Tglob (_, args, _) -> List.for_all is_writable args
          | Miniml.Tarr (a, b) -> is_writable a && is_writable b
          | Miniml.Tmeta {contents = Some t} -> is_writable t
          | Miniml.Tvar (_, _) as t ->
            names_only_scoped_tvars (cpp_of_ml env t)
          | Miniml.Tapp _ | Miniml.Tunknown | Miniml.Tmeta {contents = None} | Miniml.Topen _ ->
            false
          | _ -> true
        in
        let m = Array.length recovered in
        List.iteri
          (fun i t ->
            let i = i - (List.length exp_tys - m) in
            if i >= 0 && recovered.(i) = Miniml.Tunknown && is_writable t then
              recovered.(i) <- t )
          exp_tys
      | _ -> () );
      Miniml.Tglob (n, Array.to_list recovered, sc)
    | _ -> ty
  in
  (* The same reading of the slot, but pointwise and at any depth.  A type
     argument the term never spells -- the element of a [nil] nested inside a
     pair -- arrives erased wherever it sits, while the position states the
     whole shape; the recovery above only looks at the constructor's own
     outermost arguments. *)
  let ty =
    if
      boxed slot
      || ( match expected_ty with
         | Some t -> has_tany_in_type (unfold_cpp_typedef env t)
         | None -> false )
    then ty
    else
      match slot.expected_ml_ty with
      | None -> ty
      | Some want ->
        Ml_type_util.refine_erased
          ~writable:(fun t -> names_only_scoped_tvars (cpp_of_ml env t))
          ty want
  in
  (* A position the term leaves unknown that the expected C++ type states as
     one of this scope's own variables -- [Some (tfmap f t)] returned at
     [std::optional<T1>] -- is that variable.  Only a variable: it is the one
     C++ type with an ML reading to take back. *)
  let ty =
    (* With no slot of its own, a constructor in a tail statement lands in
       the enclosing function's result ({!with_cpp_return_type}, as
       {!position_cpp_ty} reads it). *)
    let expected =
      match expected_ty with
      | Some _ -> expected_ty
      | None -> current_cpp_return_type ()
    in
    match (ty, Option.map (fun t -> Ml_type_util.unqualify_ty (unfold_cpp_typedef env t)) expected) with
    | Miniml.Tglob (n, tys, sc), Some (Tglob (n', etys, _))
      when GlobRef.CanOrd.equal n n' && List.length tys = List.length etys
           && (not (boxed slot)) ->
      Miniml.Tglob
        ( n,
          List.map2
            (fun t e ->
              match (resolve_tmeta t, e) with
              | (Miniml.Tunknown | Miniml.Tmeta {contents = None} | Miniml.Topen _),
                Tvar (Tv_index (i, _))
                when names_only_scoped_tvars e ->
                Miniml.Tvar (Miniml.Schematic, i)
              | _ -> t )
            tys etys,
          sc )
    | _ -> ty
  in
  ty

(** What a custom constructor's arguments are built at, past its
    annotation: the type arguments the fields are expected at
    ([cc_ty_args_for_expected]), its fields' declared types
    ([cc_field_types]), its C++ type arguments as the destination refines
    them ([cc_temps_at_slot]), whether the destination spells a position
    concretely ([cc_states_unboxed]), whether it is a custom list's cons
    ([cc_list_cons]), whether its value lands in a deeply erased slot
    ([cc_deeply_erased]), and whether an argument is forwarded verbatim
    ([cc_passthrough]). *)
type custom = {
  cc_ty_args_for_expected : ml_type list;
  cc_field_types : ml_type list;
  cc_temps_at_slot : cpp_type list;
  cc_states_unboxed : int -> bool;
  cc_list_cons : bool;
  cc_deeply_erased : bool;
  cc_passthrough : int -> bool;
}

(** [custom env ~expected_ty ~slot ty r]: the custom constructor [r] of
    annotation [ty] ({!custom_refined_annotation}), built at [expected_ty]
    into [slot] under the return type in force. *)
let custom env ~expected_ty ~slot (ty : ml_type) r =
  (* Generate args with expected type hints: pass the i-th type arg of the constructor's inductive type before generating
     the i-th value arg.  This allows gen_ctor_call to recover concrete element
     types for nil lists whose ML annotation has unresolved metas (Tmeta{None}).
     Specifically: in pair(fr, nil), the pair type args [A, B] tell us B = list(A),
     so the nil's element type can be recovered as A even if its annotation is Tmeta. *)
  (* Try to get type args from the pair type annotation, falling back to the
     outer [expected_ml_ty] (set by an enclosing MLletin or MLapp
     lookahead) when the pair type itself is erased (Tmeta{None}). This
     recovers the expected element type for nil args in pairs like
       let sk0 : parser_frame × list(parser_frame) = (fr(...), nil)
     where the pair MLcons has type annotation Tmeta{None}. *)
  let ty_args_for_expected =
    let rec deep_resolve ty =
      match resolve_tmeta ty with
      | Miniml.Tglob (n, tys, s) -> Miniml.Tglob (n, List.map deep_resolve tys, s)
      | Miniml.Tarr (t1, t2) -> Miniml.Tarr (deep_resolve t1, deep_resolve t2)
      | t -> t
    in
    (* Also try the expected type from the enclosing let-binding when deep_resolve
       can't resolve sub-metas in the pair's own type annotation.
       The expected type comes from t_effective which may have different (resolved) metas. *)
    let fallback_from_expected tys =
      if List.exists (ml_type_contains_erased ~in_arrows:true) tys then
        match slot.expected_ml_ty with
        | Some exp ->
          let ctor_ind = match r with
            | GlobRef.ConstructRef ((kn, i), _) -> Some (GlobRef.IndRef (kn, i))
            | _ -> None
          in
          (match deep_resolve exp, ctor_ind with
          | Miniml.Tglob (exp_n, exp_tys, _), Some ind
            when GlobRef.CanOrd.equal exp_n ind
                 && List.length exp_tys = List.length tys ->
            (* An arrow the annotation left unresolved is erasure too -- the
               closure inside an [option (nat -> nat)] is precisely what the
               slot knows and the annotation does not.  The slot's answer is
               only usable where no type variable survives in it: one that does
               names a template parameter out of scope here, and would print as
               a bare [T1]. *)
            List.map2 (fun local outer ->
              if ml_type_contains_erased ~in_arrows:true local
                 && not (Ml_type_util.ml_type_contains_tvar outer)
              then outer else local) tys exp_tys
          | _ -> tys)
        | None -> tys
      else tys
    in
    match deep_resolve ty with
    | Miniml.Tglob (_, tys, _) -> fallback_from_expected tys
    | _ ->
      (match slot.expected_ml_ty with
      | Some exp ->
        let ctor_ind = match r with
          | GlobRef.ConstructRef ((kn, i), _) -> Some (GlobRef.IndRef (kn, i))
          | _ -> None
        in
        (match deep_resolve exp, ctor_ind with
        | Miniml.Tglob (exp_n, exp_tys, _), Some ind
          when GlobRef.CanOrd.equal exp_n ind -> exp_tys
        | _ -> [])
      | None -> [])
  in
  (* Pre-compute field types and draft template types so we can wrap lambdas
     that are stored in erased (std::any) fields.  This mirrors the logic in
     wrap_if_needed_for_field for the standard MLcons path. *)
  let field_types_for_wrap = match Table.get_ctor_ip_types_opt r with
    | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
    | None -> [] in
  let draft_ctor_temps_for_wrap =
    ctor_draft_temps env ~promoted_active:((!tctx).promoted_var_map <> [])
      ~return:(current_cpp_return_type ()) ty
  in
  (* The same slots, read off the destination instead of off this
     constructor's own annotation.  A locally concrete value can be built into
     a slot that names a more erased instantiation of the same type -- a
     [pair<List<std::any>, std::any>] field of a [sigT] receiving a
     [(l, @length A)] whose components are concrete here -- and it is the
     destination's shape that every consumer reads back, so a component
     landing in one of its erased positions has to be boxed.

     It goes the other way too, and for the same reason.  This constructor's
     own annotation can name a type variable the enclosing scope has no
     spelling for -- the [A] of the [bind] whose callback this body is -- and
     [std::any] is then not a statement that the position is boxed, only that
     the annotation could not be written here.  The destination can write it:
     the call that takes this value spells the very type [A] stands for
     ([typename _tcI0::iptr]).  Where one side is erased and the other is not,
     the one that says something is the one to believe; where both say
     something, the local instantiation is the more precise. *)
  let ctor_temps_at_slot =
    match (expected_ty, r) with
    | Some exp, GlobRef.ConstructRef ((kn, i), _) -> (
      match unfold_cpp_typedef env exp with
      | Tglob (en, eargs, _)
        when GlobRef.CanOrd.equal en (GlobRef.IndRef (kn, i))
             && List.length eargs = List.length draft_ctor_temps_for_wrap ->
        List.map2
          (fun local slot ->
            if slot = Tany then Tany
            else if prints_as_any local then slot
            (* Erased only in part -- [pair<std::any, ...>] where a field's
               class variable had no instance in scope -- the destination
               fills the part it knows, [St<ptr>]. *)
            else if Ml_type_util.has_tany_written local then
              Ml_type_util.refine_erased_by ~expected:slot local
            else local )
          draft_ctor_temps_for_wrap eargs
      | _ -> draft_ctor_temps_for_wrap )
    | _ -> draft_ctor_temps_for_wrap
  in
  (* Whether the destination spelled position [j] concretely.  A type that
     writes its arguments down -- [std::pair<std::any, Exp<std::any>>] -- has
     thereby said which of them are boxed and which are not, and a statement
     beats the inference below, which concludes from one erased argument that
     every position is read back erased.  That inference is sound only where
     the erasure is invisible in the C++ type. *)
  let slot_states_unboxed j =
    match (expected_ty, r) with
    | Some exp, GlobRef.ConstructRef ((kn, i), _) -> (
      match unfold_cpp_typedef env exp with
      (* A statement is a spelling that boxes some positions and not others;
         one that boxes none is this value's own type, which the deep
         erasure asked for by its destination overrides. *)
      | Tglob (en, eargs, _)
        when GlobRef.CanOrd.equal en (GlobRef.IndRef (kn, i))
             && List.exists prints_as_any eargs -> (
        match List.nth_opt eargs j with
        | Some t -> not (prints_as_any t)
        | None -> false )
      | _ -> false )
    | _ -> false
  in
  (* Whether this constructor's value lands in a DEEPLY erased slot: one
     whose consumer does not merely read a [std::any] back, but
     reconstructs the shape underneath it and reads every component boxed
     as well ([any_cast<pair<any,any>>]).  Two things put a value in that
     position, and they mean the same thing:

     - a sibling field of this very constructor is erased, so the whole
       tuple is read back in erased form -- e.g. [(v, tt)] at
       [symbols_semty [x] = prod (symbol_semty x) unit], where the first
       component is erased and the second is a concrete [unit];
     - the value flows straight out into a value-dependent erased slot,
       the enclosing function's C++ return type having resolved to
       [std::any] (e.g. [domty n], a type-level match).

     In both cases a concrete component stored as itself would produce
     [pair<string, monostate>], which the consumer's
     [any_cast<pair<any,any>>] cannot recover.  A custom LIST cons is
     excluded from the second case: its elements keep their own container
     type (see [is_already_container] below).  *)
  let is_list_cons_ctor =
    match r with
    | GlobRef.ConstructRef ((kn, _), _) ->
      let ind = GlobRef.IndRef (kn, 0) in
      Ml_type_util.is_custom_list_global ind
    | _ -> false
  in
  (* "A sibling field is erased" is a statement about fields, so only the
     type arguments this constructor's fields actually stand at count.
     [itreeF]'s event index erases -- no [E] has a C++ spelling -- and
     [RetF]'s one field is an [R]; reading the erasure off the whole
     argument list would box that field for a reason no field of [RetF]
     has anything to do with. *)
  let erased_arg_under_a_field =
    let occupied =
      List.fold_left collect_tvars [] field_types_for_wrap
    in
    (* Read at the destination's refinement, as [field_slot] below is: a
       field the annotation erased and the destination writes is not
       erased. *)
    List.exists
      (fun j -> List.nth_opt ctor_temps_at_slot (j - 1) = Some Tany)
      occupied
  in
  let slot_is_deeply_erased =
    erased_arg_under_a_field
    || ((not is_list_cons_ctor)
        && match current_cpp_return_type () with
           | Some t -> resolves_to_any_type t
           | None -> false)
  in
  { cc_ty_args_for_expected = ty_args_for_expected; cc_field_types = field_types_for_wrap;
    cc_temps_at_slot = ctor_temps_at_slot; cc_states_unboxed = slot_states_unboxed;
    cc_list_cons = is_list_cons_ctor; cc_deeply_erased = slot_is_deeply_erased;
    cc_passthrough = ctor_arg_is_passthrough r }

(** Where an argument of a custom constructor is built: under the return
    type [ca_ret], as the term [ca_term] (a function value stored erased
    adapted), into the slot [ca_slot] at the ML type [ca_expected_ml],
    against the C++ type [ca_expected]; [ca_erased_fn_slot] is the slot's
    own signature where it erased only its domain. *)
type custom_arg = {
  ca_ret : cpp_type option;
  ca_term : ml_ast;
  ca_expected_ml : ml_type option;
  ca_erased_fn_slot : cpp_type option;
  ca_expected : cpp_type option;
  ca_slot : slot;
}

(** [custom_field env c ~slot r i e]: where the [i]th argument [e] of the
    custom constructor [r], set up as [c] and built into [slot], is
    generated.  [var] reads a variable as {!ml_expr_is_function_value} does. *)
let custom_field ?var env c ~slot r i e =
  let ty_args_for_expected = c.cc_ty_args_for_expected and field_types_for_wrap = c.cc_field_types in
  let ctor_temps_at_slot = c.cc_temps_at_slot and is_passthrough_ctor_arg = c.cc_passthrough in
  let saved_ret = current_cpp_return_type () in
  let new_expected =
    match List.nth_opt field_types_for_wrap i with
    | Some (Miniml.Tvar (_, j) as ft) -> (
      match List.nth_opt ty_args_for_expected (j - 1) with
      | Some (Tdummy _) | None -> Some ft
      | x -> x )
    | Some ft when ty_args_for_expected <> [] ->
      Some (Mlutil.type_subst_list ty_args_for_expected ft)
    | Some ft -> Some ft
    | None ->
    match List.nth_opt ty_args_for_expected i with
    | Some (Tdummy _) | None ->
      (* A [Tdummy] here means extraction couldn't statically reduce this
         type argument (e.g. a [prod]'s component type inferred through a
         non-reducible dependent [match] like [nt_semty x] at a literal
         [x], which is dependently well-typed in Coq but whose component
         types the ML type annotation on this specific node leaves as
         placeholders) -- it carries no more information than [None], so
         fall back the same way: to the concrete field type when the
         enclosing constructor has an erased ML type (e.g. pair(pred,
         action) with Tmeta{None}).  Combined with the MLlam
         Tarr-stripping logic, this lets gen_ctor_call recover the
         concrete element type for nil constructors, and lets a "cons"
         argument like a tuple literal's own component recover its
         declared field type so it gets any_cast'd to the concrete type
         instead of staying a bare [std::any] mismatched with the
         constructor's own (correctly concrete) return type. *)
      List.nth_opt field_types_for_wrap i
    | Some _ as x -> x
  in
  (* Propagate the erased-return-slot context into nested pair/tuple
     fields (e.g. the second component of [(n, (n, tt))]) so that a
     nested prod-cons also self-boxes its OWN components into
     [std::any] instead of relying on the outer cons to wrap the whole
     nested value as a single opaque [std::any].  Without this, only
     the outer level is erased and a further destructure of the inner
     value (e.g. a recursive call peeling one field at a time) hits a
     [std::any] holding a concrete (non-any) pair, causing
     [any_cast<pair<any,any>>] to throw at runtime. *)
  let is_list_cons_ctor_for_flow_pre =
    match r with
    | GlobRef.ConstructRef ((kn, _), _) ->
      let ind = GlobRef.IndRef (kn, 0) in
      Ml_type_util.is_custom_list_global ind
    | _ -> false
  in
  let propagate_erased_ctx =
    (not is_list_cons_ctor_for_flow_pre)
    &&
    match saved_ret with
    | Some t -> resolves_to_any_type t
    | None -> false
  in
  let expected_cpp_ty =
    match new_expected with
    | Some ml_ty ->
      let cpp_ty = cpp_of_ml env ml_ty in
      (* A field at a type parameter is the constructor's instantiation
         there, as the destination refined it: the annotation's own
         spelling erases a class variable with no instance in scope
         ([pair<std::any, ...>]) that the destination writes ([St<ptr>]),
         and a nested constructor built at the erased one boxes it. *)
      let cpp_ty =
        match List.nth_opt field_types_for_wrap i with
        | Some (Miniml.Tvar (_, j)) when Ml_type_util.has_tany_written cpp_ty -> (
          match List.nth_opt ctor_temps_at_slot (j - 1) with
          | Some t when not (prints_as_any t) ->
            Ml_type_util.refine_erased_by ~expected:t cpp_ty
          | _ -> cpp_ty )
        | _ -> cpp_ty
      in
      if prints_as_any cpp_ty then None
      else (match cpp_ty with
        | Tglob (g, _, _) when is_list_global g -> None
        | _ -> Some cpp_ty)
    | None -> None
  in
  let e =
    if stores_erased_fn ?var env r ~field_tys:field_types_for_wrap ~temps:ctor_temps_at_slot i e then
      erased_fn_lambda env e
    else e
  in
  (* The slot's own signature, when it erased only its domain: a callable
     reaching it is written against that signature (its parameters arrive
     boxed), and {!coerce} adapts it with [crane_erase_fn]. *)
  let erased_fn_slot =
    if is_passthrough_ctor_arg i || not (ml_expr_is_function_value ?var e) then
      None
    else
      match List.nth_opt field_types_for_wrap i with
      | Some (Miniml.Tvar (_, j)) -> (
        match
          Option.map Ml_type_util.tvar_erase_type
            (List.nth_opt ctor_temps_at_slot (j - 1))
        with
        | Some t when partially_erased_fun_ty t -> Some t
        | _ -> None )
      | _ -> None
  in
  { ca_ret = (if propagate_erased_ctx then Some Tany else None);
    ca_term = e;
    ca_expected_ml = new_expected;
    ca_erased_fn_slot = erased_fn_slot;
    ca_expected = (match erased_fn_slot with Some _ as t -> t | None -> expected_cpp_ty);
    ca_slot = {slot with expected_ml_ty = new_expected} }
