(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The state a declaration generator works in: the per-body bookkeeping every
    top-level body begins with, and the resolutions of class-promoted type
    variables and higher-kinded carriers in scope. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Util
open Translation_state
open Translation

module IntSet = Escape.IntSet

(** Top-level bodies generated in each phase of the unit being extracted;
    see {!body_generation_counts}. *)
let body_generations : (Common.phase, int) Hashtbl.t = State.table State.Unit 3

let body_generation_counts () =
  List.map
    (fun p -> (p, Option.default 0 (Hashtbl.find_opt body_generations p)))
    [Discover; Emit Impl; Emit Intf]

(** Begin generating a top-level body -- a function's, a constant's, a
    method's or an instance method's: count it, and start its state afresh,
    so that what it generates does not depend on what was generated before
    it.  Fresh-name counters start at zero, and no parameter is tracked for
    moves; a body with parameters sets that tracking after this. *)
let begin_body () =
  let phase = get_phase () in
  Hashtbl.replace body_generations phase
    (1 + Option.default 0 (Hashtbl.find_opt body_generations phase));
  tctx :=
    { !tctx with
      match_param_counter = 0;
      cs_counter = 0;
      current_letin_depth = 0;
      move_owned_vars = Escape.IntSet.empty;
      move_n_params = 0;
      move_dead_after = Escape.IntSet.empty }

(** [with_method_env_types env params f] runs [f] with the de Bruijn type
    stack holding exactly [params] (innermost binder first, as returned by
    {!push_vars'}), restoring the ambient stack afterwards.  [env] is the
    type-variable scope the parameters' C++ types are assigned in; see
    {!Translation.push_binders}.

    An instance method's body is generated outside any enclosing function, so
    without this the stack still describes whatever was translated last — and
    a lookup of a parameter's type answers with a stale, unrelated entry (for
    a class's associated [Type], the unresolved class type variable, which
    reads as erased and provokes a spurious [any_cast]). *)
let with_method_env_types ?(cpp = []) env params f =
  let saved_env_types = (!tctx).env_types in
  let saved_erased = save_erased_env () in
  reset_env_types ();
  push_binders ~cpp env params;
  Fun.protect
    ~finally:(fun () ->
      tctx := { !tctx with env_types = saved_env_types };
      restore_erased_env saved_erased )
    f

(** Count the actual (non-promoted) type parameters in [ip_sign].  Entries
    marked [Keep] correspond to real template parameters; the remaining
    entries are promoted Type-valued fields. *)
let count_keep_params sign =
  List.length (List.filter (fun x -> x == Keep) sign)

(** True when [i] (an index into a class's [ip_vars]) is a real C++ template
    type parameter.  Everything else — the promoted [Type]-valued fields past
    the [Keep] parameters, and any [Keep] parameter that is itself a type
    constructor ([M : Type -> Type]) — becomes an associated type of the
    instance, spelled [typename I::name]. *)
let is_class_tparam class_ref i =
  i < Table.get_ind_nb_sign_keeps class_ref
  && not (Table.is_hkt_param class_ref i)

(** Name of the [i]-th element-type parameter an instance's carrier alias
    template binds. *)
let hkt_alias_param_name i = Generated_name.indexed "A" i

let recover_method_quantifier = Ml_type_util.recover_method_quantifier

let method_tvar_count = Ml_type_util.method_tvar_count

(** The arguments a higher-kinded carrier has already fixed: [Fn (prod X)]
    fixes the pair's first component, while the eta-expanded [option _] fixes
    nothing.  What is left is what the class still applies -- as the alias
    template's parameters, or as the method's own type variables. *)
let hkt_carrier_fixed_args arity ml_ty =
  match ml_ty with
  | Miniml.Tglob (r, args, _) ->
    let given = List.length args in
    let total = max arity (max given (Table.get_type_scheme_arity r)) in
    let fixed = max 0 (total - arity) in
    if given >= fixed then safe_firstn fixed args else []
  | Miniml.Tapp (_, args) ->
    (* A carrier that is a type variable ([Instance ... (M : Type -> Type)])
       is eta-expanded the same way, but has no declared scheme to compare
       against: what it applies beyond [arity] is what it fixed. *)
    safe_firstn (max 0 (List.length args - arity)) args
  | _ -> []

(** Render a type CONSTRUCTOR argument as an alias template body: the [list] of
    [Instance ListContainer : Container list] becomes [List<_A0>], to be
    emitted as [template <typename _A0> using C = List<_A0>;].  The element
    types are fresh type variables numbered from [base], so the caller must
    append {!hkt_alias_param_name} entries to the type-variable list it passes
    to [convert_ml_type_to_cpp_type]. *)
let hkt_carrier_alias base arity ml_ty =
  let is_lambda =
    match ml_ty with
    | Miniml.Tglob (_, args, _) | Miniml.Tapp (_, args) -> Mlutil.writes_binder args
    | _ -> Mlutil.type_has_hole ml_ty
  in
  match ml_ty with
  (* A carrier with a hole is a type-level lambda whose binder is the hole:
     [stateT S m] reaches here as [S -> m (S * _)], and an alias of an
     applied type, [EOUP Z := EOU (MaybePoison Z)], as [EOU (MaybePoison _)].
     The alias applies it to its parameter. *)
  | _ when arity = 1 && is_lambda ->
    ( [hkt_alias_param_name 0],
      Mlutil.fill_type_hole (Miniml.Tvar (Schematic, base + 1)) ml_ty )
  | Miniml.Tglob (r, args, es) ->
    let kept = hkt_carrier_fixed_args arity ml_ty in
    let params =
      max arity (max (List.length args) (Table.get_type_scheme_arity r))
      - List.length kept
    in
    ( List.init params hkt_alias_param_name,
      Miniml.Tglob
        ( r,
          kept
          @ List.init params (fun i -> Miniml.Tvar (Schematic, base + 1 + i)),
          es ) )
  | Miniml.Tapp (j, args) ->
    let kept = hkt_carrier_fixed_args arity ml_ty in
    let params = max arity (List.length args) - List.length kept in
    ( List.init params hkt_alias_param_name,
      Miniml.Tapp
        ( j,
          kept
          @ List.init params (fun i -> Miniml.Tvar (Schematic, base + 1 + i)) )
    )
  | _ when arity = 1 ->
    (* An unnamed carrier is the identity constructor: [F<_A0> = _A0]. *)
    ([hkt_alias_param_name 0], Miniml.Tvar (Schematic, (base + 1)))
  | _ -> ([], ml_ty)

(** The concrete types a class's associated types take in an instance, read off
    the instance's class arguments ([Container list] gives [C = List<_A0>]).
    Each is paired with the type parameters it binds: empty for a plain
    associated type, one per element type for a higher-kinded carrier. *)
let class_promoted_concrete ?(tvar_base = 0) class_ref type_args =
  List.mapi
    (fun i ty ->
      if Table.is_hkt_param class_ref i then
        hkt_carrier_alias tvar_base (Table.get_ind_hkt_arity class_ref i) ty
      else ([], ty) )
    type_args
  |> List.filteri (fun i _ -> not (is_class_tparam class_ref i))

(** Whether an [ip_vars] entry named [v] is really an associated type of
    [class_ref].

    A field whose type is a class is promoted while extraction still sees a
    class there, but whether that class survives as a concept is decided
    later, by {!Extract_env.demote_value_typeclasses}: one used in value
    position comes out as a plain struct, and the field holding it stays an
    ordinary value field.  Asking for it as [typename I::f] then sits beside
    the method requirement the value side emits, and a concept wanting one
    name both as a type and as a function is satisfied by no instance at all.
    The declaration says whether something is a class; only the back end says
    whether it stayed one. *)
let promoted_var_is_associated_type class_ref v =
  List.for_all
    (fun (field_opt, field_ty) ->
      match (field_opt, field_ty) with
      | Some fr, Miniml.Tglob (r, _, _)
        when Id.equal (Common.id_of_global Term fr) v ->
        Table.is_typeclass r
      | _ -> true )
    (Table.get_record_field_bindings class_ref)

(** The associated-type ("promoted") variables of a class, in [ip_vars] order,
    each paired with its arity: [0] for a plain associated type, [n] for a
    higher-kinded carrier, which is an alias template of [n] parameters. *)
let class_promoted_vars_arities class_ref =
  List.mapi
    (fun i v -> (v, Table.get_ind_hkt_arity class_ref i))
    (Table.get_ind_ip_vars class_ref)
  |> List.filteri (fun i _ -> not (is_class_tparam class_ref i))
  |> List.filter (fun (v, _) -> promoted_var_is_associated_type class_ref v)

(** The associated-type ("promoted") variables of a class, in [ip_vars]
    order. *)
let class_promoted_vars class_ref =
  List.map fst (class_promoted_vars_arities class_ref)

(** A class's fields paired with their ML types, as extraction recorded the
    pairing. *)
let class_fields_with_types = Table.get_record_field_bindings

(** The associated types an instance parameter provides, as a substitution from
    the bare name a promoted type variable carries to the qualified type it
    really denotes.

    [inst_ty] is the instance those names hang off: [Tinstance (_tcI0, Mon)]
    for a function's instance argument, [Tinstance (I, Mon)] inside the class's
    own concept.  A direct associated type of [class_ref] resolves to [typename
    I::Obj].  A field that is itself a type class contributes its own
    associated types one level deeper ([typename I::base_category::Obj]) —
    extraction marks those with the same bare name, so they are otherwise
    indistinguishable from direct ones.  Direct entries win: a name is never
    resolved through a field when the class declares it itself.

    The field need not be a promoted variable of [class_ref].  A class-typed
    field is spelled [typename I::PROV] whether or not it was promoted -- that
    is what the concept requires of [I] -- so the path exists either way, and
    a class whose every field is an instance promotes nothing at all.
    Requiring promotion here left [ParamsV]'s [PROV] and [PTR] contributing no
    resolutions, so [provenance], [ptr] and the rest fell back to the
    file-scope [using provenance = std::any;].

    [fields] defaults to {!class_fields_with_types}; pass it when the caller
    already holds the pairing, as it does while generating the class itself. *)
let promoted_resolutions ?fields class_ref inst_ty =
  let fields =
    match fields with Some f -> f | None -> class_fields_with_types class_ref
  in
  let direct = class_promoted_vars class_ref in
  let is_direct v = List.exists (Id.equal v) direct in
  let nested =
    List.concat_map
      (fun (field_opt, field_ty) ->
        match (field_opt, field_ty) with
        | Some field_ref, Miniml.Tglob (r, _, _) when Table.is_typeclass r ->
          let field_id = Common.id_of_global Term field_ref in
          List.filter_map
            (fun v ->
              if is_direct v then None
              else Some (v, Tqualified (Tqualified (inst_ty, field_id), v)) )
            (class_promoted_vars r)
        | _ -> [] )
      fields
  in
  List.map (fun v -> (v, Tqualified (inst_ty, v))) direct @ nested

(** The resolutions a class argument supplies to the instance that was given
    it.

    [PIV : @PI ProvenanceV PointerV] owns no type of its own: [ptr] belongs to
    [PointerV] and [prov] to [ProvenanceV].  Both are given concretely, so
    neither becomes a template parameter and neither survives into the ML type
    -- the class stands there alone as [PI] -- and their promoted variables
    keep their names while losing the path that gave them meaning, falling back
    to the file-scope [using prov = std::any;].  The variables that {e do}
    resolve are exactly the ones whose instance survived as a parameter: one
    declaration, and the only difference is whether the owner is still there.

    [own_instances] is what a class argument is applied to when it takes
    arguments.  At the instance's own definition these are its class
    parameters; at a use site they are the arguments the use writes.  The two
    share a context -- [PointerV] takes the [_tcI0] that [PIV] takes -- which
    is why one list serves both.  An argument applied to a different number is
    left alone: that it is applied at all says it has a context, and a context
    this one cannot supply is not one to guess at. *)
let rec class_arg_type ~own_instances sh =
  match sh with
  | Table.Carg_unknown -> None
  | Table.Carg (r, []) -> Some (Tglob (r, [], []))
  | Table.Carg (r, [arg]) when Table.is_projection r ->
    (* A class field is an instance of its own class -- [@IPTR P] is an [IPtr]
       -- but it is not applied to the record, it is selected from it.  Spelling
       it as a template gives the undeclared [IPTR<ParamsV<natIPtr>>], and a
       second, wrong answer for every name it owns is indistinguishable from
       none: {!drop_ambiguous} then drops the right one with it. *)
    Option.map
      (fun t -> Tqualified (t, Common.id_of_global Term r))
      (class_arg_type ~own_instances arg)
  | Table.Carg (r, args) ->
    (* A recorded argument spells itself; an unknown one is the context the
       recorded type shares with [own_instances] -- [PointerV] takes the
       [_tcI0] that [PIV] takes -- and is filled by position.  A list of a
       different length is not one to guess at. *)
    let ts =
      List.mapi
        (fun i a ->
          match class_arg_type ~own_instances a with
          | Some t -> Some t
          | None ->
            if List.length args = List.length own_instances then
              List.nth_opt own_instances i
            else None )
        args
    in
    if List.for_all Option.has_some ts then
      Some (Tglob (r, List.map Option.get ts, []))
    else None

let resolutions_of_shapes ~own_instances arg_shapes =
  List.concat_map
    (fun sh ->
      match sh with
      | Table.Carg_unknown -> []
      | Table.Carg (arg_ref, _) -> (
        match
          ( Table.get_instance_class_shape arg_ref
          , class_arg_type ~own_instances sh )
        with
        | Some (arg_class, _), Some inst_ty when Table.is_typeclass arg_class ->
          promoted_resolutions arg_class inst_ty
        | _ -> [] ) )
    arg_shapes

let instance_arg_resolutions ~own_instances inst_ref =
  match Table.get_instance_class_shape inst_ref with
  | None -> []
  | Some (_, arg_shapes) -> resolutions_of_shapes ~own_instances arg_shapes

(** The resolution a declaration's own type supplies when that type is an
    inductive whose constructor fields name an instance -- see
    {!Table.get_type_class_args}.  [boxed : @dval natIPtr] is what says which
    [IPtr] the [ptr] inside [dval] belongs to, and the only thing that does:
    the ML type keeps neither the argument nor the dependence. *)
let ind_type_resolutions r =
  match Table.get_instance_class_shape r with
  | Some (head, arg_shapes) ->
    let own_instances =
      (* The arguments the declaration's own type writes, spelled as written:
         [@dval (@ParamsV natIPtr)] holds [ParamsV<natIPtr>], not [ParamsV].
         All or none, because they are read by position. *)
      let ts = List.map (class_arg_type ~own_instances:[]) arg_shapes in
      if List.for_all Option.has_some ts then List.map Option.get ts else []
    in
    resolutions_of_shapes ~own_instances
      (* The instances the type is applied to resolve their own classes'
         variables, not only the ones its fields name: a field whose type
         unfolds a projection spells the class variable of the context
         instance directly, and [@frame natIPtr] is what says which. *)
      (arg_shapes @ Table.get_type_class_args head)
  | None -> []

(** Drop a promoted name the list answers with two different types.

    Two right answers look exactly like none, and they must: a term that names
    [natIPtr] and [boolIPtr] says nothing about which one a bare [iptr] meant,
    and spelling either one puts [Dval<typename natIPtr::iptr>] on the value
    built at the other.  The erased alias is the only answer that is not wrong
    somewhere.  Every list of resolutions read from a term passes through
    here -- a list that skipped it would reinstate the guess.

    A discard destroys evidence, so under [CRANE_CHECK_IR] it says so.  Two
    right answers are benign, but one right answer and one {e wrong} one
    annihilate just the same, and the wrong one would have been an undeclared
    identifier: the filter turns a compile error into a silent [std::any].  The
    spellings are printed because which of them is nonsense is a question only
    a reader can answer. *)
let drop_ambiguous res =
  let ambiguous (n, t) =
    List.exists (fun (m, u) -> Id.equal n m && u <> t) res
  in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    List.iter
      (fun (n, t) ->
        if ambiguous (n, t) then
          Feedback.msg_warning
            Pp.(
              str "promoted variable " ++ Id.print n
              ++ str " is answered more than once; dropping every answer" ) )
      res;
  List.filter (fun e -> not (ambiguous e)) res

(** The resolution a term supplies for the promoted type variables its own type
    leaves unresolved.

    A class's [Type] field is a promoted type variable, and a type mentioning
    one says nothing about which instance it belongs to: extraction records
    [run : EOU ptr] with [ptr] applied to no arguments at all.  Outside any
    instance struct there is then no [promoted_var_map], so the marker falls
    back to the file-scope alias -- which is the right answer for a use with no
    instance in sight, and the erased one here, because the term names one.

    Every concrete instance the term mentions is read, and each contributes
    what it knows: the promoted variables of its own class, and those of the
    class arguments it was given (see {!instance_arg_resolutions}).  A name two
    instances answer differently is dropped rather than decided -- the term
    mentions both and nothing here says which one the type meant. *)
let promoted_resolutions_of_body ?r ?ty b =
  let found = ref [] in
  (* A recorded shape is only an instance's when its head is a class: the
     record is taken at extraction, before the tables that would say so are
     filled, so the question is asked here instead. *)
  let instance_class r =
    match Table.get_instance_class_shape r with
    | Some (class_ref, _) when Table.is_typeclass class_ref -> Some class_ref
    | _ -> None
  in
  let add inst_ref inst_ty =
    match Table.get_instance_class_shape inst_ref with
    | Some (class_ref, _) when Table.is_typeclass class_ref ->
      let own_instances =
        match inst_ty with Tglob (_, args, _) -> args | _ -> []
      in
      found :=
        !found
        @ promoted_resolutions class_ref inst_ty
        @ instance_arg_resolutions ~own_instances inst_ref
    | _ -> ()
  in
  (* An applied instance is read at its application: the head on its own says
     the same instance at no arguments, which is a second, poorer answer to the
     same name and would make the pair ambiguous with itself. *)
  (* An instance applied to a lambda parameter is spelled by that parameter's
     template name, which only the term's own environment knows; there is none
     here, and a resolution nobody can spell is not one to offer. *)
  let closed e =
    let ok = ref true in
    let rec go t =
      (match t with MLrel _ -> ok := false | _ -> ());
      Mlutil.ast_iter go t
    in
    go e;
    !ok
  in
  (* An instance applied to the declaration's own parameters may have no
     recorded shape -- one declared inside a section over the same class
     ([MemStateV] under [Context {Pa : Params}]) -- and its class is then
     the codomain of its own type. *)
  let instance_class_at r =
    match instance_class r with
    | Some _ as c -> c
    | None -> (
      match Table.find_type r with
      | ty -> (
        match Mlutil.type_simpl (Ml_type_util.ml_codomain ty) with
        | Miniml.Tglob (c, _, _) when Table.is_typeclass c -> Some c
        | _ -> None )
      | exception Not_found -> None )
  in
  let add_at class_ref inst_ref inst_ty =
    match Table.get_instance_class_shape inst_ref with
    | Some _ -> add inst_ref inst_ty
    | None -> found := !found @ promoted_resolutions class_ref inst_ty
  in
  (* The declaration's own class-instance parameters -- its leading binders
     whose type is a class -- are spelled by their template names, [_tcI0]
     and on: an instance applied to one of them, [MemStateV Pa] under
     [Existing Instance], is [MemStateV<_tcI0>] and resolves the fields of
     its class as much as a closed one does.  [leading] names the leading
     binders innermost-first, the order an [MLrel] reads them in; [None]
     for one that is not an instance. *)
  let leading =
    match ty with
    | None -> []
    | Some ty ->
      let binders, _ = collect_lams b in
      let doms = Ml_type_util.ml_domains ty in
      let tc_names = ref (Translation.collect_typeclass_param_ids ty) in
      let outer_first =
        List.mapi
          (fun j _ ->
            match List.nth_opt doms j with
            | Some d when Table.is_typeclass_type d -> (
              match !tc_names with
              | n :: rest -> tc_names := rest; Some n
              | [] -> None )
            | _ -> None )
          (List.rev binders)
      in
      List.rev outer_first
  in
  (* Every free variable of [e], [d] binders below the leading ones, is one
     of the leading instance binders. *)
  let spellable d e =
    let ok = ref true in
    let rec go depth t =
      ( match t with
      | MLrel i when i > depth ->
        let k = i - depth - d - 1 in
        ( match if k >= 0 then List.nth_opt leading k else None with
        | Some (Some _) -> ()
        | _ -> ok := false )
      | MLrel _ -> ()
      | _ -> () );
      match t with
      | MLlam (_, _, b) -> go (depth + 1) b
      | MLletin (_, _, a, b) -> go depth a; go (depth + 1) b
      | _ -> Mlutil.ast_iter (go depth) t
    in
    go 0 e;
    !ok
  in
  let env_at d =
    ( List.init d (fun _ -> Id.of_string "_") @ List.map (function Some n -> n | None -> Id.of_string "_") leading,
      snd (empty_env ()) )
  in
  let rec walk_at d e =
    match strip_magic e with
    | MLapp (MLglob (r, _), args)
      when instance_class_at r <> None && (not (closed (strip_magic e)))
           && leading <> [] && spellable d (strip_magic e) ->
      Option.iter
        (add_at (Option.get (instance_class_at r)) r)
        (ml_arg_to_template_type (env_at d) (strip_magic e));
      (* As [walk] does: the arguments are read on, all but the instance's own
         dictionary arguments. *)
      List.iter
        (fun a ->
          match strip_magic a with
          | MLglob (r', _) | MLapp (MLglob (r', _), _)
            when instance_class r' <> None ->
            ()
          | _ -> walk_at d a )
        args
    | MLlam (_, _, b') -> walk_at (d + 1) b'
    | MLletin (_, _, a, b') -> walk_at d a; walk_at (d + 1) b'
    | MLcase (_, sc, pv) ->
      walk_at d sc;
      Array.iter (fun (ids, _, _, br) -> walk_at (d + List.length ids) br) pv
    | MLfix (_, ids, funs, _) -> Array.iter (walk_at (d + Array.length ids)) funs
    | e' -> Mlutil.ast_iter (walk_at d) e'
  in
  let rec walk e =
        match strip_magic e with
    | MLapp (MLglob (r, _), args)
      when instance_class r <> None && closed (strip_magic e) ->
      Option.iter (add r)
        (ml_arg_to_template_type (empty_env ()) (strip_magic e));
      (* An instance's own dictionary arguments are not independent mentions.
         What they say is already said, in this instance's spelling, by
         {!instance_arg_resolutions}; read separately they answer the same name
         in their own spelling -- [natIPtr::iptr] beside [typename
         ParamsV<natIPtr>::IPTR::iptr] -- and the pair is then dropped as
         ambiguous, leaving the name erased. *)
      List.iter
        (fun a ->
          match strip_magic a with
          | MLglob (r', _) | MLapp (MLglob (r', _), _)
            when instance_class r' <> None ->
            ()
          | _ -> walk a )
        args
    | MLglob (r, _) -> add r (Tglob (r, [], []))
    | _ -> Mlutil.ast_iter walk e
  in
  walk b;
  (if leading <> [] then
     let _, inner = collect_lams b in
     walk_at 0 inner);
  (* What the declaration's own type applies to its class binders -- see
     {!Table.get_context_instance_apps} -- read as the application it is, over
     the template names those binders take. *)
  ( match (r, ty) with
  | Some r, Some ty ->
    let tc_names = collect_typeclass_param_ids ty in
    List.iter
      (fun (inst, ords) ->
        match
          (instance_class_at inst, List.map (List.nth_opt tc_names) ords)
        with
        (* A class field of a binder is selected from it, not applied to it:
           [@PTR Pa] is [_tcI0::PTR], which the binder already resolves. *)
        | Some class_ref, names
          when List.for_all Option.has_some names
               && not (Table.is_projection inst) ->
          let names = List.map Option.get names in
          let n = List.length names in
          let app =
            MLapp (MLglob (inst, []), List.init n (fun i -> MLrel (n - i)))
          in
          Option.iter (add_at class_ref inst)
            (ml_arg_to_template_type
               (List.rev names, snd (empty_env ()))
               app )
        | _ -> () )
      (Table.get_context_instance_apps r)
  | _ -> () );
  drop_ambiguous !found

(** Map a function's own type variables to the associated types they really
    stand for.  In [mret : forall M, Mon M -> forall A, A -> M A] the variable
    standing for [M A] is [typename _tcI0::M] — an associated type of the
    instance, not a template parameter.  Left as a free template parameter it
    would be undeducible: nothing in the signature determines it. *)

(** What the declarations a term names resolve through {e their} own types.

    A match over [boxed_iptr : @dval (@ParamsV natIPtr)] spells the
    constructor's type, and that type's promoted variables are resolved by the
    scrutinee's declaration, not by anything the match body mentions.  Read
    last: an instance the body names directly is a nearer answer than one
    inherited from a name it reads. *)
let type_resolutions_of_referenced_globals b =
  let found = ref [] in
  let rec walk e =
    ( match strip_magic e with
    | MLglob (r, _) -> found := !found @ ind_type_resolutions r
    | _ -> () );
    Mlutil.ast_iter walk e
  in
  walk b;
  drop_ambiguous !found

(** Generate a declaration's type and its body against the resolution its body
    supplies -- see {!promoted_resolutions_of_body} -- and the one its own type
    does, see {!ind_type_resolutions}.  An enclosing instance struct answers
    first: a variable it declares is the one this method is written in,
    whatever else the body mentions. *)
let with_body_resolutions r b f =
  with_promoted_var_map
    ( (!tctx).promoted_var_map
    @ promoted_resolutions_of_body ~r ?ty:(try Some (Table.find_type r) with Not_found -> None) b
    @ ind_type_resolutions r
    @ type_resolutions_of_referenced_globals b )
    f

let hkt_tvar_resolutions_of_type ty =
  List.map
    (fun { htp_tvar; htp_instance; htp_field } ->
      (htp_tvar, Tqualified (htp_instance, htp_field)) )
    (hkt_tvar_positions_of_type ty)

(** Rewrite the type variables listed in [resolutions] (see
    {!hkt_tvar_resolutions_of_type}) throughout a C++ type. *)
let apply_hkt_resolutions resolutions ty =
  if resolutions = [] then ty
  else
    Minicpp.subst_cpp_tvars (fun i -> List.assoc_opt i resolutions) ty

(** Rewrite those type variables throughout the statements of a function
    body, so type annotations there agree with the resolved signature. *)
let apply_hkt_resolutions_stmts resolutions stmts =
  if resolutions = [] then stmts
  else
    let ft = apply_hkt_resolutions resolutions in
    let rec fe e = Minicpp.map_expr fe fs ft e
    and fs s = Minicpp.map_stmt fe fs ft s in
    List.map fs stmts

(** Rewrite those type variables throughout a whole declaration: an instance
    struct resolves its carrier the same way a function does, but it has no
    single signature to rewrite -- the variable turns up in its [using]
    aliases, in every method's signature and in every method's body. *)
let apply_hkt_resolutions_decl resolutions decl =
  if resolutions = [] then decl
  else
    let ft = apply_hkt_resolutions resolutions in
    let rec fe e = Minicpp.map_expr fe fs ft e
    and fs s = Minicpp.map_stmt fe fs ft s in
    Minicpp.map_decl fe fs ft decl


(** The arguments for the promoted variables [r] mentions without declaring,
    which are template parameters of whatever [r] is generated as -- see
    {!Table.promoted_type_params}.  They trail a concept's arguments (the
    instance comes first, see {!gen_typeclass_cpp}) and lead a struct's (see
    [Cpp_ind]); every use has to supply them in this order, or it names a
    different template. *)
let mentioned_promoted_args r =
  List.map (fun v -> Tpromoted v) (Table.promoted_type_params r)

(** [deapply_families name vars ty] takes the application off each of
    [name]'s family parameters in [ty], spelled at [vars].  A family is a plain
    [typename] -- [E X] is written [E] -- and so is the parameter a conversion
    from another instantiation declares in its place, which the struct-level
    {!deapply_plain_tvars} does not see. *)
let deapply_families name vars =
  let families = List.filteri (fun i _ -> Table.is_family_ind_param name i) vars in
  map_cpp_type (function
    | Tapply ((Tvar (Tv_index (_, Some v) | Tv_named v) as head), _)
      when List.exists (Id.equal v) families ->
      head
    | t -> t )

(** The conversion function by which a value is read at another instantiation
    of its own type -- [Box<Nat>] reaching a slot spelled [Box<std::any>].

    The variant path says this with a converting constructor.  A struct that is
    an aggregate cannot have one: every brace initialisation the codegen writes
    for it, and every aggregate initialisation in hand-written test code,
    depends on its staying an aggregate, which any user-declared constructor
    would end.  A conversion function is the same statement from the other side
    and an aggregate may have as many as it likes.

    [fields] gives each field's name together with its C++ type {e at a given
    spelling of the type parameters}, because the two callers -- a Rocq
    [Record] and a flat single-constructor [Inductive] -- compute that type
    differently.  Nothing is emitted where the type has no parameters, or no
    fields: there is no other instantiation to read it at.

    [leading] are arguments the conversion keeps rather than respells: the
    promoted variables a caller did not put in [vars] (see
    {!mentioned_promoted_args}), which belong to the scope the type was
    declared in and not to the instantiation being converted.

    No constraint excludes [_U = T].  A conversion function to its own class
    type is never selected, so declaring it is harmless and saying so costs a
    [requires] clause on every generated struct. *)
let conversion_to_other_instantiation ~leading ~name ~templates ~vars ~fields =
  if vars = [] || fields = [] then []
  else
    let n_vars = List.length vars in
    let u_var_names =
      List.mapi (fun i _ -> Generated_name.member "U" ~of_:n_vars i) vars
    in
    let u_tys = List.map named_tvar u_var_names in
    (* Every inductive generated into this same scope -- the type itself,
       its mutual siblings, and any other module-local inductive -- is
       spelled bare here, so it must not be namespace-qualified. *)
    let skip g =
      GlobRef.CanOrd.equal g name
      || Table.same_mutual_block g name
      || List.exists (GlobRef.CanOrd.equal g) (get_local_inductives ())
    in
    let types =
      List.map
        (fun (field_id, at) ->
          ( field_id,
            deapply_families name vars (at vars),
            deapply_families name u_var_names (at u_var_names) ))
        fields
    in
    (* One constructor holds every field, so every field's route is needed:
       the conversion exists exactly where each one does. *)
    let converted =
      List.map
        (fun (field_id, src_ty, dst_ty) ->
          gen_type_conversion_expr ~skip ~route:Required ~src_ty ~dst_ty (CPPvar field_id))
        types
    in
    let requirements =
      List.filter_map
        (fun (_, src_ty, dst_ty) -> route_requirement ~skip ~src_ty ~dst_ty ())
        types
    in
    (* The source instantiation is the same template as the destination, so its
       arguments have the same kinds: a [template <typename> class] parameter
       cannot be stood in for by a plain [typename]. *)
    let tparams =
      List.mapi
        (fun i u ->
          let tt =
            match List.nth_opt templates i with Some (tt, _) -> tt | None -> TTtypename
          in
          (tt, u) )
        u_var_names
    in
    [ ( Fmethod
          { mf_name = Id.of_string "operator_at_other_instantiation";
            mf_globref = None;
            mf_tparams = tparams;
            mf_ret_type = Tglob (name, leading @ u_tys, []);
            mf_params = [];
            mf_body = [Sreturn (Some (CPPbraced converted))];
            mf_receiver = Instance { this_pos = 0; is_const = true; ref_qual = Rq_any };
            mf_is_inline = false;
            mf_no_pure = true;
            mf_is_noexcept = false;
            mf_kind = Conversion requirements },
        VPublic,
        SAccessors ) ]
