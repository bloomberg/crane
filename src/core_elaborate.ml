(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global calls elaborated from Core, ahead of translation
    (docs/Pipeline-Disentangling-Plan.md, section 4.7).  See
    [core_elaborate.mli]. *)

open Miniml
open Names
open Util
open Translation_state
open Ml_type_util
open Translation_support
open Translation_types
open Table

(** [classify ~lex id written] -- the role each argument the call of [id]
    writes has, as Core elaborates the call from the call alone
    ({!Elaborated_call.role}): a dictionary, a regular argument, one past the
    callee's arity and so applied to its result, or one at no value position.
    A variable argument is read off the binder it names in [lex], the
    environment the call is typed in, by its ML type and its role
    ({!Lexenv.binder}); no C++ name is consulted, and nothing of the
    traversal that asks. *)
let classify ~lex id written =
  (* Each argument with its position, so that the partition below says
     where each one went rather than handing back the arguments. *)
  let args = List.mapi (fun i a -> (i, a)) written in
  (* When the call has more args than the function's ML value-domain, the
     excess args are curried applications to the result. This is common with
     Rocq's Function vernacular _correct proof terms, where the extraction
     produces e.g. div2_rect f f0 f1 n _res __ but div2_rect only has 4
     value-domain params (f, f0, f1, n). The trailing _res and __ are applied
     to the result via currying.

     Split into: - primary_args: first n_value_dom args (passed to the
     function) - excess_args: remaining non-dummy args (curried onto the
     result) Only activates when n_args > n_value_dom; otherwise unchanged. *)
  let args_before_split = args in
  let args, excess_args =
    let is_value_arg = function
      | MLdummy _ -> false
      (* A variable bound at an erased type carries no more than a dummy:
         under [Conservative Types] a definition keeps its type binders and
         passes them on ([length A l']). *)
      | MLrel (i, _) -> (
        match Lexenv.type_opt lex i with
        | Some t -> not (erased_by_extraction t)
        | None -> true )
      | _ -> true
    in
    let is_value (_, a) = is_value_arg a in
    let is_value_dom t =
      match resolve_tmeta t with
      | Miniml.Tdummy _ -> false
      | _ -> true
    in
    let rec collect_tarr_dom acc = function
      | Miniml.Tarr (t1, t2) -> collect_tarr_dom (resolve_tmeta t1 :: acc) t2
      | _ -> List.rev acc
    in
    match find_type_opt id with
    | Some ml_ty ->
      let all_dom = collect_tarr_dom [] ml_ty in
      (* Count value-domain entries by filtering out ALL [Tdummy] positions
         (both [Ktype] for erased type params and [Kprop] for erased proofs).
         Symmetrically, filter the arg list to exclude [MLdummy] entries.
         Comparing these two filtered counts avoids false excess detection
         when erased params appear in [args] as [MLdummy] instead of (or in
         addition to) being carried in [tys]. *)
      let n_value_dom = List.length (List.filter is_value_dom all_dom) in
      (* An erased argument at a position the declaration takes a value at
         stays: the category classes over [obj : Type] take their objects
         as values, and at [obj := Type -> Type] those objects are families
         the call erases.  Dropping them would change the call's arity; the
         declaration receives an empty box instead. *)
      let value_args =
        (* Two conventions meet here.  The arguments the Rocq term gave
           have the declaration's erased domains dropped ([make_mlargs]
           kills each [Tdummy]), so each is at a value domain, erased or
           not.  The tail an eta-expansion invents keeps them: a dummy at
           each erased domain, a variable at each value one
           ([STRefToIxNat __ __ ref]).  The tail is the longest suffix
           paired with the domains that way, provided what precedes it
           fills the remaining value domains exactly; with none, every
           argument is at a value domain or past the last one.  The one
           dummy with no domain at all is the one a purely logical
           signature is applied to. *)
        if n_value_dom = 0 then List.filter is_value args
        else
          let n_args = List.length args and n_dom = List.length all_dom in
          let eta_paired k =
            List.for_all2
              (fun d a -> is_value_dom d = is_value a)
              (List.lastn k all_dom) (List.lastn k args)
            && List.length
                 (List.filter is_value_dom (List.firstn (n_dom - k) all_dom))
               = n_args - k
          in
          let rec longest k =
            if k = 0 then None else if eta_paired k then Some k else longest (k - 1)
          in
          match longest (min n_args n_dom) with
          | Some k ->
            List.firstn (n_args - k) args
            @ List.filter is_value (List.lastn k args)
          | None -> args
      in
      let n_value_args = List.length value_args in
      if n_value_args > n_value_dom then
        let primary =
          List.filteri (fun i _ -> i < n_value_dom) value_args
        in
        let excess =
          List.filteri
            (fun i a -> i >= n_value_dom && is_value a)
            value_args
        in
        (primary, excess)
      else
        (value_args, [])
    | None -> (List.filter is_value args, [])
  in
  (* A value argument that vanishes here vanishes from the emitted call, and
     the parameter it would have filled is dropped from the declaration by
     the same [Tdummy] reading of the callee's domain -- leaving a body that
     names a binder nothing supplies.  Report it rather than make it a
     question about reading the generated C++ back. *)
  let () =
    if Sys.getenv_opt "CRANE_DBG_DROPPED_ARGS" <> None then
      let n_in = List.length args_before_split in
      let n_out = List.length args + List.length excess_args in
      if n_out < n_in then
        Feedback.msg_warning
          (Pp.str
             (Printf.sprintf
                "crane: call to %s drops %d of %d arguments (%d dummy, %d \
                 value domains declared)"
                (Table.kername_of_global id)
                (n_in - n_out) n_in
                (List.length
                   (List.filter
                      (function _, MLdummy _ -> true | _ -> false)
                      args_before_split ))
                (List.length args) ) )
  in
  (* An erased instance leaves the call but not the declaration: its
     parameter is still one of the callee's, so a position counted in the
     declaration's parameter list steps over it. *)
  let instances, regular = List.partition (fun (_, a) -> is_typeclass_instance_arg ~lex a) args in
  let erased, kept = List.partition (fun (_, a) -> instance_arg_is_erased ~lex a) instances in
  (* The erased arguments left among the regular ones are the ones the
     declaration takes a value at (see [value_args] above); they are
     generated as empty boxes rather than as the [CPPabort] an [MLdummy] is
     elsewhere. *)
  let role_of i =
    let at l = List.exists (fun (j, _) -> Int.equal i j) l in
    if at kept then Elaborated_call.Dictionary
    else if at erased then Elaborated_call.Erased_dictionary
    else if at regular then Elaborated_call.Regular
    else if at excess_args then Elaborated_call.Excess
    else Elaborated_call.Dropped
  in
  List.mapi (fun i _ -> role_of i) written

(* The call of [use] to [args], each argument in the role at its position. *)
let of_roles use args roles =
  let id = use.callee in
  (* Order the instance arguments the way the callee numbered its own
     [_tcI] parameters.  [Gen_decls.gen_dfun] iterates [collect_lams]
     output, which is reversed from source order, so a plain constrained
     function's first instance parameter is the source-last one; an instance
     struct is stripped left to right by [Gen_decls.gen_instance_struct] and
     keeps source order.  Call sites have the arguments in source order. *)
  let dictionaries =
    if ref_returns_typeclass id then Elaborated_call.Source_order else Elaborated_call.Reversed
  in
  Elaborated_call.of_roles ~callee:id ~callee_type:(find_type id) ~dictionaries
    ~tyargs:(Call_tyargs.of_use use) args roles

let elaborate_arguments ~lex use args = of_roles use args (classify ~lex use.callee args)

(* The holes of [call]'s reading of its scheme variables that its context
   states: the ML type its position expects or states for its result
   ([expected_ml], else [stated_ml]), and the heads its arguments' types give
   a type-level function a domain names. *)
let resolve_from_context ~lex ~expected_ml ~stated_ml (call : Elaborated_call.t) =
  let {Elaborated_call.callee = id; callee_type = fn_ml_ty; primary = primary_ml_args; tyargs; _} =
    call
  in
  (* An erased event family the position's type names: [memM_interp]'s [E],
     given unapplied where [on_mem] takes a handler into [itree BotE].  The
     family occurs in the callee's result only, where nothing deduces it and
     the phantom filler would write [void]. *)
  let tyargs =
    match
      match expected_ml with
      | Some _ as t -> t
      | None -> stated_ml
    with
    | Some result when Call_tyargs.interior_holes tyargs <> [] ->
      let families = Ml_type_util.event_family_ml_tvars [fn_ml_ty] in
      (* A family is a head, or one applied at the index it erases
         ([BotE _]); [box nat] met at a bare variable is a value type, not
         the family. *)
      let family_shaped b =
        match resolve_tmeta b with
        | Miniml.Tglob (_, [], _) -> true
        | Miniml.Tglob (_, args, _) ->
          Ml_type_util.is_ml_erased_ty (List.nth args (List.length args - 1))
        | _ -> false
      in
      (* With [~constructors]: an applied variable against an application
         is the head, which for a family -- the only variables filled here --
         is the answer. *)
      let found =
        tvar_instantiation_found ~lex ~constructors:true ~result
          fn_ml_ty primary_ml_args
      in
      (* Only where nothing deduces it: a family a parameter spells is the
         compiler's to read off the argument. *)
      let deducible =
        Option.default IntSet.empty (deducible_tvars_of_glob id)
      in
      Call_tyargs.resolve Call_tyargs.Expected_result
        (fun v ->
          let k = Scheme.Var.ordinal v in
          match List.assoc_opt k found with
          | Some b
            when IntSet.mem k families && (not (IntSet.mem k deducible))
                 && family_shaped b ->
            Some b
          | _ -> None )
        (Call_tyargs.interior_holes tyargs) tyargs
    | _ -> tyargs
  in

  (* A type-level function passed where a type alias in a domain names it
     -- the category's [C] in [Id_ obj C] -- is a hole of the reading, stated
     by the dictionary argument.  Filled before anything is substituted, so
     the parameter types the arguments are generated against and the
     explicit type arguments the call writes agree. *)
  Elaborated_call.with_tyargs call
    (resolve_from_argument_heads ~only_alias_args:true ~lex tyargs primary_ml_args)

let instantiate ~lex ~expected_ml ~stated_ml ~caller ~scope call =
  let call = resolve_from_context ~lex ~expected_ml ~stated_ml call in
  let {Elaborated_call.callee = id; callee_type = fn_ml_ty; primary = primary_ml_args; tyargs; _} =
    call
  in
  (* A partial application is eta-expanded into a lambda spelled in the
     caller's scope, and a variable of the callee's that neither the call
     nor its arguments instantiate is not one of the caller's: left in, it
     prints as whichever caller variable shares its index -- [h_get]'s index
     as the enclosing handler's [T1].  It is erased, and a position nothing
     deduces is then written as the box it is. *)
  let reading =
    let n_params =
      let rec count ty =
        match expand_ml_fun_alias ty with
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with
           | Miniml.Tdummy _ -> count rest
           | _ -> 1 + count rest)
        | _ -> 0
      in
      count fn_ml_ty
    in
    (* Only one the lambda's result spells: a variable the codomain does not
       mention -- a rank-2 handler's [forall X] -- is not the call's to
       instantiate, and keeps itself.  And not in a call to the declaration
       being generated, whose variables {e are} the caller's. *)
    let self_call =
      match caller with
      | Some r -> GlobRef.UserOrd.equal r id
      | None -> false
    in
    if self_call || List.length primary_ml_args >= n_params then tyargs
    else
      let tyargs = resolve_from_argument_types ~lex tyargs primary_ml_args in
      let in_cod = collect_tvars_set IntSet.empty (ml_codomain fn_ml_ty) in
      let open_vars = Call_tyargs.beyond_extent tyargs in
      match
        List.fold_left
          (fun m v ->
            let i = Scheme.Var.ordinal v in
            if IntSet.mem i in_cod then max m i else m )
          0 open_vars
      with
      | 0 -> tyargs
      | n ->
        (* Erased only where it would be misread: a variable whose spelling
           no caller variable has is bound by the eta-lambda itself (see
           [eta_tparams]), and deduced there from the parameter that names
           it -- [memM T2] of a natural transformation. *)
        let collides i =
          List.exists
            (fun v -> String.equal (Id.to_string v) (Cpp_ir.Type.positional_name i))
            scope
        in
        Call_tyargs.resolve Call_tyargs.Eta_parameter
          (fun v ->
            let i = Scheme.Var.ordinal v in
            Some
              ( if IntSet.mem i in_cod && collides i then Miniml.Tunknown
                else Miniml.Tvar (Miniml.Schematic, i) ) )
          (List.filter (fun v -> Scheme.Var.ordinal v <= n) open_vars)
          tyargs
  in
  (* The one substitution that takes the callee's declared types to this
     call's; without it the argument generated into a [bind]'s [m A] is left
     with no stated type at all.  The declared parameter list and the
     substituted one are not indexed alike: substitution can make a
     parameter dummy that was not one before ({!Param_pos}). *)
  Elaborated_call.instantiate call ~reading
    ~at_call:(fun tys -> instantiate_at_call ~lex ~caller id tys primary_ml_args)
    ~expand:expand_ml_fun_alias
    ~erased:(fun t ->
      match resolve_tmeta t with
      | Miniml.Tdummy _ -> true
      | _ -> false )

(** Where the walk met an application: in a body as it is generated -- a
    declaration's, a method's, an instance method's -- or in a term a custom
    type is applied to, converted wherever the type is. *)
type site =
  | Body
  | Type_term

(** A global application of the program: the occurrence of the use naming
    its callee, the roles of the arguments it writes, its instantiation as
    planned where the walk met it ({!instantiate}), if that succeeded,
    whether it builds a closed instance ({!builds_closed_instance}),
    whether it calls a class field as a static member of an instance
    ({!Translation_types.static_projection}), whether its head is closed
    ({!closed_head}), and whether it calls a kept instance's member template
    ({!member_template_projection}). *)
type entry = {
  occurrence : Occurrence.t;
  roles : Elaborated_call.role list;
  planned : Elaborated_call.instantiated option;
  site : site;
  closed_instance : bool;
  static_projection : Elaborated_call.static_projection option;
  closed_head : bool;
  member_template : bool;
}

type t = {
  calls : entry list Ref.User.Map.t;  (** By callee, each newest first. *)
  named : GlobRef.Set_env.t;  (** Every global the bodies name, applied or not. *)
  dictionary_calls : (Occurrence.t * (GlobRef.t * GlobRef.t)) list;
      (** Each application of a singleton class's dictionary, by the
          occurrence of the variable at its head: the class and its one
          method ({!singleton_dictionary_head}). *)
  constructions : (Occurrence.t * bool) list GlobRef.Map_env.t;
      (** Each construction, by its constructor and then its occurrence:
          whether it is a closed term of a shared variant
          ({!is_shared_constant_term}). *)
  matches : (Occurrence.t * Match_kind.t) list Int.Map.t;
      (** Each match, by its number of branches and then its occurrence:
          how it is lowered ({!Match_kind.classify}). *)
}

let empty =
  { calls = Ref.User.Map.empty;
    named = GlobRef.Set_env.empty;
    dictionary_calls = [];
    constructions = GlobRef.Map_env.empty;
    matches = Int.Map.empty }

(* Whether [e] is a closed constructor term of a shared variant with fields:
   built from constructors, literals and erased arguments only, so its value
   is the same every time it is evaluated. *)
let is_shared_constant_term e =
  let rec closed = function
    | MLcons (_, _, ts, _) -> List.for_all closed ts
    | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ | MLdummy _ -> true
    | MLmagic (_, a, _) -> closed a
    | _ -> false
  in
  match e with
  | MLcons (_, (GlobRef.ConstructRef ((kn, i), _) as r), (_ :: _ as ts), _) ->
    Table.is_shared_variant (GlobRef.IndRef (kn, i))
    && (not (Table.is_custom r))
    && List.exists (function MLdummy _ -> false | _ -> true) ts
    && List.for_all closed ts
  | _ -> false

(* [m] with [fact] recorded for the occurrence [occ] in the bucket [key]. *)
let add_keyed key occ fact m =
  GlobRef.Map_env.update key (fun l -> Some ((occ, fact) :: Option.default [] l)) m

(* Whether the call [use args], standing in [lex], builds a typeclass
   instance -- its Rocq type says so ({!Table.builds_instance}): a singleton
   class's method is a function, so its instance's ML type is an arrow, not
   the class -- from no value of [lex]: its only free variables are instance
   parameters, which C++ takes as template arguments ({!binder_is_instance}).
   Such a call is the same value every time it is evaluated. *)
let builds_closed_instance ~lex use args =
  (not (Table.is_custom use.callee))
  && args <> []
  && Table.builds_instance use.callee
  && Escape.IntSet.for_all (binder_is_instance lex) (Escape.free_rels 0 (MLapp (MLglob use, args)))

(* Whether the call [call] of [use], standing in [lex], applies arguments past its
   callee's arity to a head -- the callee applied to the rest, at least one --
   that names no value of [lex]: a function, a handler [case_] combines, say,
   built from nothing the call can change, so the same every time the call is
   evaluated.  Not a custom callee, whose text is no function to keep. *)
let closed_head ~lex use (call : Elaborated_call.t) =
  let n = List.length call.args - List.length call.excess in
  (not (Table.is_custom call.callee))
  && n > 0 && call.excess <> []
  && Escape.IntSet.for_all (binder_is_instance lex)
       (Escape.free_rels 0 (MLapp (MLglob use, List.filteri (fun i _ -> i < n) call.args)))

(* Whether the call [call], standing in [lex], projects a class field
   through its one dictionary argument where that instance was kept
   ({!Translation_types.kept_instance_of_projection}) and its class declares
   the field as a member template: the instance's own method can then be
   called in place of the field's dispatcher. *)
let member_template_projection ~lex (call : Elaborated_call.t) =
  match call.instances with
  | [inst] -> (
    kept_instance_of_projection ~lex call.callee [inst] <> None
    &&
    match resolve_tmeta (instance_class_ty ~lex inst) with
    | Tglob (c, _, _) -> method_is_member_template c call.callee
    | _ -> false )
  | _ -> false

(* The class and its one method, where the variable [i] of [lex] is the
   dictionary of a singleton class: an instance parameter -- a declaration's
   dictionary, or a binder named as an instance -- at the class's type. *)
let singleton_dictionary_head lex i =
  match Lexenv.binder lex i with
  | Some {eb_id; eb_type; eb_role} when eb_role = Lexenv.Dictionary || Common.is_tc_instance_id eb_id -> (
    match resolve_tmeta eb_type with
    | Tglob (c, _, _) -> Option.map (fun m -> (c, m)) (Table.singleton_class_method c)
    | _ -> None )
  | _ -> None

(* What the walk has found so far: the walk's own, never seen outside
   {!structure}. *)
type builder = t ref

(* The ML types a position expects ([expected]) and states ([stated]) for
   the value generated there: the slot translation threads, kept as
   translation keeps it. *)
type position = {expected : ml_type option; stated : ml_type option}

let no_position = {expected = None; stated = None}

(* Where a body is generated: the declaration it is generated as ([caller],
   none for a method of an inductive, which is lowered outside any), the
   type variables it is generated under by name ([scope]), and how many its
   head numbers ([n_outer], past which a let-bound lambda numbers its own). *)
type walker = {
  b : builder;
  n_outer : int;
  caller : GlobRef.t option;
  scope : Id.t list;
  site : site;
}

(* The variables a head of [n] generates under: [T1] .. [Tn]. *)
let head_scope n = List.init n (fun k -> Cpp_ir.Type.positional_id (k + 1))

let walker ?caller ?scope b ~n_outer =
  let scope = match scope with Some s -> s | None -> head_scope n_outer in
  {b; n_outer; caller; scope; site = Body}

let name (b : builder) r = b := {!b with named = GlobRef.Set_env.add r !b.named}

let record w ~position lex use args =
  match classify ~lex use.callee args with
  | roles ->
    let call = of_roles use args roles in
    let planned =
      match
        instantiate ~lex ~expected_ml:position.expected ~stated_ml:position.stated ~caller:w.caller
          ~scope:w.scope call
      with
      | inst -> Some inst
      | exception e when CErrors.noncritical e -> None
    in
    let others = Option.default [] (Ref.User.Map.find_opt use.callee !(w.b).calls) in
    let entry =
      { occurrence = Global_use.occurrence use;
        roles;
        planned;
        site = w.site;
        closed_instance = builds_closed_instance ~lex use args;
        static_projection = static_projection ~lex use args;
        closed_head = closed_head ~lex use call;
        member_template = member_template_projection ~lex call }
    in
    w.b := {!(w.b) with calls = Ref.User.Map.add use.callee (entry :: others) !(w.b).calls};
    planned
  (* A callee with no type is never translated as a call: the traversal
     reaches it by another route or not at all. *)
  | exception Not_found -> None

(* Where the [i]th regular argument of [inst] is generated: the substituted
   parameter at its position, or, where substitution erased it, the one the
   callee declares (translation's [gen_call_args]). *)
let argument_position (inst : Elaborated_call.instantiated) i =
  let param_index = Param_pos.of_regular ~leading:(Elaborated_call.leading_params inst.call) i in
  let subst_index =
    if Table.is_inline_custom inst.call.callee then Some (Param_pos.subst_at_declared param_index)
    else inst.subst_index_of_orig param_index
  in
  match subst_index with
  | Some i -> Param_pos.nth inst.params i
  | None -> (
    match Param_pos.nth inst.params_orig param_index with
    | Some t when not (erased_by_extraction t) -> Some t
    | _ -> None )

(* The position of each argument of a global call planned as [planned], in
   a call at [position]: a regular argument is expected at its parameter's
   type unless that has an erasure in it, and stated at it; one past the
   callee's arity is applied to the result, and inherits the call's
   position; any other, and every argument of a call not planned, is
   generated with none. *)
let argument_positions ~position planned =
  match planned with
  | None -> fun _ -> no_position
  | Some (inst : Elaborated_call.instantiated) ->
    let roles = Array.of_list inst.call.roles in
    let regular_index =
      let k = ref (-1) in
      Array.map (function Elaborated_call.Regular -> incr k; !k | _ -> -1) roles
    in
    fun i ->
      if i >= Array.length roles then no_position
      else
        match roles.(i) with
        | Elaborated_call.Regular ->
          let param = argument_position inst regular_index.(i) in
          let expected =
            match param with
            | Some t when not (ml_type_contains_erased t) -> Some t
            | _ -> position.expected
          in
          {expected; stated = param}
        | Elaborated_call.Excess -> position
        | Elaborated_call.Dictionary | Elaborated_call.Erased_dictionary | Elaborated_call.Dropped ->
          no_position

(* The position of the body of a lambda of [n] binders at [position]: its
   expected type past [n] arrows, where that leaves a resolved codomain;
   its stated type as it was. *)
let lambda_body_position ~n position =
  let rec strip n ty =
    if n = 0 then Some ty
    else match resolve_tmeta ty with Tarr (_, cod) -> strip (n - 1) cod | _ -> None
  in
  let expected =
    match position.expected with
    | Some fn_ty -> (
      match strip n fn_ty with
      | Some cod -> (
        match resolve_tmeta cod with
        | Tdummy _ | Tunknown | Tmeta {contents = None} | Topen _ -> position.expected
        | _ -> Some cod )
      | None -> position.expected )
    | None -> None
  in
  {position with expected}

let binder role (x, ty) = {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = role}

(* The binders [ids], innermost first, as [collect_lams] returns them. *)
let push role ids lex = Lexenv.push (List.map (binder role) ids) lex

(* [walk w ~position lex e] elaborates the calls of [e], generated in [lex]
   at [position], each at the position translation generates it at: a
   recursion translation makes with no slot of its own resets it. *)
let rec walk w ?(position = no_position) lex e =
  let go ?(position = no_position) lex e = walk w ~position lex e in
  match e with
  | MLapp (MLglob use, args) ->
    walk_use w lex use;
    let at = argument_positions ~position (record w ~position lex use args) in
    List.iteri (fun i a -> go ~position:(at i) lex a) args
  (* A local callee's arguments are generated at the call's position. *)
  | MLapp (f, args) ->
    ( match f with
    | MLrel (i, occ) ->
      Option.iter
        (fun head -> w.b := {!(w.b) with dictionary_calls = (occ, head) :: !(w.b).dictionary_calls})
        (singleton_dictionary_head lex i)
    | _ -> () );
    go lex f;
    List.iter (go ~position lex) args
  | MLlam _ as e ->
    let ids, body = Mlutil.collect_lams e in
    List.iter (fun (_, ty) -> walk_type w lex ty) ids;
    go ~position:(lambda_body_position ~n:(List.length ids) position) (push Lexenv.Value ids lex) body
  (* An alias of a polymorphic function is not bound but put in place of its
     uses ({!Translation_support.let_lambda}), and its calls are those of
     what it abbreviates, at the arguments each use gives it.  A lambda that
     is bound is generated as a function of its own, at no position. *)
  | MLletin (x, ty, (MLlam _ as a), body, _) -> (
    walk_type w lex ty;
    match let_lambda ~lex ~n_outer:w.n_outer ty a body with
    | Inlined body -> go ~position lex body
    | Bound | At_instance _ | Lifted ->
      go lex a;
      go ~position (push Lexenv.Value [(x, ty)] lex) body )
  | MLletin (x, ty, a, body, _) ->
    walk_type w lex ty;
    go ~position:{position with expected = Some ty} lex a;
    go ~position (push Lexenv.Value [(x, ty)] lex) body
  | MLcons (ty, r, args, occ) ->
    w.b := {!(w.b) with constructions = add_keyed r occ (is_shared_constant_term e) !(w.b).constructions};
    walk_type w lex ty;
    List.iter (go ~position:{expected = None; stated = position.stated} lex) args
  | MLtuple args -> List.iter (go lex) args
  | MLcase (ty, scrut, branches, occ) ->
    let kind = Match_kind.classify ty branches in
    w.b :=
      { !(w.b) with
        matches =
          Int.Map.update (Array.length branches)
            (fun l -> Some ((occ, kind) :: Option.default [] l))
            !(w.b).matches };
    walk_type w lex ty;
    go lex scrut;
    (* A branch's result type is written under its binders: a custom match
       declares it as the type its arm returns. *)
    Array.iter
      (fun (ids, rty, _, body) ->
        List.iter (fun (_, ty) -> walk_type w lex ty) ids;
        let lex = push Lexenv.Value (List.rev ids) lex in
        walk_type w lex rty;
        go ~position lex body )
      branches
  | MLfix (_, fs, defs, _, _) ->
    Array.iter (fun (_, ty) -> walk_type w lex ty) fs;
    (* The last function of the group is the innermost binder. *)
    let fs = List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs) in
    Array.iter (go (push Lexenv.Value fs lex)) defs
  | MLmagic (_, e, _) -> go ~position lex e
  | MLparray (elems, def) ->
    Array.iter (go lex) elems;
    go lex def
  (* A global named but not applied -- a function passed as a value -- is
     translated as its call with no arguments. *)
  | MLglob use ->
    walk_use w lex use;
    ignore (record w ~position lex use [])
  | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ -> ()

and walk_use w lex use =
  name w.b use.callee;
  Global_use.iter_types (walk_type w lex) use

(* A custom type applied to a term -- a fixed-size array to its length --
   has calls of its own, translated where the type is converted, in no
   declaration's name. *)
and walk_type w lex ty =
  match resolve_tmeta ty with
  | Tglob (g, tys, args) ->
    List.iter (walk_type w lex) tys;
    if Table.is_custom g then List.iter (walk {w with caller = None; site = Type_term} lex) args
  | Tarr (dom, cod) ->
    walk_type w lex dom;
    walk_type w lex cod
  | Tapp (_, tys) -> List.iter (walk_type w lex) tys
  | _ -> ()

(* The variables a declaration of type [ty] is generated under: the type
   variables of its head, which a let-bound lambda in its body is numbered
   past ({!Local_types}). *)
let head_variables ty = Mlutil.IntSet.fold max (Mlutil.ml_tvars ty) 0

(* A declaration's own parameters are bound as its parameters, at the types
   its body is generated with ({!Translation_support.reconcile_parameter_type}):
   the class-typed ones are its dictionaries
   ({!Translation_state.parameter_role}).  Translation unifies a parameter's
   annotation with the declaration's type when it generates the head; an
   annotation that is still a bare metavariable is solved to the declared
   type there, so that is the type read here, without solving anything.  The
   lambdas bind every domain: Core eta-expands each definition
   ({!Normalize.eta_expand}), so a definition that is another function,
   [add := Z.add], calls it; only an axiom's or exception's parameters are
   named here, with no body to bind them. *)
let declaration_scope ty body =
  let ty = Mlutil.type_simpl ty in
  let params, body = declared_parameters ty body in
  let parameter (x, body_ty) sig_ty =
    let body_ty =
      match resolve_tmeta body_ty with Tmeta {contents = None} | Topen _ -> sig_ty | t -> t
    in
    let ty = reconcile_parameter_type body_ty sig_ty in
    binder (parameter_role ty) (x, ty)
  in
  (Lexenv.push (List.map2 parameter params (List.rev (Ml_type_util.ml_domains ty))) Lexenv.empty, body)

(* [e], standing in [lex] under a head of [n_outer] type variables, with
   every let-bound lambda as translation generates it
   ({!Translation_support.let_lambda}): an alias it inlines put in place of
   its uses, one used at a single instance bound at it, and one bound as a
   value given a binder for every value arrow of its type
   ({!Translation_support.eta_bound_lambda}). *)
let rec inline_aliases ~n_outer lex e =
  let go = inline_aliases ~n_outer in
  let under ids body = go (push Lexenv.Value ids lex) body in
  match e with
  | MLletin (x, ty, (MLlam _ as a), body, occ) -> (
    match let_lambda ~lex ~n_outer ty a body with
    | Inlined body -> go lex body
    | At_instance inst ->
      let subst = Mlutil.type_subst_list inst in
      go lex (MLletin (x, subst ty, Mlutil.ast_map_types subst a, body, occ))
    | Bound -> MLletin (x, ty, go lex (Translation_support.eta_bound_lambda ty a), under [(x, ty)] body, occ)
    | Lifted -> MLletin (x, ty, go lex a, under [(x, ty)] body, occ) )
  | MLletin (x, ty, a, body, occ) -> MLletin (x, ty, go lex a, under [(x, ty)] body, occ)
  | MLlam (x, ty, body) -> MLlam (x, ty, under [(x, ty)] body)
  | MLcase (ty, scrut, branches, occ) ->
    MLcase
      ( ty,
        go lex scrut,
        Array.map (fun (ids, rty, pat, body) -> (ids, rty, pat, under (List.rev ids) body)) branches,
        occ )
  | MLfix (i, fs, defs, cofix, occ) ->
    let fs' = List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs) in
    MLfix (i, fs, Array.map (under fs') defs, cofix, occ)
  | e -> Mlutil.ast_map (go lex) e

let generated_definition ty body =
  match body with
  | MLaxiom _ | MLexn _ -> body
  | _ ->
    let ty' = Mlutil.type_simpl ty in
    let params, _ = collect_typed_lams ty' body in
    let lex, inner = declaration_scope ty body in
    Mlutil.named_lams params (inline_aliases ~n_outer:(head_variables ty') lex inner)

(* A declaration's calls, read in that scope. *)
let declaration ?caller ?scope b ty body =
  let lex, body = declaration_scope ty body in
  let ty = Mlutil.type_simpl ty in
  let w = walker ?caller ?scope b ~n_outer:(head_variables ty) in
  walk_type w Lexenv.empty ty;
  walk w lex body

(* A constant typed by a name that stands for arrows -- an instance of a
   single-method class is typed by the class -- is generated eta-expanded to
   those arrows ({!Gen_functions.gen_spec}): the slot it initialises is a
   function of the full signature, which no partial application fills. *)
let constant_at_alias ~caller b ty body =
  let ty = Mlutil.type_simpl ty in
  let body = match body with MLmagic (_, b, _) -> b | b -> b in
  if Ml_type_util.ml_domains ty = [] then
    match Ml_type_util.eta_expand_to (Ml_type_util.expand_ml_fun_alias ty) body with
    | expanded when expanded != body -> walk (walker ~caller b ~n_outer:(head_variables ty)) Lexenv.empty expanded
    | _ -> ()

(* An instance's methods are generated from its record's fields not as
   written but as {!Instance_methods} elaborates them -- expanded to the arity
   the class declares, or, a function named point-free, applied to
   parameters of its own -- and under the instance's own parameters, so those
   are the bodies the calls inside them are elaborated in.  A method that
   binds no parameter but erased ones and is applied to parameters of its
   own is generated as that application alone ({!Gen_instances}), so that is
   the only body of it walked: the body as written shares its matches'
   occurrences with the application, which pushes the arguments into a
   single-branch match ({!Mlutil.canonical_app}).  The record as written is
   walked too, for the globals it names alone. *)
let instance_methods b name body ty =
  Option.iter
    (fun (lam_params, methods) ->
      let lex =
        Lexenv.push (List.rev_map (fun (x, ty) -> binder (parameter_role ty) (Id x, ty)) lam_params) Lexenv.empty
      in
      let w = walker ~caller:name b ~n_outer:(head_variables ty) in
      List.iter
        (fun (m : Instance_methods.method_) ->
          let params, inner = Instance_methods.params m in
          let eta =
            if List.for_all (fun p -> p.Instance_methods.erased) params then Instance_methods.eta_call m inner
            else None
          in
          match eta with
          | Some (eta, call) -> walk w (push Lexenv.Value (List.rev_map (fun (x, ty) -> (Id x, ty)) eta) lex) call
          | None -> walk w lex m.body )
        methods )
    (Instance_methods.methods name body ty)

(* A call converts its callee's declared type, instantiated, so the terms
   custom types are applied to there -- [not] in [{x = y} + {x <> y}] -- are
   elaborated with it; the unit's own declarations' types are walked with
   them, the others' here, as closed types.  Walking one may name another
   global, whose type is then walked in turn. *)
let rec foreign_types b ~walked =
  let pending = GlobRef.Set_env.diff !b.named walked in
  if not (GlobRef.Set_env.is_empty pending) then begin
    let w = {(walker b ~n_outer:0) with site = Type_term} in
    GlobRef.Set_env.iter (fun r -> Option.iter (walk_type w Lexenv.empty) (find_type_opt r)) pending;
    foreign_types b ~walked:(GlobRef.Set_env.union walked pending)
  end

(* [f] walking a body no call is generated from -- an instance's record as
   written, where its methods are generated as {!Instance_methods}
   elaborates them -- for the globals it names alone. *)
let names_only (b : builder) f =
  let scratch = ref {empty with named = !b.named} in
  f scratch;
  b := {!b with named = !scratch.named}

(* A function generated as a method of its inductive is generated from its
   body renumbered so the inductive's variables come first
   ({!Method_registry.renumbering}), and nowhere as written: outside any
   declaration, under the inductive's variables and then its own, each
   spelled as the method spells it ({!Gen_inductives.method_scope}). *)
let method_ b vars (_, body, ty, this_pos) =
  let r = Method_registry.renumbering ~num_ind_vars:(List.length vars) ~this_pos ty in
  let scope = vars @ head_scope (List.length r.Method_registry.extra) in
  declaration ~scope b (Method_registry.renumber_type r ty) (Method_registry.renumber_body r body)

let structure ~methods struc =
  let b = ref empty in
  let defined = ref GlobRef.Set_env.empty in
  let define r = defined := GlobRef.Set_env.add r !defined in
  let closed_type = walk_type {(walker b ~n_outer:0) with site = Type_term} Lexenv.empty in
  let inductive ind = Array.iter (fun p -> Array.iter (List.iter closed_type) p.ip_types) ind.ind_packets in
  let as_methods =
    let acc = ref GlobRef.Set_env.empty in
    Modutil.struct_iter
      (function
        | Dind (kn, ind) -> List.iter (fun (_, (r, _, _, _)) -> acc := GlobRef.Set_env.add r !acc) (methods kn ind)
        | Dterm _ | Dfix _ | Dtype _ -> () )
      ignore ignore struc;
    !acc
  in
  let as_method r = GlobRef.Set_env.mem r as_methods in
  Modutil.struct_iter
    (function
      | Dterm (r, _, _) when as_method r -> define r
      | Dterm (r, body, ty) ->
        define r;
        let written b =
          declaration ~caller:r b ty body;
          constant_at_alias ~caller:r b ty body
        in
        if Instance_methods.methods r body ty <> None then names_only b written else written b;
        instance_methods b r body ty
      | Dfix fds ->
        List.iter
          (fun fd ->
            define fd.fd_ref;
            if not (as_method fd.fd_ref) then declaration ~caller:fd.fd_ref b fd.fd_type fd.fd_body )
          fds
      | Dind (kn, ind) ->
        inductive ind;
        List.iter (fun (vars, candidate) -> method_ b vars candidate) (methods kn ind)
      | Dtype (_, _, ty) -> closed_type ty )
    (function
      | Sind (_, ind) -> inductive ind
      | Stype (_, _, ty) -> Option.iter closed_type ty
      | Sval (_, _, ty) -> closed_type ty )
    ignore struc;
  foreign_types b ~walked:!defined;
  !b

let referenced t = GlobRef.Set_env.elements t.named

let installed = State.cell State.Unit empty

type tally = {found : int; recomputed : int; taken : int; live : int}

let no_tally = {found = 0; recomputed = 0; taken = 0; live = 0}
let tally = State.cell State.Unit no_tally

(* Whether the unit's elaborations are installed: planning translates
   bodies before they are. *)
let walked = State.cell State.Unit false

let install t =
  installed := t;
  walked := true;
  tally := no_tally

(* A body's annotations may be rewritten before it is translated, which
   rebuilds every node, so the use's occurrence is what identifies the
   application; one a rewrite duplicated is found only where every copy has
   the same roles. *)
let roles t use n =
  match Ref.User.Map.find_opt use.callee t.calls with
  | None -> None
  | Some entries -> (
    let occurrence = Global_use.occurrence use in
    match
      List.filter
        (fun e -> Occurrence.equal e.occurrence occurrence && Int.equal (List.length e.roles) n)
        entries
    with
    | [] -> None
    | e :: rest when List.for_all (fun e' -> List.equal ( = ) e.roles e'.roles) rest ->
      Some e.roles
    | _ -> None )

(* Whether [t] reached the use, as an application to fewer than [n]
   arguments: translation applied it to the rest itself, extending it to the
   arity its context expects -- [fun _ no => length no], simplified to [fun _
   => length], gets its [no] back -- and a call translation built is
   elaborated where it is translated. *)
let extended t use n =
  match Ref.User.Map.find_opt use.callee t.calls with
  | None -> false
  | Some entries ->
    let occurrence = Global_use.occurrence use in
    List.exists (fun e -> Occurrence.equal e.occurrence occurrence && List.length e.roles < n) entries

let elaboration ~lex use args =
  let elaborate () = elaborate_arguments ~lex use args in
  let from_core roles =
    let call = of_roles use args roles in
    if Probe.checking () && not (Elaborated_call.same_roles call (elaborate ())) then
      CErrors.anomaly
        Pp.(
          str "Crane: a call to " ++ str (Table.kername_of_global use.callee)
          ++ str " elaborated from Core disagrees with its elaboration where it is translated." );
    call
  in
  match Common.get_phase () with
  | Common.Plan -> (
    match roles !installed use (List.length args) with
    | Some roles -> from_core roles
    | None -> elaborate () )
  | Common.Emit -> (
    match roles !installed use (List.length args) with
    | Some roles ->
      tally := {!tally with found = !tally.found + 1};
      from_core roles
    | None ->
      tally := {!tally with recomputed = !tally.recomputed + 1};
      if not (extended !installed use (List.length args)) then
        Probe.violation "elaborated calls"
          Pp.(
            str "a call to " ++ str (Table.kername_of_global use.callee)
            ++ str " is translated where Core elaboration did not reach it." );
      elaborate () )

(* The instantiation planned for the application, with [n] arguments, that
   names its callee by [use]: [`Planned] where every entry the walk made
   there planned one and all agree, [`Ambiguous] with the sites of the
   entries where they do not or one failed, [`Unwalked] where the walk made none. *)
let planned t use n =
  match Ref.User.Map.find_opt use.callee t.calls with
  | None -> `Unwalked
  | Some entries -> (
    let occurrence = Global_use.occurrence use in
    match
      List.filter
        (fun e -> Occurrence.equal e.occurrence occurrence && Int.equal (List.length e.roles) n)
        entries
    with
    | [] -> `Unwalked
    | {planned = Some p; _} :: rest
      when List.for_all
             (function
               | {planned = Some p'; _} -> Elaborated_call.same_instantiation p p'
               | {planned = None; _} -> false )
             rest ->
      `Planned p
    | entries -> `Ambiguous (List.map (fun (e : entry) -> e.site) entries) )

let instantiation ~lex ~expected_ml ~stated_ml ~caller ~scope use args =
  let call = elaboration ~lex use args in
  let live () = instantiate ~lex ~expected_ml ~stated_ml ~caller ~scope call in
  let describe what =
    Pp.(str "a call to " ++ str (Table.kername_of_global use.callee) ++ str what)
  in
  let from_core p =
    let p = Elaborated_call.at_call p call in
    if Probe.checking () then begin
      let agrees = Elaborated_call.same_instantiation p (live ()) in
      Probe.hit "elab-plan" (fun () -> if agrees then "agree" else "disagree " ^ Table.kername_of_global use.callee);
      if not agrees then
        Probe.violation "planned instantiations"
          (describe " is instantiated where it is translated otherwise than Core planned it.")
    end;
    p
  in
  match Common.get_phase () with
  | Common.Plan -> (
    match planned !installed use (List.length args) with
    | `Planned p -> from_core p
    | `Ambiguous _ | `Unwalked -> live () )
  | Common.Emit -> (
    match planned !installed use (List.length args) with
    | `Planned p ->
      tally := {!tally with taken = !tally.taken + 1};
      from_core p
    | (`Ambiguous _ | `Unwalked) as why ->
      tally := {!tally with live = !tally.live + 1};
      Probe.hit "elab-plan" (fun () ->
          (match why with
           | `Ambiguous sites ->
             "ambiguous "
             ^ String.concat "," (List.map (function Body -> "body" | Type_term -> "type") sites)
             ^ " "
           | `Unwalked -> "unwalked ")
          ^ Table.kername_of_global use.callee);
      if not (extended !installed use (List.length args)) then
        Probe.violation "planned instantiations"
          (describe
             ( match why with
             | `Ambiguous _ -> " has no single instantiation planned for it."
             | `Unwalked -> " is translated where Core elaboration did not reach it." ) );
      live () )

let planned_instantiation use args =
  let n = List.length args in
  match (roles !installed use n, planned !installed use n) with
  | Some roles, `Planned p -> Some (Elaborated_call.at_call p (of_roles use args roles))
  | _ -> None

(* [lookup what ~equal ~live planned] -- the answer the installed walk
   planned ([planned], [None] where it planned none or its entries
   disagree), checked under [CRANE_CHECK_IR] against [live ()], the answer
   the traversal's own environment gives, which is taken where the walk
   planned none or is not installed yet. *)
let lookup what ~equal ~live planned =
  let phase = match Common.get_phase () with Common.Plan -> "plan " | Common.Emit -> "" in
  match planned with
  | Some _ when not !walked -> live ()
  | Some p ->
    Probe.hit "elab-fact" (fun () -> phase ^ String.map (function ' ' -> '_' | c -> c) what ^ " planned");
    if Probe.checking () && not (equal p (live ())) then
      Probe.violation what (Pp.str "the answer translation's environment gives differs from Core's");
    p
  | None ->
    Probe.hit "elab-fact" (fun () -> phase ^ String.map (function ' ' -> '_' | c -> c) what ^ " live");
    live ()

(* The one value the answers all give, if they agree on one. *)
let agreed equal = function
  | [] -> None
  | a :: rest -> if List.for_all (equal a) rest then Some a else None

let same_head (c, m) (c', m') = GlobRef.CanOrd.equal c c' && GlobRef.CanOrd.equal m m'


(* What every entry the walk made for the application, with [n] arguments,
   naming its callee by [use] says of it ([fact]), if they all say one
   thing. *)
let entry_fact ~equal fact use n =
  match Ref.User.Map.find_opt use.callee !installed.calls with
  | None -> None
  | Some entries ->
    let occurrence = Global_use.occurrence use in
    agreed equal
      (List.filter_map
         (fun e ->
           if Occurrence.equal e.occurrence occurrence && Int.equal (List.length e.roles) n then Some (fact e)
           else None )
         entries )

let closed_instance_call ~lex use args =
  lookup "closed instance calls" ~equal:Bool.equal
    ~live:(fun () -> builds_closed_instance ~lex use args)
    (entry_fact ~equal:Bool.equal (fun e -> e.closed_instance) use (List.length args))

let static_projection_call ~lex use args =
  let equal = Option.equal Elaborated_call.same_static_projection in
  lookup "static projections" ~equal
    ~live:(fun () -> static_projection ~lex use args)
    (entry_fact ~equal (fun e -> e.static_projection) use (List.length args))

let closed_head_call ~lex use args =
  lookup "closed heads" ~equal:Bool.equal
    ~live:(fun () -> closed_head ~lex use (elaborate_arguments ~lex use args))
    (entry_fact ~equal:Bool.equal (fun e -> e.closed_head) use (List.length args))

let member_template_call ~lex use args =
  lookup "member template projections" ~equal:Bool.equal
    ~live:(fun () -> member_template_projection ~lex (elaborate_arguments ~lex use args))
    (entry_fact ~equal:Bool.equal (fun e -> e.member_template) use (List.length args))

let singleton_dictionary_call ~live occ =
  let planned =
    match List.filter_map (fun (o, h) -> if Occurrence.equal o occ then Some h else None) !installed.dictionary_calls with
    | [] -> Some None
    | heads -> Option.map Option.make (agreed same_head heads)
  in
  lookup "singleton dictionary calls" ~equal:(Option.equal same_head) ~live planned

let shared_constant = function
  | MLcons (_, r, _, occ) as e ->
    let planned =
      match GlobRef.Map_env.find_opt r !installed.constructions with
      | None -> None
      | Some l ->
        agreed Bool.equal (List.filter_map (fun (o, f) -> if Occurrence.equal o occ then Some f else None) l)
    in
    lookup "shared constants" ~equal:Bool.equal ~live:(fun () -> is_shared_constant_term e) planned
  | _ -> false

let match_kind ty branches occ =
  let planned =
    match Int.Map.find_opt (Array.length branches) !installed.matches with
    | None -> None
    | Some l -> agreed ( = ) (List.filter_map (fun (o, k) -> if Occurrence.equal o occ then Some k else None) l)
  in
  lookup "match kinds" ~equal:( = ) ~live:(fun () -> Match_kind.classify ty branches) planned

let report () =
  let n = Ref.User.Map.fold (fun _ l acc -> acc + List.length l) !installed.calls 0 in
  Printf.sprintf
    "elaborated calls: %d planned; emission found %d, elaborated %d itself; took %d instantiations planned, \
     %d instantiated itself"
    n !tally.found !tally.recomputed !tally.taken !tally.live
