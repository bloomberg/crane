(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An instance's methods as Core elaborates them.  See
    [instance_methods.mli]. *)

open Names
open Util
open Type_util
open Core_query

type layers = {
  inner_ty : Core.Type.t;
  inner_body : Core.Expr.t;
  dictionaries : (Id.t * Core.Type.t) list;
  lam_params : (Id.t * Core.Type.t) list;
}

let layers ty body =
  (* For parameterized instances, strip Core.Type.Arrow/Core.Expr.Lambda layers to get to the inner
     typeclass type and constructor body. Example: numOption has type
     Core.Type.Arrow(Core.Type.Erased,
     Core.Type.Arrow(Core.Type.Global_app(Numeric,[A],[]),
     Core.Type.Global_app(Numeric,[option A],[]))) and body Core.Expr.Lambda(_,
     Core.Type.Erased, Core.Expr.Lambda(_, Core.Type.Global_app(Numeric,...),
     Core.Expr.Construct(...))) *)
  let rec strip_outer_layers ty body tc_acc lam_acc =
    let stop ty body =
      {inner_ty = ty; inner_body = body; dictionaries = List.rev tc_acc; lam_params = List.rev lam_acc}
    in
    match (ty, body) with
    | Core.Type.Arrow {parameter = arg_ty;
                       result = rest_ty}, Core.Expr.Lambda {parameter = core_id;
                                                            parameter_type = lam_ty;
                                                            body = rest_body} ->
      if erased_by_extraction arg_ty then
        (* Erased type parameter -- skip (template params are inferred from
           type variables in the return type) *)
        strip_outer_layers rest_ty rest_body tc_acc ((Core_util.id_of_binder_name core_id, lam_ty) :: lam_acc)
      else if parameter_role arg_ty = Dictionary then
        (* The binder is typed by the class, as the instance's type writes
           it: a singleton class's binder is annotated with the class
           unfolded, which no call through it can read the carrier from. *)
        let instance_name = Common.tc_instance_id (List.length tc_acc) in
        strip_outer_layers rest_ty rest_body ((instance_name, arg_ty) :: tc_acc)
          ((instance_name, arg_ty) :: lam_acc)
      else (* Not a type param or typeclass -- stop stripping *)
        stop ty body
    | Core.Type.Arrow {parameter = arg_ty; _}, _
      when erased_by_extraction arg_ty || Table.is_typeclass_type arg_ty ->
      (* An instance eta-reduced past its own parameters -- [TFunctor_pair
         := ft_pair] -- takes them all the same. *)
      let arg =
        if erased_by_extraction arg_ty then Core.Expr.Erased_value Core.Erasure_reason.Type_argument else
          Core.Expr.fresh_rel 1 in
      let applied =
        match Core_util.ast_lift 1 body with
        | Core.Expr.Apply {callee = f; arguments = args} -> Core.Expr.Apply {callee = f; arguments = args @ [arg]}
        | f -> Core_normalize.apply f [arg]
      in
      let body =
        Core.Expr.Lambda
          {parameter = Core.Binder_name.Source (Id.of_string "x"); parameter_type = arg_ty; body = applied} in
      strip_outer_layers ty body tc_acc lam_acc
    | _ -> stop ty body
  in
  strip_outer_layers ty body [] []

let record_body name class_ref inner_ty lam_params inner_body =
  let inner_body =
    match inner_body with
    | Core.Expr.Coerce {value = b; _}
    | Core.Expr.Boxed_value {value = b; _}
    | Core.Expr.Lambda_group_barrier {value = b; _} -> b
    | b -> b
  in
  let as_method m = function
    | Core.Expr.Fixpoint {members = [|{body = c; _}|]; _} | Core.Expr.Cofixpoint {members = [|{body = c; _}|]; _}
      when lam_params = [] ->
      let n_class = Type_util.projection_class_arity m in
      let erased = List.init n_class (fun _ -> Core.Expr.Erased_value Core.Erasure_reason.Type_argument) in
      Core_util.ast_subst
        (Core.Expr.Apply
           { callee = Core.Expr.Global (Core_util.open_reference m);
             arguments = erased @ [Core.Expr.Global (Core_util.open_reference name)] })
        c
    | b -> b
  in
  match (Table.singleton_class_method class_ref, inner_body) with
  | Some _, (Core.Expr.Construct _ as b) -> b
  | Some m, b ->
    Core.Expr.Construct {result_type = inner_ty;
                         constructor = class_ref;
                         arguments = [as_method m b];
                         occurrence = Core.Occurrence.fresh ()}
  | None, b -> b

let record_type_args (cons_ty : Core.Type.t) type_args =
  let erased t =
    match resolve_meta t with
    | Core.Type.Unknown | Core.Type.Erased _ -> true
    | _ -> false
  in
  match cons_ty with
  | Core.Type.Global_app {type_arguments = ta; _} when ta <> [] ->
    List.mapi
      (fun i t ->
        if not (erased t) then t
        else
          match List.nth_opt type_args i with
          | Some d when not (erased d) -> d
          | _ -> t )
      ta
  | _ -> type_args

let rec class_type ty =
  match ty with
  | Core.Type.Arrow {parameter = d; result = rest} when erased_by_extraction d || Table.is_typeclass_type d ->
    class_type rest
  | Core.Type.Meta {contents = Some t} -> class_type t
  | t -> t

let instance_tvars ty inner_ty =
  (* The classes of the instance's dictionary parameters.  Read off the
     instance's type, not its binders: a singleton class's dictionary binder
     is annotated with the class unfolded. *)
  let dict_tys =
    let rec dicts acc = function
      | Core.Type.Arrow {parameter = a; result = b} ->
        dicts (if Table.is_typeclass_type a then a :: acc else acc) b
      | Core.Type.Meta {contents = Some t} -> dicts acc t
      | _ -> List.rev acc
    in
    dicts [] ty
  in
  let dict_vars =
    let rec vars acc = function
      | Core.Type.Variable {variable = i; _} | Core.Type.Variable_app {head = i; arguments = []} -> i :: acc
      | Core.Type.Variable_app {head = i; arguments = tys} -> List.fold_left vars (i :: acc) tys
      | Core.Type.Global_app {type_arguments = tys; _} -> List.fold_left vars acc tys
      | Core.Type.Arrow {parameter = a; result = b} -> vars (vars acc a) b
      | Core.Type.Meta {contents = Some t} -> vars acc t
      | _ -> acc
    in
    List.fold_left vars [] dict_tys
  in
  let rec collect_core_tvars acc = function
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i} ->
      if List.mem i acc then
        acc
      else
        i :: acc
    (* A family parameter -- [Functor (box E)] -- is written applied, and is
       one of the instance's variables all the same.  Not a carrier one of
       its dictionaries is about: [Monad m] reaches [m] through the
       dictionary, and the instance declares nothing for it. *)
    | Core.Type.Variable_app {head = i; arguments = tys} ->
      let acc =
        if List.mem i acc || List.mem i dict_vars then acc else i :: acc
      in
      List.fold_left collect_core_tvars acc tys
    | Core.Type.Arrow {parameter = t1; result = t2} -> collect_core_tvars (collect_core_tvars acc t1) t2
    | Core.Type.Global_app {type_arguments = tys; _} -> List.fold_left collect_core_tvars acc tys
    | Core.Type.Meta {contents = Some t} -> collect_core_tvars acc t
    | _ -> acc
  in
  (* A variable a dictionary parameter mentions is one of the instance's too,
     though the class arguments may not: [via {A B C} `{Conv A B} `{Conv B C}
     : Sz (A * C)] binds [B] for its constraints alone.  Not one a dictionary
     is about as its carrier -- see [dict_vars]. *)
  let constraint_args = function
    | Core.Type.Global_app {head = cls; type_arguments = args; _} ->
      List.filteri (fun i _ -> not (Table.is_hkt_param cls i)) args
    | _ -> []
  in
  match inner_ty with
  | Core.Type.Global_app {type_arguments = type_args; _} ->
    List.sort compare
      (List.fold_left collect_core_tvars []
         (type_args @ List.concat_map constraint_args dict_tys))
  | _ -> []

let tvar_count ~instance_tvars ty type_args =
  List.fold_left
    (fun n t -> max n (Core_util.type_maxvar t))
    (max (List.length instance_tvars) (Core_util.type_maxvar ty))
    type_args

type instance = {
  class_ref : GlobRef.t;
  type_args : Core.Type.t list;
  tvar_count : int;
}

(* [ty] split into the parameters a field declared at [declared_arity] value
   arrows takes -- erased and class-typed ones riding along uncounted -- and
   the rest, folded back into the result type. *)
let split_at_arity declared_arity ty =
  let args, ret = get_args_and_ret [] ty in
  let rec split n acc = function
    | t :: rest
      when erased_by_extraction t || Table.is_typeclass_type t ->
      split n (t :: acc) rest
    | t :: rest when n > 0 -> split (n - 1) (t :: acc) rest
    | surplus -> (List.rev acc, surplus)
  in
  let kept, surplus = split declared_arity [] args in
  ( kept,
    List.fold_right (fun a r -> Core.Type.Arrow {parameter = a; result = r}) surplus ret )

(* A promoted type variable -- [Core.Type.Variable 3] for [edge] in [Graph] -- replaced by
   the concrete type the instance gives it.  Only the variables beyond the
   ones the instance binds -- its template parameters, and the carriers it
   reaches through a dictionary -- are, to avoid disturbing regular type
   variable references. *)
let subst_promoted_tvars {type_args; tvar_count = nb_sign_keeps; _} ty =
  if List.length type_args > nb_sign_keeps then
    let rec subst = function
      | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = j}
        when j > nb_sign_keeps && j <= List.length type_args ->
        List.nth type_args (j - 1)
      | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = subst a; result = subst b}
      | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
        Core.Type.Global_app {head = r; type_arguments = List.map subst l; index_arguments = a}
      | Core.Type.Meta {contents = Some t} -> subst t
      | Core.Type.Meta _ as t -> t
      | t -> t
    in
    subst ty
  else
    ty

type method_ = {
  field_core_ty : Core.Type.t;
  subst_args : Core.Type.t list;
  subst_ty : Core.Type.t;
  n_method_tvars : int;
  declared_arity : int;
  body : Core.Expr.t;
}

let args_and_ret m = split_at_arity m.declared_arity m.subst_ty
let declared_args_and_ret m = split_at_arity m.declared_arity m.field_core_ty

let prepare_method ?(freshen = true) ({class_ref; type_args; tvar_count = instance_tvar_count} as inst)
    method_ref field_core_ty field_body =
  (* Strip coercion wrappers from the field body -- promoted dependent
     records produce Core.Expr.Coerce due to Core.Type.Variable/Core.Type.Global_app mismatches. *)
  let rec strip_magic = function
    | Core.Expr.Coerce {value = b; _}
    | Core.Expr.Boxed_value {value = b; _}
    | Core.Expr.Lambda_group_barrier {value = b; _} ->
      strip_magic b
    | b -> b
  in
  (* The method is generated more than once -- declared, then defined --
     and each generation gives the body's open annotations identities of its
     own. *)
  (* A field body is substituted into ([record_body]) and applied to
     invented parameters ([layers]) after {!Core_normalize.structure} ran:
     canonical again only once its spines are read again. *)
  let field_body = Core_normalize.spine (strip_magic field_body) in
  let field_body = if freshen then Core_util.freshen_metas field_body else field_body in
  (* The class field's type loses the method's own quantifier; give it back
     before renumbering and substituting.  The instance's class arguments are
     substituted into the result further down ([subst_ty]), which gives the
     concrete type (e.g. [bool] for [eqb : A -> A -> bool]). *)
  let field_core_ty =
    recover_method_quantifier class_ref method_ref field_core_ty
  in
  (* The field numbers its own [forall A] right after the class's
     parameters, and the instance numbers its binders from one as
     well: [Monad_stateT]'s carrier [stateT S m] names the same
     variable the method's [A] does, so substituting the carrier in
     would spell [A] as the inner monad.  Move the method's variables
     above every instance binder first -- the positions the
     declaration binds them at anyway. *)
  let method_tvar_base =
    max (List.length (Table.get_ind_ip_vars class_ref))
      instance_tvar_count
  in
  let n_method_tvars = method_tvar_count class_ref field_core_ty in
  let field_core_ty =
    let nclass = List.length (Table.get_ind_ip_vars class_ref) in
    let own =
      List.sort compare
        (List.filter (fun i -> i > nclass)
           (collect_tvars [] field_core_ty))
    in
    let sub =
      List.mapi
        (fun k i ->
          (i, Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = method_tvar_base + 1 + k}) )
        own
    in
    if List.for_all (fun (i, t) -> t = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i}) sub
    then field_core_ty
    else subst_tvars_type sub field_core_ty
  in
  (* Extraction eta-expands a type-constructor argument, so the
     carrier arrives as [option<_>] rather than the bare [option] the
     application needs; contract it before substituting.

     Unless the carrier is written with a [Core.Type.Unknown] hole.  Then it is
     already the type-level lambda, the hole is its binder, and the
     binder may be written more than once: [stateT S m] arrives as
     [stateT(S, m _, _)], because the record's monad parameter is
     itself applied to the element.  Dropping the trailing argument
     keeps one occurrence and loses the other, and what comes out is a
     [stateT] short a template argument.  Applying a hole is filling
     it -- every occurrence at once -- which {!Core_util.apply_core_type}
     already does, so there is nothing to contract here. *)
  let subst_args =
    List.mapi
      (fun i t ->
        match t with
        | _ when Core_util.type_has_hole t -> t
        | Core.Type.Global_app {head = r; type_arguments = _ :: _; index_arguments = es}
          when Table.is_hkt_param class_ref i ->
          (* Only the eta-expanded arguments come off: a carrier that
             arrived partially applied keeps the ones it fixed. *)
          Core.Type.Global_app {head = r; type_arguments = hkt_carrier_fixed_args
                (Table.get_ind_hkt_arity class_ref i)
                t; index_arguments = es}
        | Core.Type.Variable_app {head = j; arguments = _ :: _} when Table.is_hkt_param class_ref i
          ->
          (* Same contraction for a carrier that is a type variable:
             what is left is the head the class applies. *)
          ( match
              hkt_carrier_fixed_args
                (Table.get_ind_hkt_arity class_ref i)
                t
            with
          | [] -> Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = j}
          | fixed -> Core.Type.Variable_app {head = j; arguments = fixed} )
        | t -> t )
      (Type_util.instance_type_args type_args)
  in
  let subst_ty = Core_util.type_subst_list subst_args field_core_ty in
  (* The concept requires the field at the arity the class declared it
     at, so an instance whose type argument is itself a function type
     ([Instance : D (nat -> nat)]) may not absorb the arrows that
     arrived with the substitution as further parameters: they belong
     to the value the accessor returns. *)
  let declared_arity = count_core_value_arrows field_core_ty in
  let method_args_and_ret () = split_at_arity declared_arity subst_ty in
  (* The declared signature numbers the method's own type variables
     after every parameter of the class, while the body -- extracted
     on its own -- numbers them after the instance's own binders, and
     need not have numbered them consecutively.  Read the body's
     quantifiers off the body and map them, in order, onto the
     positions the declared signature gives them; left alone the body would
     name [A] where the class carrier sits. *)
  let field_body =
    if n_method_tvars = 0 then field_body
    else
      let base = method_tvar_base in
      let body_tvars =
        let acc = ref [] in
        ignore
          (Core_util.ast_map_types
             (fun t ->
               acc := collect_tvars !acc t;
               t )
             field_body);
        List.sort compare
          (List.filter (fun i -> i > instance_tvar_count) !acc)
      in
      let subst =
        List.mapi
          (fun k i -> (i, Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = base + 1 + k}))
          (safe_firstn n_method_tvars body_tvars)
        (* A body may name more variables than the field declares --
           an inner monad the mode erases leaves one behind.  The
           declaration binds what it declares and no more, so what is
           left over is spelled the way any type the declaration
           cannot name is: erased. *)
        @ List.filteri
            (fun k _ -> k >= n_method_tvars)
            (List.map (fun i -> (i, Core.Type.Unknown)) body_tvars)
      in
      if List.for_all (fun (i, t) -> t = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                             variable = i}) subst
      then field_body
      else Core_util.ast_map_types (subst_tvars_type subst) field_body
  in
  (* An instance method may have been eta-reduced below the arity its
     class field declares ([cmap A B f x := f x] extracts to
     [fun A B f => f]).  The concept requires the declared arity, so
     re-introduce the missing arguments.

     A body with no lambdas at all is left alone: {!eta_call}, which the
     instance's generator uses, handles the point-free case, and it also
     bridges a parameter the class declares at an erased type to the
     concrete type the named body expects. *)
  let rec nb_lams = function
    | Core.Expr.Lambda {parameter_type = ty; body = rest; _} ->
      (if erased_by_extraction ty then 0 else 1) + nb_lams rest
    | _ -> 0
  in
  (* A binder whose type extraction erased away ([token], a
     one-constructor inductive carrying no information) still occupies
     a parameter slot: the class declares the field at an arity every
     instance must meet, and the concept checks that arity.  Where the
     body's leading binders line up one-for-one with the declared
     arguments, the declaration's type wins over the body's erased
     annotation, so the parameter survives instead of being dropped as
     a proof binder would be. *)
  let field_body =
    let declared = fst (get_args_and_ret [] subst_ty) in
    let rec leading = function Core.Expr.Lambda {body = r; _} -> 1 + leading r | _ -> 0 in
    if leading field_body <> List.length declared then field_body
    else
      let rec retype tys body =
        match (tys, body) with
        | ty :: rest, Core.Expr.Lambda {parameter = id; parameter_type = bty; body = b} ->
          let erased_value =
            (* [Core.Erasure_reason.Type_argument] is an erased type abstraction -- the field's own
               [forall A], which stands at no declared argument.  Any
               other erased annotation is a value binder whose type
               carried no information. *)
            match extraction_erasure bty with
            | Some (Proof | Implicit _) -> true
            | Some (Type_binder | Void) | None -> false
          in
          let bty = if erased_value && not (erased_by_extraction ty) then ty else bty in
          Core.Expr.Lambda {parameter = id; parameter_type = bty; body = retype rest b}
        | _ -> body
      in
      retype declared field_body
  in
  let field_body =
    if nb_lams field_body = 0 && Table.get_ind_hkt_params class_ref = []
    then field_body
    else
    let arg_types =
      List.filter
        (fun t ->
          not (Table.is_typeclass_type t) && not (erased_by_extraction t) )
        (fst (method_args_and_ret ()))
    in
    let missing =
      List.length arg_types - nb_lams field_body
    in
    if missing <= 0 then field_body
    else
      let missing_tys =
        List.filteri
          (fun i _ -> i >= List.length arg_types - missing)
          arg_types
      in
      let rec expand = function
        | Core.Expr.Lambda {parameter = id; parameter_type = ty; body = rest} ->
          Core.Expr.Lambda {parameter = id; parameter_type = ty; body = expand rest}
        | inner ->
          let inner = Core_util.ast_lift missing inner in
          let args =
            List.init missing (fun i -> Core.Expr.fresh_rel (missing - i))
          in
          List.fold_left
            (fun acc (i, ty) ->
              Core.Expr.Lambda
                {parameter = Core.Binder_name.Source (Id.of_string ("a" ^ string_of_int i));
                  parameter_type = ty; body = acc} )
            (Core_normalize.apply inner args)
            (List.rev (List.mapi (fun i t -> (i, t)) missing_tys))
      in
      expand field_body
  in
  (* The body's embedded types still mention the class's promoted type
     variables ([list E] carries [Core.Type.Variable 1], not [list nat]).  Resolve
     them exactly as the parameter and return types are resolved: left
     alone they would render as the concept's template parameter [T1],
     which is not in scope inside the instance struct. *)
  let field_body = Core_util.ast_map_types (subst_promoted_tvars inst) field_body in
  (* The body was extracted at the class's erased field type, so its
     [Core.Expr.Match] and [Core.Expr.Construct] annotations say [option _] where the
     declared signature says [option A].  Push the declared type back
     down, or the body would spell [Option<std::any>] against a value
     the signature typed [Option<_A0>]. *)
  let field_body = Core_util.recover_erased_types subst_ty field_body in
  {field_core_ty; subst_args; subst_ty; n_method_tvars; declared_arity; body = field_body}

type param = {
  binder : Core.Binder_name.t;
  binder_ty : Core.Type.t;
  erased : bool;
}

(* Whether a binder's recorded type says it carries nothing: extraction
   writes an erased binder's type as [Core.Type.Erased], and one it could not type at
   all as [Core.Type.Axiom]. *)
let is_erasable_binder_ty ty =
  erased_by_extraction ty || match ty with Core.Type.Axiom -> true | _ -> false

(* Every leading [Core.Expr.Lambda], erased or not. *)
let rec count_leading_lams = function
  | Core.Expr.Lambda {body = rest; _} -> 1 + count_leading_lams rest
  | _ -> 0

let params m =
  let rec extract n rem acc body =
    match body with
    (* Past the declared arity the remaining binders are the value's own, not
       the accessor's: they stay in the body, which the return type spells as
       a [std::function].  Checked before the erased case, since an erased
       binder past the arity is the value's too. *)
    | Core.Expr.Lambda _ when n >= m.declared_arity -> (List.rev acc, body)
    | Core.Expr.Lambda {parameter = binder; parameter_type = binder_ty; body = rest}
      when is_erasable_binder_ty binder_ty
           && (rem > m.declared_arity - n || not (Core_util.ast_occurs 1 rest)) ->
      (* An erased binder is no parameter, but it is still a binder: dropping
         it would shift every de Bruijn index the body uses to name the ones
         that remain.

         A binder may only be dropped while binders are left to spare, or
         while the body makes no use of it: extraction sometimes annotates a
         value binder as erased ([ret := @Some] extracts as [fun (_ : axiom)
         (x : dummy) => Some x]), and the declared arity is what says how many
         of them the concept is owed. *)
      extract n (rem - 1) ({binder; binder_ty; erased = true} :: acc) rest
    | Core.Expr.Lambda {parameter = binder; parameter_type = binder_ty; body = rest} ->
      extract (n + 1) (rem - 1) ({binder; binder_ty; erased = false} :: acc) rest
    | _ -> (List.rev acc, body)
  in
  extract 0 (count_leading_lams m.body) [] m.body

let eta_call m inner_body =
  let all_arg_types, _ = args_and_ret m in
  (* Filter out type class instance and erased args *)
  let arg_types =
    List.filter
      (fun t -> (not (Table.is_typeclass_type t)) && not (erased_by_extraction t))
      all_arg_types
  in
  match arg_types with
  | [] -> None
  | _ ->
    (* Parameters only for the real arguments, but [Core.Expr.Erased_value] for the erased
       ones in the application, so the body receives every argument it
       expects. *)
    let nparams = List.length arg_types in
    let core_rels =
      let real_idx = ref nparams in
      List.map
        (fun t ->
          if erased_by_extraction t || Table.is_typeclass_type t then
            Core.Expr.Erased_value Core.Erasure_reason.Type_argument
          else begin
            let r = Core.Expr.fresh_rel !real_idx in
            decr real_idx;
            r
          end )
        all_arg_types
    in
    let params = List.mapi (fun i t -> (Id.of_string ("a" ^ string_of_int i), t)) arg_types in
    (* The body's de Bruijn indices lifted over the new parameters. *)
    Some (params, Core_normalize.apply (Core_util.ast_lift nparams inner_body) core_rels)

let methods name body ty =
  let {inner_ty; inner_body; lam_params; _} = layers ty body in
  match inner_ty with
  | Core.Type.Global_app {head = class_ref; type_arguments = type_args; _} when Table.is_typeclass class_ref -> (
    match record_body name class_ref inner_ty lam_params inner_body with
    | Core.Expr.Construct {result_type = cons_ty; arguments = method_bodies; _} ->
      let fields = Table.record_field_bindings_of_type inner_ty in
      if List.length fields <> List.length method_bodies then None
      else
        let type_args = record_type_args cons_ty type_args in
        let tvar_count = tvar_count ~instance_tvars:(instance_tvars ty inner_ty) ty type_args in
        let inst = {class_ref; type_args; tvar_count} in
        let method_of {Core.Record.Field.projection = field; type_ = field_ty} field_body =
          match (field, field_ty) with
          (* A class-typed field is promoted, not generated as a method. *)
          | Some _, Core.Type.Global_app {head = r; _} when Table.is_typeclass r -> None
          | Some method_ref, _ -> Some (prepare_method ~freshen:false inst method_ref field_ty field_body)
          | None, _ -> None
        in
        Some (lam_params, List.filter_map Fun.id (List.map2 method_of fields method_bodies))
    | _ -> None )
  | _ -> None
