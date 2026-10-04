(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Records and type classes: a record's struct, a class's concept and the
    constraint a class-typed parameter states. *)

open Common
open Miniml
open Minicpp
open Names
open Table
open Util
open Ml_type_util
open Translation
open Gen_context

module IntSet = Escape.IntSet

(** Generate C++ struct for a record type.

    Only actual type parameters ([Keep] in [ip_sign]) become C++ template
    parameters.  Promoted Type-valued fields (present in [ip_vars] but past
    the [Keep] entries) are erased to [std::any] — they have no C++ template
    counterpart in a plain struct (unlike typeclasses, which turn them into
    [typename I::field] requirements). *)
let gen_record_cpp name fields ind =
  let nb_keep = count_keep_params ind.ip_sign in
  let param_ip_vars = List.filteri (fun i _ -> i < nb_keep) ind.ip_vars in
  let vars = List.map Common.tparam_name param_ip_vars in
  (* Use full ip_vars for type name resolution so Tvars resolve to names,
     then replace promoted Tvars (not in template params) with std::any. *)
  let all_vars = List.map Common.tparam_name ind.ip_vars in
  let promoted_var_names =
    List.filteri (fun i _ -> i >= nb_keep) ind.ip_vars
    |> List.map (fun id -> Id.to_string (Common.tparam_name id))
  in
  let replace_promoted = function
    | (Tpromoted id | Tvar (Tv_index (_, Some id) | Tv_named id))
      when List.mem (Id.to_string id) promoted_var_names ->
      Tany
    | Tglob (g, _, _) when Table.is_promoted_type_var g ->
      ( match Table.promoted_type_var_name g with
      | Some var_id when List.mem (Id.to_string var_id) promoted_var_names ->
        Tany
      | _ -> Tany )
    | ty -> ty
  in
  (* A field's type at a given spelling of the template parameters.  The
     promoted tail is not a template parameter and keeps its own name; only
     the [Keep] prefix is respelled, which is what the conversion function
     below needs. *)
  let field_cpp_ty param_names t =
    let spelling =
      List.mapi
        (fun i x -> match List.nth_opt param_names i with Some u -> u | None -> x)
        all_vars
    in
    let ct =
      convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
        spelling t
    in
        let ct = Minicpp.map_cpp_type replace_promoted ct in
        (* A record's parameters are plain [typename]s, so one of them cannot
           be applied: where the field type applies a higher-kinded parameter
           ([F A]), the parameter stands for the carrier already applied at
           the erased element -- [FnD<std::optional<std::any>>] -- and the
           application is the parameter itself.  Only a class demotes such a
           parameter to an associated type it can apply. *)
    Minicpp.map_cpp_type
      (function
        | Tapply ((Tvar (Tv_index (_, Some v) | Tv_named v) as head), _)
          when List.exists (fun x -> Id.equal x v) spelling -> head
        | ty -> ty )
      ct
  in
  let field_name i x =
    match x with
    | Some n -> n
    | None -> GlobRef.VarRef (Id.of_string ("_field" ^ string_of_int i))
  in
  let l =
    List.mapi
      (fun i (x, t) ->
        (Fvar' (field_name i x, field_cpp_ty vars t), VPublic, SNoTag) )
      fields
  in
  (* A record's fields are payloads like any other, so the promoted variables
     they name are template parameters here too -- see
     {!Table.promoted_type_params} and its use for the other inductive
     kinds. *)
  let ty_vars =
    List.map (fun v -> (TTtypename, v)) (Table.promoted_type_params name)
    @ List.map (fun x -> (TTtypename, x)) vars
  in
  let conversion_field =
    conversion_to_other_instantiation ~leading:(mentioned_promoted_args name)
      ~name ~templates:(List.map (fun x -> (TTtypename, x)) vars) ~vars
      ~fields:
        (List.mapi
           (fun i (x, t) ->
             ( Id.of_string_soft
                 (Common.pp_global_name Type (field_name i x)),
               fun param_names -> field_cpp_ty param_names t ) )
           fields)
  in
  Dstruct
    {
      ds_ref = name;
      ds_fields = l @ conversion_field;
      ds_tparams = ty_vars;
      ds_constraint = None;
      ds_needs_shared_from_this = false;
    }

(** The concept constraint an instance parameter of type [ty] carries.

    Three things go into the argument list, and the only reason this is a
    function is that two call sites -- {!strip_outer_layers} for a lambda's
    instance binder and {!promote_typeclass_params} for a declared one -- have
    to agree on all three or the constraint does not match the concept:

    - the instance itself, which the printer supplies as the first argument;
    - the class's kept type arguments, for a multi-parameter concept;
    - the promoted variables the class {e mentions} without declaring, which
      {!gen_typeclass_cpp} makes template parameters of the concept.  They are
      written as the bare names the class spells, so the pass that resolves a
      bare promoted name against the instance owning it reaches them the way it
      reaches every other position in the signature. *)
let concept_constraint_of_class_type ty =
  match ty with
  | Miniml.Tglob (class_ref, type_args, _) ->
    let kept =
      if Table.get_ind_nb_tparams class_ref = 0 then []
      else
        List.map
          (convert_ml_type_to_cpp_type (empty_env ()) [])
          (Table.drop_hkt_args class_ref type_args)
    in
    Some (TTconcept (class_ref, kept @ mentioned_promoted_args class_ref))
  | _ -> None

(** Generate a C++ concept from a type class.
   Type class Eq(A) with method eqb : A -> A -> bool becomes:
   template<typename I, typename A>
   concept Eq = requires(A a0, A a1) {
     { I::eqb(a0, a1) } -> std::convertible_to<bool>;
   };

   Uses CPPconvertible_to with the actual cpp_type for the constraint,
   which will be pretty-printed in cpp.ml.
*)
let gen_typeclass_cpp name fields ind =
  let nb_keep = count_keep_params ind.ip_sign in
  let inst_id =
    let param_names =
      List.mapi (fun i x -> if i < nb_keep
                            then Id.to_string (Common.tparam_name x)
                            else "") ind.ip_vars
    in
    if List.mem "I" param_names then Generated_name.id "Inst"
    else Id.of_string "I"
  in
  (* Split ip_vars into param vars (real type params) and promoted vars
     (associated types). Prefix param vars with t_ for BDE convention. *)
  (* A parameter that is itself a type constructor ([M : Type -> Type]) is not
     a C++ template type parameter but an associated type of the instance
     ([typename I::M]) — the same treatment promoted Type-valued fields get. *)
  let is_tparam i = is_class_tparam name i in
  let prefixed_ip_vars =
    List.mapi (fun i x -> if is_tparam i then Common.tparam_name x else x)
      ind.ip_vars
  in
  let param_vars = List.filteri (fun i _ -> is_tparam i) prefixed_ip_vars in
  (* Read the promoted half off {!class_promoted_vars} rather than re-deriving
     it here: the two must agree element for element, because [type_reqs]
     below pairs them up. *)
  let promoted_vars = class_promoted_vars name in
  (* Only param vars become concept template parameters; promoted vars become
     typename requirements inside the requires block *)
  let ty_vars = List.map (fun x -> (TTtypename, x)) param_vars in
  (* The promoted variables the class {e mentions} without declaring them --
     [ptr] and [iptr], reached through a field whose type is a section
     inductive.  They are template parameters here for the same reason they
     are on {!gen_record_cpp}'s struct: the text spells them bare, and bare is
     what a template parameter of that name makes correct. *)
  let mentioned_promoted =
    List.map (fun v -> (TTtypename, v)) (Table.promoted_type_params name)
  in
  let all_params =
    ((TTtypename, inst_id) :: ty_vars) @ mentioned_promoted
  in
  (* Build typename requirements for promoted vars: typename I::field; *)
  (* A higher-kinded carrier is an alias template, so the concept cannot ask
     for it bare: it is probed at [std::any], the same erased element type the
     method requirements below are stated at. *)
  let type_reqs =
    List.map2
      (fun var_id arity ->
        let assoc = Tqualified (Tinstance (inst_id, name), var_id) in
        if arity = 0 then assoc
        else Tapply (assoc, List.init arity (fun _ -> Tany)) )
      promoted_vars
      (List.map snd (class_promoted_vars_arities name))
  in
  let promoted_map =
    promoted_resolutions ~fields name (Tinstance (inst_id, name))
  in
  (* Substitute promoted Tvars in cpp_type trees.  After conversion, a promoted
     var appears as [Tvar (Tv_index (_, Some name) | Tv_named name)]; [promoted_map] says which qualified
     type that bare name really denotes ([typename I::Obj], or
     [typename I::base_category::Obj] when it comes from a typeclass-typed
     promoted field).  A name with no entry is left as a plain type variable. *)
  let subst_promoted_in_cpp_type =
    rewrite_cpp_type (function
      | Tpromoted vname | Tvar (Tv_index (_, Some vname) | Tv_named vname) -> (
        match List.find_opt (fun (n, _) -> Id.equal n vname) promoted_map with
        | Some (_, replacement) -> Some replacement
        | None -> Some (named_tvar vname) )
      | _ -> None )
  in
  (* Check if a type is a bare promoted Tvar — a Tvar whose index is beyond the
     real type parameters. This indicates the field's type is entirely
     determined by a promoted associated type, so we can't decompose it into
     args and return type at concept time (the concrete type might be a
     function). *)
  let is_bare_promoted_tvar ty =
    match ty with
    | Miniml.Tvar (Schematic, n) -> not (is_tparam (n - 1))
    | _ -> false
  in
  (* Check if a field type is a typeclass-typed promoted field.  Such
     fields become [typename I::field] requirements (already in type_reqs)
     and should NOT generate method requirements in the concept body. *)
  let is_typeclass_field_type ty =
    match ty with
    | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
    | _ -> false
  in
  (* This is the same question {!promoted_var_is_associated_type} asks, so the
     two lists partition the fields and no name can reach both.  They are
     computed in different places and could drift apart again; a concept that
     wants one name as a type and as a function is satisfied by no instance at
     all, and nothing downstream of it instantiates, so the failure is silent
     everywhere except in the error count of whatever used it. *)
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    List.iter
      (fun (field_opt, field_ty) ->
        match field_opt with
        | Some fr when not (is_typeclass_field_type field_ty) ->
          let fid = Common.id_of_global Term fr in
          if List.exists (Id.equal fid) promoted_vars then
            CErrors.user_err
              Pp.(
                str "Crane: concept '"
                ++ Id.print (Common.id_of_global Type name)
                ++ str "' requires '" ++ Id.print fid
                ++ str "' both as a type and as a method." )
        | _ -> () )
      fields;
  (* Generate a single method requirement. Returns either: - `Normal (params,
     (call, constraint))` for regular methods - `Disjunctive expr` for fields
     whose type is a bare promoted Tvar *)
  let gen_method_req (field_opt, field_ty) =
    match field_opt with
    | None -> None (* Anonymous field, skip *)
    | Some field_ref ->
      let method_name = Common.pp_global_name Term field_ref in
      if is_typeclass_field_type field_ty then
        (* TypeClass-typed field (a superclass instance).  It carries no
           method of its own: the instance exposes it as a nested type, so
           the concept asks for [typename I::field;] rather than a call.  A
           method requirement would try to use the concept name as a concrete
           type (e.g. [std::shared_ptr<PreCategory>]), which is invalid. *)
        Some
          (`Type
            (Tqualified
               ( Tinstance (inst_id, name),
                 Common.id_of_global Term field_ref )))
      else if is_bare_promoted_tvar field_ty then
        (* Field type is a bare promoted Tvar (e.g., fun_ind_prf :
           fun_ind_prf_ty). The concrete type could be a plain value or a
           function with any arity. Generate a disjunctive concept requirement:
           requires { { I::method() } -> std::convertible_to<T>; } || requires {
           { I::method } -> std::convertible_to<T>; } The first clause handles
           nullary accessors (Meyers singleton pattern). The second handles
           functions (pointer converts to std::function) and static data members
           (direct value). *)
        let ret_cpp =
          convert_ml_type_to_cpp_type
            (empty_env ())
            prefixed_ip_vars
            field_ty
        in
        let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
        let constraint_expr = CPPconvertible_to ret_cpp in
        let qualified =
          CPPscope (CPPvar inst_id, Id.of_string method_name, [])
        in
        let call_form =
          CPPrequires ([], [(mk_call qualified [], constraint_expr)], [])
        in
        let value_form = CPPrequires ([], [(qualified, constraint_expr)], []) in
        Some (`Disjunctive (CPPbinop (Bor, call_form, value_form)))
      else
        let args, ret = get_args_and_ret [] field_ty in
        (* Filter out type class instance arguments (they're passed via
           template) *)
        let args =
          List.filter (fun t ->
            not (Table.is_typeclass_type t) && not (Mlutil.isTdummy t)) args
        in
        let ret_cpp =
          convert_ml_type_to_cpp_type
            (empty_env ())
            prefixed_ip_vars
            ret
        in
        let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
        (* Emit each argument inline as [std::declval<ArgType>()] rather than
           binding it to a shared [requires(...)] parameter.  A requires-
           expression has a single parameter list shared across all its
           requirement lines, so naming arguments positionally (a0, a1, ...)
           and deduplicating by name aliases parameters of different types
           across methods (e.g. [g : T -> T] would reuse [a0 : pair<T,T>]
           left over from [f : T*T -> T]).  Using [declval] gives each method
           its own correctly-typed arguments, matching the module-type concept
           idiom in [cpp.ml]'s [pp_spec_as_requirement]. *)
        let arg_declvals =
          List.map
            (fun arg_ty ->
              let arg_cpp =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  prefixed_ip_vars
                  arg_ty
              in
              CPPdeclval (subst_promoted_in_cpp_type arg_cpp) )
            args
        in
        (* Method call: I::method_name(std::declval<...>(), ...). *)
        (* A method of a higher-kinded class is a member template, and the
           probe states its requirement at the erased element type, so the
           arguments are spelled out rather than deduced: a nullary method
           ([I::empty()]) offers nothing to deduce from, and defaulting the
           parameters instead would let a call that fails to deduce silently
           fall back to [std::any].  {!method_tvar_count} is the same count
           the instance binds. *)
        let ntv =
          method_tvar_count
            name
            (recover_method_quantifier name field_ref field_ty)
          (* A class-typed argument is a template parameter of the method, not
             a value: the instance declares one per such argument, after its
             own type variables. *)
          + List.length
              (List.filter
                 Table.is_typeclass_type
                 (fst (get_args_and_ret [] field_ty)) )
        in
        let callee =
          if ntv = 0 then
            CPPscope (CPPvar inst_id, Id.of_string method_name, [])
          else
            CPPscope ( CPPvar inst_id,
                Id.of_string method_name,
                List.init ntv (fun _ -> Tany) )
        in
        let call = mk_call callee arg_declvals in
        (* Constraint: use the cpp_type directly - cpp.ml will render it *)
        let constraint_expr = CPPconvertible_to ret_cpp in
        Some (`Normal ([], (call, constraint_expr)))
  in
  let all_reqs =
    List.filter_map (fun pair -> gen_method_req pair) fields
  in
  (* Superclass fields contribute [typename I::field;] alongside the promoted
     associated types.  Without them a class made purely of superclasses would
     yield an empty (and therefore ill-formed) requires-expression. *)
  let type_reqs =
    List.fold_left
      (fun acc req ->
        match req with
        | `Type t when not (List.exists (fun t' -> t' = t) acc) -> acc @ [t]
        | _ -> acc )
      type_reqs all_reqs
  in
  (* Separate normal requirements from disjunctive ones *)
  let normal_reqs =
    List.filter_map
      (function
        | `Normal r -> Some r
        | _ -> None )
      all_reqs
  in
  let disjunctive_exprs =
    List.filter_map
      (function
        | `Disjunctive e -> Some e
        | _ -> None )
      all_reqs
  in
  (* Build the concept body. Normal requirements go in a single requires{}
     block. Disjunctive requirements (for bare-Tvar fields) are &&-ed
     separately, each wrapped in parentheses via the || rendering. *)
  let concept_body =
    let normal_part =
      if normal_reqs = [] then
        None
      else
        (* Arguments are emitted inline as [std::declval<...>()], so the
           requires-expression needs no parameter list. *)
        let constraints = List.map snd normal_reqs in
        Some (CPPrequires ([], constraints, type_reqs))
    in
    match (normal_part, disjunctive_exprs) with
    | Some np, [] -> np
    | None, [d] ->
      if type_reqs <> [] then
        CPPbinop (Band, CPPrequires ([], [], type_reqs), d)
      else
        d
    | None, d :: rest ->
      let base =
        if type_reqs <> [] then
          CPPbinop (Band, CPPrequires ([], [], type_reqs), d)
        else
          d
      in
      List.fold_left (fun acc e -> CPPbinop (Band, acc, e)) base rest
    | Some np, ds -> List.fold_left (fun acc e -> CPPbinop (Band, acc, e)) np ds
    | None, [] ->
      if type_reqs <> [] then
        CPPrequires ([], [], type_reqs)
      else
        CPPrequires ([], [], [])
    (* degenerate: no requirements *)
  in
  Dtemplate (all_params, None, Dconcept (name, concept_body))

(** Whether a binder's recorded type says it carries nothing: extraction
    writes an erased binder's type as [Tdummy], and one it could not type at
    all as [Taxiom]. *)
let is_erasable_binder_ty ty =
  Mlutil.isTdummy ty || match ty with Miniml.Taxiom -> true | _ -> false

(** The number of lambdas a term opens with. *)
let rec count_leading_lams = function
  | MLlam (_, _, rest) -> 1 + count_leading_lams rest
  | _ -> 0

(** What becomes of one of an instance method's binders in the C++ signature.

    [`Value] is an ordinary parameter; [`Instance] is a class-typed binder,
    which leaves the value list for the template one because the instance
    satisfying a concept is a type; [`Erased] is a binder with no
    computational content, which is no parameter at all but still occupies a
    de Bruijn slot the body counts through. *)
type binder_kind = [`Value | `Instance | `Erased]

(** One binder an instance method's body opens with, as {!binder_kind}
    classified it.  The ML type is the one the body spells it by and the C++
    type the one the accessor declares: the three travel together, and reading
    the kind of the [i]th binder out of a list beside them is how they come
    apart. *)
type method_binder = {
  mb_name : Id.t;
  mb_ml_ty : ml_type;
  mb_cpp_ty : cpp_type;
  mb_kind : binder_kind;
}
