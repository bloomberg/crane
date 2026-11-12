(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A global call as Core elaborates it.  See [elaborated_call.mli]. *)

type role =
  | Dictionary
  | Erased_dictionary
  | Regular
  | Excess
  | Dropped

type dictionary_order =
  | Source_order
  | Reversed

type t = {
  callee : Names.GlobRef.t;
  callee_type : Miniml.ml_type;
  args : Miniml.ml_ast list;
  roles : role list;
  primary : Miniml.ml_ast list;
  excess : Miniml.ml_ast list;
  instances : Miniml.ml_ast list;
  erased_instances : int;
  regular : Miniml.ml_ast list;
  tyargs : Call_tyargs.t;
}

let of_roles ~callee ~callee_type ~dictionaries ~tyargs args roles =
  let having p = List.filter_map (fun (a, r) -> if p r then Some a else None) (List.combine args roles) in
  let instances = having (( = ) Dictionary) in
  {
    callee;
    callee_type;
    args;
    roles;
    primary = having (function Dictionary | Erased_dictionary | Regular -> true | _ -> false);
    excess = having (( = ) Excess);
    instances = (match dictionaries with Source_order -> instances | Reversed -> List.rev instances);
    erased_instances = List.length (List.filter (( = ) Erased_dictionary) roles);
    regular = having (( = ) Regular);
    tyargs;
  }

let with_tyargs c tyargs = {c with tyargs}

let same_roles a b =
  Names.GlobRef.UserOrd.equal a.callee b.callee
  && List.equal ( == ) a.args b.args
  && List.equal ( = ) a.roles b.roles

let leading_params c = List.length c.instances + c.erased_instances
let dictionary_filled c = Call_tyargs.resolved_from Call_tyargs.Argument_heads c.tyargs

type instantiated = {
  call : t;
  reading : Call_tyargs.t;
  tys : Mlutil.Var_types.t;
  callee_type_at_call : Miniml.ml_type;
  params : Param_pos.subst Param_pos.params;
  params_orig : Param_pos.orig Param_pos.params;
  subst_index_of_orig : Param_pos.orig Param_pos.pos -> Param_pos.subst Param_pos.pos option;
}

let instantiate call ~reading ~at_call ~expand ~erased =
  let tys = Call_tyargs.by_variable reading in
  let subst = at_call tys in
  let callee_type_at_call = subst call.callee_type in
  let params_orig = Param_pos.orig_params ~expand call.callee_type in
  {
    call;
    reading;
    tys;
    callee_type_at_call;
    params = Param_pos.subst_params ~expand callee_type_at_call;
    params_orig;
    subst_index_of_orig = Param_pos.subst_of_orig ~erased:(fun t -> erased (subst t)) params_orig;
  }

let same_reading a b =
  let ordinals vs = List.map Scheme.Var.ordinal vs in
  let evidences =
    Call_tyargs.[Written; Argument_types; Argument_heads; Expected_result; Eta_parameter]
  in
  Mlutil.Var_types.equal (Call_tyargs.by_variable a) (Call_tyargs.by_variable b)
  && List.equal Int.equal (ordinals (Call_tyargs.holes a)) (ordinals (Call_tyargs.holes b))
  && List.equal Int.equal (ordinals (Call_tyargs.beyond_extent a)) (ordinals (Call_tyargs.beyond_extent b))
  && List.for_all (fun e -> Call_tyargs.resolved_from e a = Call_tyargs.resolved_from e b) evidences

let same_instantiation a b =
  Names.GlobRef.UserOrd.equal a.call.callee b.call.callee
  && List.equal ( = ) a.call.roles b.call.roles
  && same_reading a.call.tyargs b.call.tyargs
  && same_reading a.reading b.reading
  && Mlutil.eq_ml_type a.callee_type_at_call b.callee_type_at_call

let at_call inst call =
  if not (Names.GlobRef.UserOrd.equal inst.call.callee call.callee && List.equal ( = ) inst.call.roles call.roles)
  then invalid_arg "Elaborated_call.at_call";
  {inst with call = {call with tyargs = inst.call.tyargs}}

type static_projection = {
  instance : int;
  domains : Miniml.ml_type list;
  missing : Miniml.ml_type list;
}

let same_static_projection a b =
  Int.equal a.instance b.instance
  && List.equal Mlutil.eq_ml_type a.domains b.domains
  && List.equal Mlutil.eq_ml_type a.missing b.missing
