(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

let install struc (facts : Program_facts.t) (plan : Target_plan.t) =
  Table.set_used_customs facts.used_customs;
  Table.set_higher_order_projections facts.higher_order_projections;
  List.iter
    (fun ({block; kind; _} : Target_plan.kind_decision) ->
      Table.add_inductive_kind block kind;
      let write kn ind = if Names.MutInd.UserOrd.equal kn block then ind.ind_kind <- kind in
      Modutil.struct_iter
        (function Dind (kn, ind) -> write kn ind | _ -> ())
        (function Sind (kn, ind) -> write kn ind | _ -> ())
        (fun _ -> ())
        struc )
    plan.inductive_kinds

let install_template_kinds (plan : Target_plan.t) =
  List.iter (fun (r, kinds) -> Tparam_kinds.record r kinds) plan.template_kinds

let install_modules = Module_plan.install

let install_callables = Callable_abi.install

let install_pointer_fields = Loopify_analysis.install_ctor_ptr_fields

let install_accessors = List.iter Cpp_state.register_template_static_accessor_ref

let install_nested_structs =
  List.iter (fun (name, owner) -> Cpp_state.add_nested_struct_name name owner)

let install_unmerged_wrappers =
  List.iter (fun name -> Hashtbl.replace Cpp_state.unmerged_wrappers name ())

let check_installed (facts : Program_facts.t) (plan : Target_plan.t) =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    let fail what =
      CErrors.anomaly
        Pp.(str ("Crane: the installed " ^ what ^ " no longer agree with the plan."))
    in
    (* Emitting a custom marks it used too, so rendering may add to these;
       what the structure names must still be there. *)
    if not (Ref.User.Set.subset facts.used_customs (Table.used_customs ())) then
      fail "used custom references";
    if not (Ref.User.Set.equal (Table.higher_order_projections ()) facts.higher_order_projections)
    then fail "higher-order projections";
    List.iter
      (fun ({block; _} : Target_plan.kind_decision) ->
        let installed = Table.inductive_kind_of (Names.GlobRef.IndRef (block, 0)) in
        if not (Option.equal Target_plan.kind_equal installed (Target_plan.kind_of plan block))
        then fail "inductive kinds" )
      plan.inductive_kinds;
    List.iter
      (fun (r, kinds) ->
        if not (Tparam_kinds.equal (Tparam_kinds.recorded r) kinds) then
          fail "template-parameter kinds" )
      plan.template_kinds;
    if not (Module_plan.installed plan.modules) then fail "module plan";
    (* Each was decided when it was planned, so the kind asked at is not
       consulted again. *)
    List.iter
      (fun (r, s) -> if not (String.equal (Common.pp_global_name Common.Term r) s) then fail "global names")
      plan.representation.names;
    List.iter
      (fun (c, ids) ->
        let ctor = Ml_type_util.ctor_struct_name_of_ref c in
        List.iteri
          (fun j id ->
            if not (Names.Id.equal (Common.lookup_ctor_field_name ~owner:c ctor j) id) then
              fail "constructor field names" )
          ids )
      plan.representation.field_names;
    let describe (name, owner) =
      name ^ " ("
      ^ ( match owner with
        | Cpp_state.NSref r -> Pp.string_of_ppcmds (Names.GlobRef.print r)
        | Cpp_state.NSmodule mp -> Names.ModPath.to_string mp )
      ^ ")"
    in
    let mem (n, o) l =
      List.exists (fun (n', o') -> String.equal n n' && Cpp_state.nested_struct_owner_equal o o') l
    in
    let planned = plan.representation.nested_structs
    and printed = !Cpp_state.printed_nested_structs in
    List.iter
      (fun x -> if not (mem x planned) then fail ("nested structs: printed but not planned " ^ describe x))
      printed;
    if printed <> [] then
      List.iter
        (fun x -> if not (mem x printed) then fail ("nested structs: planned but not printed " ^ describe x))
        planned;
    List.iter
      (fun abi ->
        if not (Option.equal Callable_abi.equal (Callable_abi.lookup (Callable_abi.callee abi)) (Some abi))
        then fail "callable plans" )
      plan.callables
  end
