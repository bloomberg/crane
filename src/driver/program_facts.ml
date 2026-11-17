(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Program facts, observed from the structure alone.  See
    [program_facts.mli]. *)


type t = {
  used_customs : Core.Ref.User.Set.t;
  higher_order_projections : Core.Ref.User.Set.t;
  effects : Core_plan.Effects.t;
}

type program = {
  throwing_values : Names.GlobRef.t list;
  parameter_ownership : (Names.GlobRef.t * bool list) list;
  recursive_groups : Core_plan.Recursive_groups.t;
  partner_closure_params : (Names.GlobRef.t * int list) list;
  reusing_matches : Core.Ref.User.Set.t;
  recursion : Core_plan.Recursion.t;
  control : Core_to_control.Lower_control.t;
}

let analyze_program cx normalized =
  let struc = Core_passes.Phase.structure normalized in
  let recursive_groups = Core_plan.Recursive_groups.analyze struc in
  let methods = Core_plan.Method_registry.create ~ret_is_erased:(Core_to_cpp.Lower_expr.return_type_is_erased cx) struc in
  let receiver r = Option.map snd (Core_plan.Method_registry.is_registered_method methods r) in
  let recursion = Core_plan.Recursion.analyze ~suspension:(Core_to_cpp.Suspension.suspension cx) recursive_groups
    normalized in
  { throwing_values = Core_plan.Structure.throwing_values struc;
    parameter_ownership = Core_plan.Ownership.summarize ~receiver struc;
    recursive_groups;
    partner_closure_params = Core_to_cpp.Callable_params.partner_closure_params recursive_groups struc;
    reusing_matches = Core_plan.Ownership.reusing_matches struc;
    recursion;
    control =
      Core_to_control.Lower_control.lower
        ~methods:(fun r -> Option.has_some (Core_plan.Method_registry.is_registered_method methods r))
        recursion normalized }

let lowering (program : program) : Core_to_cpp.Lowering_state.program_facts =
  { throwing_values = List.fold_left (fun s r -> Core.Ref.Can.Set.add r s) Core.Ref.Can.Set.empty program.throwing_values;
    parameter_ownership =
      List.fold_left (fun m (r, f) -> Core.Ref.User.Map.add r f m) Core.Ref.User.Map.empty program.parameter_ownership;
    partner_closure_params =
      List.fold_left (fun m (g, is) -> Core.Ref.User.Map.add g is m) Core.Ref.User.Map.empty program.partner_closure_params;
    reusing_matches = program.reusing_matches }

(* The custom-extracted references [struc] names, a used constructor
   adding its inductive. *)
let used_customs struc =
  let used = ref Core.Ref.User.Set.empty in
  let add r = used := Core.Ref.User.Set.add r !used in
  let mark r =
    if Base.Table.is_custom r then begin
      add r;
      (* Imports registered on an inductive are due when a constructor of it
         is used. *)
      match r with Names.GlobRef.ConstructRef (ip, _) -> add (Names.GlobRef.IndRef ip) | _ -> ()
    end
  in
  Core_passes.Modutil.struct_iter
    (Core_passes.Modutil.decl_iter_references mark mark mark)
    (Core_passes.Modutil.spec_iter_references mark mark mark)
    (fun _ -> ())
    struc;
  !used

(* The projections [struc]'s term definitions name anywhere in their
   bodies. *)
let higher_order_projections struc =
  let found = ref Core.Ref.User.Set.empty in
  let rec scan = function
    | Core.Expr.Global {callee = r; _} when Base.Table.is_projection r -> found := Core.Ref.User.Set.add r !found
    | a -> Base.Core_util.ast_iter scan a
  in
  Core_passes.Modutil.struct_iter
    (fun d -> List.iter (fun (fd : Core.Recursion.Definition.t) -> scan fd.body) (Base.Core_util.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  !found

let analyze struc =
  { used_customs = used_customs struc;
    higher_order_projections = higher_order_projections struc;
    effects = Core_plan.Effects.analyze struc }

let equal a b =
  Core.Ref.User.Set.equal a.used_customs b.used_customs
  && Core.Ref.User.Set.equal a.higher_order_projections b.higher_order_projections
  && Core_plan.Effects.equal a.effects b.effects
