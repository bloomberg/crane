(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A copy of a Core term that is new terms.  See [core_copy.mli]. *)


(* [e] with each variable a use in it leaves rigid that [rigid] solves
   solved so. *)
let rec solve_rigid rigid e =
  let solves v (s : Core.Type.t Scheme.slot) =
    match s.solution with Scheme.Identity -> Option.has_some (rigid v) | Scheme.Type _ -> false
  in
  match e with
  | Core.Expr.Global u -> (
    match Core.Global_use.instantiation u with
    | Some inst when Scheme.Instantiation.exists solves inst ->
      Core.Expr.Global
        (Core.Global_use.polymorphic (Core.Global_use.callee u)
           (Scheme.Instantiation.map_slots
              (fun v (s : Core.Type.t Scheme.slot) ->
                match (s.solution, rigid v) with
                | Scheme.Identity, Some t -> {s with solution = Scheme.Type t}
                | _ -> s )
              inst ) )
    | _ -> e )
  | e -> Mlutil.ast_map (solve_rigid rigid) e

(* The callee's own open annotations and holes are renamed before [types]
   instantiates it: what the use solves a variable to belongs to the caller,
   whose open annotations are numbered apart from the callee's and may share
   a number with one of them. *)
let copy_with ~types ~rigid e =
  Fresh_occurrences.term (solve_rigid rigid (Mlutil.ast_map_types types (Mlutil.freshen_holes (Mlutil.freshen_metas e))))

(* A copy at no instantiation. *)
let copy = copy_with ~types:Fun.id ~rigid:(fun _ -> None)

(* What [use] solves its callee's variables to: a type for each annotation,
   and for each variable a rigid self-reference inside the callee leaves
   standing for itself, its solution if the use solves it. *)
let solutions use =
  match Core.Global_use.instantiation use with
  | None -> (Fun.id, fun _ -> None)
  | Some inst ->
    let scheme = Scheme.Instantiation.scheme inst in
    let rigid v =
      Option.bind (Scheme.Var.of_tvar scheme (Scheme.Var.ordinal v)) (fun w ->
          match (Scheme.Instantiation.slot inst w).solution with
          | Scheme.Type t -> Some t
          | Scheme.Identity -> None )
    in
    ((fun t -> (Mlutil.Partial.instantiate inst t :> Core.Type.t)), rigid)

let instance use body =
  let types, rigid = solutions use in
  copy_with ~types ~rigid body

(* The lambdas of the instantiated body are peeled one per declared domain;
   each argument then stands for its parameter, by substitution or a let. *)
let call ~ty use body args =
  let types, _ = solutions use in
  let ty = Mlutil.type_simpl (types ty) in
  let params, body = Ml_type_util.collect_typed_lams ty (instance use body) in
  let domains = Ml_type_util.ml_domains ty in
  if List.length params <> List.length domains || List.length args <> List.length params then None
  else
    (* At the type {!Core_elaborate.declaration_scope} binds the parameter
       at, which is the type translation declares it with. *)
    let parameter_type annotated declared =
      match annotated with
      | Core.Type.Open _ -> declared
      | t -> Core_query.reconcile_parameter_type t declared
    in
    (* A parameter passed a variable, or an erased value, is read as it:
       bound by a let, it would be a copy of what the call passes. *)
    let rec bind lifted = function
      | [] -> body
      | (_, ((Core.Expr.Bound_variable _ | Core.Expr.Erased_value _) as a)) :: rest ->
        Mlutil.ast_subst (Mlutil.ast_lift lifted a) (bind (lifted + 1) rest)
      | (((x, annotated), declared), a) :: rest ->
        Core.Expr.Let {binder = x;
                       binder_type = parameter_type annotated declared;
                       value = Mlutil.ast_lift lifted a;
                       body = bind (lifted + 1) rest;
                       occurrence = Core.Occurrence.fresh ()}
    in
    Some (bind 0 (List.combine (List.combine (List.rev params) domains) args))
