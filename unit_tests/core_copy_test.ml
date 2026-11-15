(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A copy of a Core term is new terms: occurrences, holes and open
   annotations of its own, and the callee's variables solved as the use
   solves them. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "core_copy: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let x s = Core.Binder_name.Source (Id.of_string s)
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
let bool = Core.Type.Global_app {head = r "bool"; type_arguments = []; index_arguments = []}
let a = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}

let rec occurrences e =
  let here =
    match e with
    | Core.Expr.Bound_variable {occurrence = o; _}
    | Core.Expr.Let {occurrence = o; _}
    | Core.Expr.Match {occurrence = o; _}
    | Core.Expr.Fixpoint {occurrence = o; _} | Core.Expr.Cofixpoint {occurrence = o; _} ->
      [o]
    | Core.Expr.Global u -> [Core.Global_use.occurrence u]
    | _ -> []
  in
  let below = ref [] in
  Mlutil.ast_iter (fun c -> below := !below @ occurrences c) e;
  here @ !below

let shares e e' =
  Core.Occurrence.shared (fun visit -> List.iter visit (occurrences e); List.iter visit (occurrences e')) <> []

let slot solution = {Scheme.solution; source = Scheme.Not_written}
let use_at scheme f = Core.Global_use.polymorphic (r "g") (Scheme.Instantiation.make scheme f)

let rec holes = function
  | Core.Type.Hole h -> [h]
  | Core.Type.Arrow {parameter = s; result = t} -> holes s @ holes t
  | Core.Type.Global_app {type_arguments = ts; _} | Core.Type.Variable_app {arguments = ts; _} ->
    List.concat_map holes ts
  | _ -> []

let use_holes = function
  | Core.Expr.Global u ->
    let hs = ref [] in
    Core.Global_use.iter_types (fun t -> hs := !hs @ holes t) u;
    !hs
  | _ -> []

let () =
  let scheme = Scheme.Id.fresh (r "g") ~arity:1 in
  let self = Core.Expr.Global (Core.Global_use.identity (r "g") scheme) in
  let fix = Core.Expr.Fixpoint {selected = 0; functions = [|(Id.of_string "go", Core.Type.Arrow {parameter = a; result = a})|]; bodies = [|Core.Expr.Lambda {parameter = x "y"; parameter_type = a; body = Core.Expr.Apply {callee = Core.Expr.fresh_rel 2; arguments = [Core.Expr.fresh_rel 1]}}|]; occurrence = Core.Occurrence.fresh ()} in
  let body =
    Core.Expr.Lambda {parameter = x "n"; parameter_type = a; body = Core.Expr.Let {binder = x "m"; binder_type = a; value = Core.Expr.fresh_rel 1; body = Core.Expr.Apply {callee = fix; arguments = [Core.Expr.Apply {callee = self; arguments = [Core.Expr.fresh_rel 1]}]}; occurrence = Core.Occurrence.fresh ()}}
  in
  let copied = Core_copy.copy body in
  check "a copy is the term it copies" (copied = body);
  check "a copy shares no occurrence with its original" (not (shares body copied));
  check "the copied term itself has every occurrence once" (not (shares copied (Core.Expr.Erased_value Core.Erasure_reason.Type_argument)));
  check "a term sharing an occurrence is told apart" (shares body body);
  let matching =
    Core.Expr.Lambda {parameter = x "b"; parameter_type = bool; body = Core.Expr.Match {scrutinee_type = bool; scrutinee = Core.Expr.fresh_rel 1; branches = [| { Core.Match.Branch.binders = [];
                 result_type = nat;
                 pattern = Core.Pattern.Wildcard;
                 body = Core.Expr.Let {binder = x "k"; binder_type = nat; value = Core.Expr.Erased_value Core.Erasure_reason.Type_argument; body = Core.Expr.fresh_rel 1; occurrence = Core.Occurrence.fresh ()} } |]; occurrence = Core.Occurrence.fresh ()}}
  in
  check "a copied match is a match of its own" (not (shares matching (Core_copy.copy matching)));
  (* Holes: renamed apart from the original's, the same new one wherever
     the original shares one. *)
  let h = Core.Type.Hole (Scheme.Hole.fresh ()) in
  let two = Core.Expr.Apply {callee = Core.Expr.Global (use_at scheme (fun _ -> slot (Scheme.Type h)));
                             arguments = [Core.Expr.Global (use_at scheme (fun _ -> slot (Scheme.Type h)))]} in
  ( match Core_copy.copy two with
  | Core.Expr.Apply {callee = f; arguments = [g]} ->
    let hf = use_holes f and hg = use_holes g in
    check "a copied hole is a new hole" (hf <> holes h);
    check "a hole shared in the original is shared in the copy" (hf = hg && List.length hf = 1)
  | _ -> check "a copy keeps the shape" false );
  (* Open annotations: likewise, in the frozen program copies are made in. *)
  let o = Core.Type.Open (Core.Open.fresh 7) in
  Core.Meta.freeze ();
  let opened = Core_copy.copy (Core.Expr.Lambda {parameter = x "p"; parameter_type = o; body = Core.Expr.Lambda {parameter = x "q"; parameter_type = o; body = Core.Expr.fresh_rel 1}}) in
  Core.Meta.thaw ();
  ( match opened with
  | Core.Expr.Lambda {parameter_type = Core.Type.Open p;
                      body = Core.Expr.Lambda {parameter_type = Core.Type.Open q; _}; _} ->
    check "a copied open annotation is a new one" (not (Core.Open.equal p (match o with Core.Type.Open o -> o | _ -> assert false)));
    check "an open annotation shared in the original is shared in the copy" (Core.Open.equal p q)
  | _ -> check "a copy keeps the lambdas" false );
  (* Instantiation: the use's solutions replace the callee's variables, in
     annotations and in a rigid self-reference's slots. *)
  let at_nat = use_at scheme (fun _ -> slot (Scheme.Type nat)) in
  let inst = Core_copy.instance at_nat body in
  ( match inst with
  | Core.Expr.Lambda {parameter_type = t;
                      body = Core.Expr.Let {binder_type = t';
                                            body = Core.Expr.Apply {callee = (Core.Expr.Fixpoint {functions = [|(_, ft)|]; _} | Core.Expr.Cofixpoint {functions = [|(_, ft)|]; _});
                                                                    arguments = [Core.Expr.Apply {callee = Core.Expr.Global u; _}]}; _}; _} ->
    check "a parameter's variable is solved" (t = nat && t' = nat);
    check "a local fixpoint's signature is solved" (ft = Core.Type.Arrow {parameter = nat; result = nat});
    ( match Core.Global_use.instantiation u with
    | Some i ->
      check "a rigid self-reference is solved where the use solves its variable"
        (List.for_all
           (fun v -> (Scheme.Instantiation.slot i v).solution = Scheme.Type nat)
           (Scheme.Var.all scheme) )
    | None -> check "the self-reference stays polymorphic" false )
  | _ -> check "an instance keeps the shape" false );
  check "an instance shares no occurrence with its original" (not (shares body inst));
  let rigid = Core_copy.instance (Core.Global_use.identity (r "g") scheme) body in
  ( match rigid with
  | Core.Expr.Lambda {body = Core.Expr.Let {body = Core.Expr.Apply {arguments = [Core.Expr.Apply {callee = Core.Expr.Global u; _}]; _}; _}; _} ->
    check "a rigid use leaves the self-reference rigid"
      (match Core.Global_use.instantiation u with
       | Some i -> Scheme.Instantiation.for_all (fun _ s -> s.Scheme.solution = Scheme.Identity) i
       | None -> false )
  | _ -> check "a rigid instance keeps the shape" false );
  check "a rigid instance is the body itself" (rigid = body)

(* A call: the callee's body under a let per parameter passed a term to
   evaluate, outermost first, each argument lifted past the lets before it;
   a parameter passed a variable or an erased value reads it. *)
let () =
  let ty = Core.Type.Arrow {parameter = nat;
                            result = Core.Type.Arrow {parameter = bool;
                                                      result = Core.Type.Arrow {parameter = nat; result = nat}}} in
  let h = Core.Global_use.monomorphic (r "h") and k = Core.Global_use.monomorphic (r "k") in
  let body =
    Core.Expr.Lambda {parameter = x "p"; parameter_type = nat; body = Core.Expr.Lambda {parameter = x "q"; parameter_type = bool; body = Core.Expr.Lambda {parameter = x "s"; parameter_type = nat; body = Core.Expr.Apply {callee = Core.Expr.Global h; arguments = [Core.Expr.fresh_rel 3; Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 1]}}}}
  in
  let use = Core.Global_use.monomorphic (r "f") in
  let a1 = Core.Expr.Apply {callee = Core.Expr.Global k;
                            arguments = [Core.Expr.fresh_rel 3]} and a2 = Core.Expr.fresh_rel 1 and a3 = Core.Expr.Apply {callee = Core.Expr.Global k;
                                                                                                                          arguments = [Core.Expr.fresh_rel 2]} in
  ( match Core_copy.call ~ty use body [a1; a2; a3] with
  | Some
      (Core.Expr.Let {binder = p;
                      binder_type = tp;
                      value = a1';
                      body = Core.Expr.Let {binder = s;
                                            binder_type = ts;
                                            value = a3';
                                            body = Core.Expr.Apply {arguments = [Core.Expr.Bound_variable {index = 2; _}; Core.Expr.Bound_variable {index = 3;
                                                                                                                                                    occurrence = o}; Core.Expr.Bound_variable {index = 1; _}; Core.Expr.Bound_variable {index = 1; _}]; _}; _}; _}) ->
    check "the parameters passed a term are bound outermost first" (p = x "p" && s = x "s");
    check "each binder takes its parameter's type" (tp = nat && ts = nat);
    check "the first argument stands where the call did" (a1' == a1);
    check "a later argument is lifted past the lets before it"
      (match a3' with Core.Expr.Apply {arguments = [Core.Expr.Bound_variable {index = 3; _}]; _} -> true | _ -> false);
    check "a parameter passed a variable reads it as a read of its own"
      (match a2 with Core.Expr.Bound_variable {occurrence = o2; _} -> not (Core.Occurrence.equal o o2) | _ -> false)
  | _ -> check "a call is lets around the body" false );
  ( match Core_copy.call ~ty:(Core.Type.Arrow {parameter = nat; result = nat}) use (Core.Expr.Lambda {parameter = x "p"; parameter_type = nat; body = Core.Expr.fresh_rel 1}) [Core.Expr.Erased_value Core.Erasure_reason.Type_argument] with
  | Some (Core.Expr.Erased_value Core.Erasure_reason.Type_argument) -> ()
  | _ -> check "a parameter passed an erased value is that value" false );
  check "a call with too few arguments is not made" (Core_copy.call ~ty use body [a1] = None);
  check "a call with too many arguments is not made" (Core_copy.call ~ty use body [a1; a2; a3; a2] = None);
  check "a body binding fewer parameters than its type is not called"
    (Core_copy.call ~ty use (Core.Expr.Lambda {parameter = x "p"; parameter_type = nat; body = Core.Expr.Erased_value Core.Erasure_reason.Type_argument}) [a1; a2; a3] = None)
