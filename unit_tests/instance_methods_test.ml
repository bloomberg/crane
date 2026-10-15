(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* An instance's methods as Core elaborates them: from the class field's
   declared type, the instance's class arguments and the body the record
   gives the field alone, with no C++ type chosen. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "instance_methods: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let a = Tvar (Schematic, 1)

let class_ref =
  GlobRef.IndRef (MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string "T"])) (Label.make "C")), 0)

(* An instance of [C nat], [C] binding no variable of the instance's own. *)
let inst = {Instance_methods.class_ref; type_args = [nat]; tvar_count = 0}
let add = MLglob (Global_use.monomorphic (r "add"))
let prepare field_ty body = Instance_methods.prepare_method ~freshen:false inst (r "op") field_ty body

let () =
  let op_ty = Tarr (a, Tarr (a, a)) in
  let reduced = prepare op_ty (MLlam (Id (Id.of_string "x"), nat, MLapp (add, [MLrel 1]))) in
  check "the class arguments are substituted into the declared type"
    (reduced.subst_ty = Tarr (nat, Tarr (nat, nat)));
  check "the declared arity is the field's" (reduced.declared_arity = 2);
  check "a body eta-reduced below the declared arity is expanded back to it"
    ( reduced.body
    = MLlam
        ( Id (Id.of_string "x"),
          nat,
          MLlam (Id (Id.of_string "a0"), nat, MLapp (MLapp (add, [MLrel 2]), [MLrel 1])) ) );
  let params, inner = Instance_methods.params reduced in
  check "the accessor takes each binder up to the arity as a parameter"
    (List.length params = 2 && List.for_all (fun p -> not p.Instance_methods.erased) params);
  check "the body past the parameters is the call" (inner = MLapp (MLapp (add, [MLrel 2]), [MLrel 1]));
  check "a body taking its parameters is not eta-called" (Instance_methods.eta_call reduced inner <> None);
  let point_free = prepare op_ty add in
  check "a body naming a function point-free is left as written" (point_free.body = add);
  let params, inner = Instance_methods.params point_free in
  check "a point-free body gives the accessor no parameter" (params = [] && inner = add);
  check "a point-free body is applied to a parameter per declared argument"
    ( Instance_methods.eta_call point_free inner
    = Some ([(Id.of_string "a0", nat); (Id.of_string "a1", nat)], MLapp (add, [MLrel 2; MLrel 1])) );
  let value = prepare a (MLglob (Global_use.monomorphic (r "zero"))) in
  check "a value field is not eta-called" (Instance_methods.eta_call value value.body = None)
