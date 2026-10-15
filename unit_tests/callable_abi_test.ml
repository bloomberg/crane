(* A declared template head read as an ABI plan: every parameter's origin
   and write policy, and a scheme variable found by identity wherever the
   head put it. *)

open Crane_plugin
open Callable_abi

let check name cond =
  if not cond then (
    Printf.eprintf "callable_abi: %s\n" name;
    exit 1 )

let callee = Names.GlobRef.VarRef (Names.Id.of_string "f")
let id = Names.Id.of_string

let () =
  let scheme = Scheme.Id.fresh callee ~arity:2 in
  let var i = Option.get (Scheme.Var.of_tvar scheme i) in
  (* A dictionary first, the second variable, the first moved last with a
     default, a deduced callable, and a parameter the declaration made up. *)
  let abi =
    of_head ~callee ~scheme:(Some scheme)
      [ (Minicpp.TTtypename, Common.tc_instance_id 0);
        (Minicpp.TTtypename, Minicpp.tvar_id 2);
        (Minicpp.TTfun ([], Minicpp.Tvoid), Common.fun_tparam_id 0);
        (Minicpp.TTtypename, id "CraneP0");
        (Minicpp.TTtypename_default Minicpp.Tvoid, Minicpp.tvar_id 1) ]
  in
  let origins = List.map (fun p -> p.origin) (template_head abi) in
  check "origins"
    ( match origins with
    | [From_instance 0; From_scheme v2; From_callable 0; Derived _; From_scheme v1] ->
      Scheme.Var.equal v2 (var 2) && Scheme.Var.equal v1 (var 1)
    | _ -> false );
  check "policies"
    ( List.map (fun p -> p.write) (template_head abi)
      |> function
      | [Writable; Writable; Deduce_only; Writable; Defaulted _] -> true
      | _ -> false );
  check "a variable is found where the head put it"
    (Option.map (fun p -> Template_param.position p.id) (parameter_of_var abi (var 1)) = Some 4
     && Option.map (fun p -> Template_param.position p.id) (parameter_of_var abi (var 2)) = Some 1);
  check "valid" (validate abi = []);
  (* A name that merely looks generated is not the variable's. *)
  let other = of_head ~callee ~scheme:(Some scheme) [(Minicpp.TTtypename, id "T01")] in
  check "T01 is no variable"
    (match template_head other with [{origin = Derived _; _}] -> true | _ -> false);
  (* A plan of a callable Crane does not generate states its scheme. *)
  let f = foreign ~callee ~scheme:(Some scheme) () in
  check "foreign plans one writable parameter per variable"
    ( List.map (fun p -> (p.origin, p.write)) (template_head f)
      |> function
      | [(From_scheme a, Writable); (From_scheme b, Writable)] ->
        Scheme.Var.equal a (var 1) && Scheme.Var.equal b (var 2)
      | _ -> false );
  (* How the value parameters are passed is part of the head. *)
  let owned = of_head ~passing:[Owned; Borrowed] ~callee ~scheme:(Some scheme) [] in
  let borrowed = of_head ~passing:[Borrowed; Borrowed] ~callee ~scheme:(Some scheme) [] in
  check "passing is part of the plan"
    (passing owned = Some [Owned; Borrowed] && not (equal owned borrowed));
  check "a foreign plan does not say how it passes" (passing f = None)
