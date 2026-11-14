(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What a head's relaxations decided, applied to a declaration: the rewrite a
   function generated under a planned head receives, without the head being
   decided again. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "head_relaxation: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let id = Id.of_string
let named s : Cpp_ir.Lowered.Type.t = Variable (Named (id s))
let nat : Cpp_ir.Lowered.Type.t = Entity_application (r "nat", [], [])

let fn ret params body : Cpp_ir.Lowered.Decl.t =
  Function
    { path = {outer = (r "f", []); inner = []};
      return_type = ret;
      no_pure = false;
      constexpr = Undecided;
      shape = Definition (params, body);
      binders = [];
      loop = None }

let () =
  let decl = fn (Apply (named "T1", [nat])) [(id "x", Apply (named "T1", [nat]))] [] in
  ( match Head_relaxation.apply (Head_relaxation.Computed_return nat) decl with
  | Function {return_type; shape = Definition (params, _); _} ->
    check "a computed return replaces the return type" (return_type = nat);
    check "and nothing else" (params = [(id "x", Apply (named "T1", [nat]))])
  | _ -> check "a function stays a function" false );
  let relaxed = Head_relaxation.Param_applications {relaxed = [id "T1"]; deduced = [((id "T1", [nat]), id "_P0")]} in
  ( match Head_relaxation.apply relaxed decl with
  | Function {return_type; shape = Definition (params, _); _} ->
    check "an application a parameter was given is that parameter where it is passed"
      (params = [(id "x", named "_P0")]);
    check "the return type keeps the application" (return_type = Apply (named "T1", [nat]))
  | _ -> check "a function stays a function" false );
  let erased = fn (named "T2") [(id "x", named "T2")] [Return (Some (Any_cast (named "T2", Local (id "x"))))] in
  ( match Head_relaxation.apply (Head_relaxation.Unmentioned [id "T2"]) erased with
  | Function {return_type; shape = Definition (params, [Return (Some (Any_cast (target, _)))]); _} ->
    check "an unmentioned variable is erased in the signature" (return_type = Any && params = [(id "x", Any)]);
    check "but not as an any_cast's target" (target = named "T2")
  | _ -> check "a function stays a function" false );
  check "relaxations apply first first"
    (Head_relaxation.apply_all [relaxed; Head_relaxation.Computed_return nat] decl = fn nat [(id "x", named "_P0")] [])
