(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What a head's relaxations decided, applied to a declaration: the rewrite a
   function generated under a planned head receives, without the head being
   decided again. *)

open Crane_plugin
open Names
open Minicpp

let check name cond =
  if not cond then (
    Printf.eprintf "head_relaxation: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let id = Id.of_string
let named s = Tvar (Tv_named (id s))
let nat = Tglob (r "nat", [], [])
let fn ret params body = Dfun (mk_dfun ~ret (r "f") (Ddef (params, body)))

let () =
  let decl = fn (Tapply (named "T1", [nat])) [(id "x", Tapply (named "T1", [nat]))] [] in
  ( match Head_relaxation.apply (Head_relaxation.Computed_return nat) decl with
  | Dfun {df_ret; df_shape = Ddef (params, _); _} ->
    check "a computed return replaces the return type" (df_ret = nat);
    check "and nothing else" (params = [(id "x", Tapply (named "T1", [nat]))])
  | _ -> check "a function stays a function" false );
  let relaxed =
    Head_relaxation.Param_applications {relaxed = [id "T1"]; deduced = [((id "T1", [nat]), id "_P0")]}
  in
  ( match Head_relaxation.apply relaxed decl with
  | Dfun {df_ret; df_shape = Ddef (params, _); _} ->
    check "an application a parameter was given is that parameter where it is passed"
      (params = [(id "x", named "_P0")]);
    check "the return type keeps the application" (df_ret = Tapply (named "T1", [nat]))
  | _ -> check "a function stays a function" false );
  let erased =
    fn (named "T2")
      [(id "x", named "T2")]
      [Sreturn (Some (CPPany_cast (named "T2", CPPvar (id "x"))))]
  in
  ( match Head_relaxation.apply (Head_relaxation.Unmentioned [id "T2"]) erased with
  | Dfun {df_ret; df_shape = Ddef (params, [Sreturn (Some (CPPany_cast (target, _)))]); _} ->
    check "an unmentioned variable is erased in the signature" (df_ret = Tany && params = [(id "x", Tany)]);
    check "but not as an any_cast's target" (target = named "T2")
  | _ -> check "a function stays a function" false );
  check "relaxations apply first first"
    ( Head_relaxation.apply_all [relaxed; Head_relaxation.Computed_return nat] decl
    = fn nat [(id "x", named "_P0")] [] )
