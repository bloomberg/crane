(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A call as Core elaborates it, from the callee's type and the call's
   arguments alone: no C++ type is chosen, no expression generated. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "elaborated_call: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Tglob (r "nat", [], [])

let declare s ty =
  Table.add_type (r s) ty;
  MLglob (Global_use.monomorphic (r s))

let elaborate f args =
  Translation_calls.elaborate_call ~slot:Translation_support.empty_slot (Common.empty_env ())
    (Call_tyargs.of_use (Global_use.monomorphic f)) args

let () =
  let a = declare "a" nat and b = declare "b" nat and c = declare "c" nat in
  let f = r "f" in
  Table.add_type f (Tarr (nat, Tarr (nat, nat)));
  let exact = elaborate f [a; b] in
  check "a call at the callee's arity passes every argument"
    (exact.primary = [a; b] && exact.excess = [] && exact.regular = [a; b]);
  check "no dictionary, so none occupies a parameter"
    (exact.instances = [] && Elaborated_call.leading_params exact = 0);
  let over = elaborate f [a; b; c] in
  check "an argument past the arity is applied to the result"
    (over.primary = [a; b] && over.excess = [c]);
  let partial = elaborate f [a] in
  check "a partial application passes what it has" (partial.primary = [a] && partial.excess = []);
  let g = r "g" in
  Table.add_type g (Tarr (nat, Tarr (Tdummy Ktype, Tarr (nat, nat))));
  let eta = elaborate g [a; MLdummy Ktype; b] in
  check "a dummy at an erased domain is not a value argument"
    (eta.primary = [a; b] && eta.excess = []);
  check "the callee's declared type is kept" (eta.callee_type = Table.find_type g)
