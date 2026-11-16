(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The context of one unit's extraction.  See [unit_context.mli]. *)

type t = {
  config : Table.unit_config;
  callables : Callable_abi.decided;
  modules : Module_plan.layout;
  scopes : Scope_plan.bound;
}

let make ~config =
  {config; callables = Callable_abi.undecided; modules = Module_plan.no_layout; scopes = Scope_plan.none}
let detached = make ~config:{Table.concurrent = false}
let non_atomic_rc u = Table.non_atomic_rc_for u.config
let count_rc u = Table.count_rc_for u.config
