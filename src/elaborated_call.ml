(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A global call as Core elaborates it.  See [elaborated_call.mli]. *)

type t = {
  callee : Names.GlobRef.t;
  callee_type : Miniml.ml_type;
  primary : Miniml.ml_ast list;
  excess : Miniml.ml_ast list;
  instances : Miniml.ml_ast list;
  erased_instances : int;
  regular : Miniml.ml_ast list;
  tyargs : Call_tyargs.t;
}

let make ~callee ~callee_type ~primary ~excess ~instances ~erased_instances ~regular ~tyargs =
  {callee; callee_type; primary; excess; instances; erased_instances; regular; tyargs}

let leading_params c = List.length c.instances + c.erased_instances
let dictionary_filled c = Call_tyargs.resolved_from Call_tyargs.Argument_heads c.tyargs
