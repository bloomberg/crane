(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Declaration-level C++ code generation: inductives, records, typeclasses,
    instances, and top-level function definitions. Depends on the
    expression-level codegen in {!Lower_expr}.

    The generators live in {!Decl_state}, {!Records}, {!Instances},
    {!Functions} and {!Inductives}, in dependency order; this module
    gathers them behind one interface. *)

include Decl_state
include Records
include Instances
include Functions
include Inductives
