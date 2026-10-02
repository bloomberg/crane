(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Declaration-level C++ code generation: inductives, records, typeclasses,
    instances, and top-level function definitions. Depends on the
    expression-level codegen in {!Translation}. *)

(** The generators live in {!Gen_context}, {!Gen_records}, {!Gen_instances},
    {!Gen_functions} and {!Gen_inductives}, in dependency order; this module
    gathers them behind one interface. *)

include Gen_context
include Gen_records
include Gen_instances
include Gen_functions
include Gen_inductives
