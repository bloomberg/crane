(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Program]: a whole extracted program's implementation, what
    extraction hands to the Core passes ({!Core_phase}). *)

(** The module structure of each module path, in dependency order. *)
type t = (Names.ModPath.t * Module.Structure.t) list
