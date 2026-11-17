(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Program]: a whole extracted program's implementation, what
    extraction hands to the Core passes ({!Core_passes.Phase}). *)

(** The module structure of each module path, in dependency order, at the
    phase ['p]. *)
type 'p at = (Names.ModPath.t * 'p Module.Structure.at) list

(** A frozen program ({!Phase.frozen}). *)
type t = Phase.frozen at

(** An extracted program, which may hold metavariables. *)
type extracted = Phase.extracted at
