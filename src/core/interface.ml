(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Interface]: a whole extracted program's interface, the
    counterpart of [Core.Program] for module signatures. *)

(** The module signature of each module path, at the phase ['p]. *)
type 'p at = (Names.ModPath.t * 'p Module.Signature.at) list

(** A frozen interface ({!Phase.frozen}). *)
type t = Phase.frozen at

(** An extracted interface, which may hold metavariables. *)
type extracted = Phase.extracted at
