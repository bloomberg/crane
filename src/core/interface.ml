(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Interface]: a whole extracted program's interface, the
    counterpart of [Core.Program] for module signatures. *)

(** The module signature of each module path. *)
type t = (Names.ModPath.t * Module.Signature.t) list
