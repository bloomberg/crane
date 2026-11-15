(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A whole extracted program's interface: the module signature of each
    module path. *)
type t = (Names.ModPath.t * Module.Signature.t) list
