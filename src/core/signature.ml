(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What extraction kept and erased of a PCUIC object's arguments, and the
    interface view of a Core entity ([Core.Signature.Declaration]). *)

module Argument = Grammar.Signature.Argument

type t = Grammar.Signature.t

module Declaration = struct
  include Grammar.Signature.Declaration

  (** A declaration of the frozen program ({!Phase.frozen}). *)
  type t = Phase.frozen at

  (** A declaration of the extracted program, which may hold
      metavariables. *)
  type extracted = Phase.extracted at
end
