(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Match]: the branches of a [Core.Expr.Match] ([Core.Match.Branch]). *)

module Branch = struct
  include Grammar.Match.Branch

  (** A branch of the frozen program ({!Phase.frozen}). *)
  type t = Phase.frozen at

  (** A branch of the extracted program, which may hold metavariables. *)
  type extracted = Phase.extracted at
end
