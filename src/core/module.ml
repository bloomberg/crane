(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core module language: module types and their refinements,
    signatures, structures, module expressions, and a module binding
    ([t]: an implementation and its module type).  Each takes the phase
    index ({!Phase}); its [t] is the frozen instance and [extracted] the
    extracted one. *)

(** A module type: a path, a functor signature, an explicit signature, or
    one refined by a [with] constraint. *)
module Type = struct
  include Grammar.Module_type

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** A [with] refinement fixing a type or module component by path. *)
module Refinement = struct
  include Grammar.Refinement

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** One component of a module signature. *)
module Signature_item = struct
  include Grammar.Signature_item

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** A module signature's components, paired with their labels. *)
module Signature = struct
  include Grammar.Module_signature

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** One component of a module implementation. *)
module Structure_item = struct
  include Grammar.Structure_item

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** A module expression: a path, a functor, a structure or an application. *)
module Expr = struct
  include Grammar.Module_expr

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** A module structure's components, paired with their labels. *)
module Structure = struct
  include Grammar.Module_structure

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

include Grammar.Module_binding

(** A module binding of the frozen program. *)
type t = Phase.frozen at

(** A module binding of the extracted program. *)
type extracted = Phase.extracted at
