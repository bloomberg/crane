(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global references, compared under an identity a table's type states.

    A [GlobRef.t] carries two names.  Its {e user} name is the one a reference
    was written under: an [Include] alias, or a functor instance's copy, is a
    global of its own ({!User}).  Its {e canonical} name is the definition the
    name reaches: the alias and its target are one ({!Can}).  Which identity a
    table means is a decision about what it records -- a property of a name,
    such as which call is a self-call, or of a definition, such as which
    mapping it has -- so every table keyed by global references is built from
    one of these two modules, and its type says which.  [User.Map.t] and
    [Can.Map.t] are distinct types: a table cannot be handed to code written
    for the other identity, and no table hashes a [GlobRef.t] structurally. *)

open Names

module type IDENTITY = sig
  val equal : GlobRef.t -> GlobRef.t -> bool
  val compare : GlobRef.t -> GlobRef.t -> int
  val hash : GlobRef.t -> int

  module Set : CSig.USetS with type elt = GlobRef.t
  module Map : CMap.UExtS with type key = GlobRef.t and module Set := Set
  module Tbl : Hashtbl.S with type key = GlobRef.t
end

(** Identity of the name a reference was written under ([GlobRef.UserOrd]). *)
module User : IDENTITY

(** Identity of the definition a reference reaches ([GlobRef.CanOrd]). *)
module Can : IDENTITY
