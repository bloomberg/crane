(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global references, compared under a stated identity.  See [ref.mli]. *)

open Names

module type IDENTITY = sig
  val equal : GlobRef.t -> GlobRef.t -> bool
  val compare : GlobRef.t -> GlobRef.t -> int
  val hash : GlobRef.t -> int

  module Set : CSig.USetS with type elt = GlobRef.t
  module Map : CMap.UExtS with type key = GlobRef.t and module Set := Set
  module Tbl : Hashtbl.S with type key = GlobRef.t
end

module User = struct
  include GlobRef.UserOrd
  module Set = GlobRef.Set_env
  module Map = GlobRef.Map_env
  module Tbl = Hashtbl.Make (GlobRef.UserOrd)
end

module Can = struct
  include GlobRef.CanOrd
  module Set = GlobRef.Set
  module Map = GlobRef.Map
  module Tbl = Hashtbl.Make (GlobRef.CanOrd)
end
