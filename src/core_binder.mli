(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core binder a C++ local stands for, recorded where translation
    declares the local (docs/Pipeline-Disentangling-Plan.md, Milestone 6).

    A binder is named by the definition whose Core body binds it and by its
    de Bruijn level there: the number of binders, the definition's parameters
    included, it is bound under in the body as translation generates it
    ({!Core_elaborate.generated_definition}), where an inlined alias binds
    nothing.  Two binders of one definition at one level
    are never in scope together, so among the binders in scope at a point the
    level tells them apart -- which is what a pass reading a variable's
    binding through the scope it is read in needs, and all it needs.  The C++
    spelling of the local is not part of it: translation renames a binder to
    avoid a clash and names a constructor field after the field, not after
    the pattern variable.

    A binder a let or a sequential bind introduces also records that term
    ({!site}), which tells two such binders apart where the scope does not:
    one at one level in each of two branches. *)

type t = private {
  origin : Names.GlobRef.t;
  level : int;
  site : Miniml.Occurrence.t option;
      (** the let binding it, or the use of the bind whose continuation's
          parameter it is, where one does *)
}

val make : origin:Names.GlobRef.t -> level:int -> ?site:Miniml.Occurrence.t -> unit -> t

(** The same binder among the binders in scope: origin and level. *)
val equal : t -> t -> bool

(** Whether no site tells [b] and [b'] apart: either records none, or both
    record the same one. *)
val same_site : t -> t -> bool
