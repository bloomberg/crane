(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core binder a C++ local stands for, recorded where translation
    declares the local, so that passes after translation can relate a C++
    local back to the Core variable it binds.

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

    A binder a let, a sequential bind or a pattern introduces also records
    where ({!site}), which tells two such binders apart where the scope does
    not: one at one level in each of two branches. *)

(** The term binding a binder.  A pattern binds every variable of its
    branch, one level each, so its match and the branch tell its binders
    apart from any other's: patterns are flat, a constructor applied to
    variables. *)
type site =
  | Binding of Miniml.Occurrence.t
      (** the let binding it, or the use of the bind whose continuation's
          parameter it is *)
  | Branch of Miniml.Occurrence.t * int
      (** the match and the index, among its branches, of the branch whose
          pattern binds it *)

(** A binder: the definition whose body binds it, its de Bruijn level
    there, and, for a let, bind or pattern binder, its site. *)
type t = private {
  origin : Names.GlobRef.t;  (** the definition whose Core body binds it *)
  level : int;  (** its de Bruijn level in that body, parameters included *)
  site : site option;  (** the term binding it, for a let, bind or pattern *)
}

(** [make ~origin ~level ?site ()] is the binder at [level] in [origin]'s
    body, bound at [site] if given. *)
val make : origin:Names.GlobRef.t -> level:int -> ?site:site -> unit -> t

(** The same binder among the binders in scope: origin and level. *)
val equal : t -> t -> bool

(** Whether two sites are the same binding, or the same branch of the same
    match. *)
val equal_site : site -> site -> bool

(** Whether no site tells [b] and [b'] apart: either records none, or both
    record the same one. *)
val same_site : t -> t -> bool
