(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core binder a C++ local stands for, recorded where translation
    declares the local (docs/Pipeline-Disentangling-Plan.md, Milestone 6).

    A binder is named by the definition whose Core body binds it and by its
    de Bruijn level there: the number of binders, the definition's parameters
    included, it is bound under in the body as translation generates it
    ({!Core_elaborate.generated_scope}), where an inlined alias binds
    nothing.  Two binders of one definition at one level
    are never in scope together, so among the binders in scope at a point the
    level tells them apart -- which is what a pass reading a variable's
    binding through the scope it is read in needs, and all it needs.  The C++
    spelling of the local is not part of it: translation renames a binder to
    avoid a clash and names a constructor field after the field, not after
    the pattern variable. *)

type t = private {
  origin : Names.GlobRef.t;
  level : int;
}

val make : origin:Names.GlobRef.t -> level:int -> t

val equal : t -> t -> bool
