(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What splicing decided about the partners of a program's loopified
    functions ({!Recursion_plan.splice_partners}): which functions it
    decided, and, for each whose machine enters a copy of a partner spliced
    into its body, the local fixpoint that copy is.  A value of the program
    being normalized ({!Core.normalize}), read by the passes after it. *)

type t

(** Nothing decided. *)
val empty : t

(** [decide ?entered r s]: [s], with the partners of [r] decided -- spliced,
    one of them entered as the local fixpoint [entered], or left as they
    are. *)
val decide : ?entered:Miniml.Occurrence.t -> Names.GlobRef.t -> t -> t

(** Whether the partners of [r] are decided: splicing again leaves them as
    they are. *)
val decided : t -> Names.GlobRef.t -> bool

(** The local fixpoint the machine of [r] enters, a partner's copy spliced
    into its body. *)
val entered_copy : t -> Names.GlobRef.t -> Miniml.Occurrence.t option

(** Whether [o] is a local fixpoint some machine enters
    ({!entered_copy}). *)
val is_entered_copy : t -> Miniml.Occurrence.t -> bool

val equal : t -> t -> bool
