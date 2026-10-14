(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the template parameters of a generated inductive or alias are, by
    0-based position in its C++ template parameter list.  Planned before
    anything is rendered ({!Target_plan.template_kinds}) and recorded again
    when the declaration's header is generated; emptied by
    [Table.reset_tables]. *)

open Names

(** One declaration's parameter kinds. *)
type t = {
  template_templates : (int * int) list;
      (** The positions declared [template <typename> class], each with its
          arity: a use must pass a bare template name there. *)
  families : int list;
      (** The positions applied in the definition but still declared a plain
          [typename] -- event families. *)
  phantoms : int list;  (** The positions the definition never spells. *)
}

val equal : t -> t -> bool

val reset : unit -> unit

(** Table sizes, for [Table.census]. *)
val sizes : unit -> (string * int) list

(** Record [r]'s kinds. *)
val record : GlobRef.t -> t -> unit

(** The kinds recorded for [r]; no position of any kind if none were. *)
val recorded : GlobRef.t -> t

val template_template_arity : GlobRef.t -> int -> int option
val is_family : GlobRef.t -> int -> bool

(** Whether [r] has any family position. *)
val has_family : GlobRef.t -> bool

val is_phantom : GlobRef.t -> int -> bool
