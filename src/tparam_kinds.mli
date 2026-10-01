(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the template parameters of a generated inductive or alias are, by
    0-based position in its C++ template parameter list.  Filled when the
    declaration's header is generated; emptied by [Table.reset_tables]. *)

open Names

val reset : unit -> unit

(** Table sizes, for [Table.census]. *)
val sizes : unit -> (string * int) list

(** Record the positions declared [template <typename> class], each with its
    arity: a use must pass a bare template name there. *)
val add_template_template : GlobRef.t -> (int * int) list -> unit

val template_template_arity : GlobRef.t -> int -> int option

(** Record the positions applied in the definition but still declared a plain
    [typename] -- event families. *)
val add_family : GlobRef.t -> int list -> unit

val is_family : GlobRef.t -> int -> bool

(** Whether [r] has any family position. *)
val has_family : GlobRef.t -> bool

(** Record the positions the definition never spells. *)
val add_phantom : GlobRef.t -> int list -> unit

val is_phantom : GlobRef.t -> int -> bool
