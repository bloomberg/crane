(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ a file writes, as a tree, before it is printed
    (docs/Pipeline-Disentangling-Plan.md, section 4.13: the seed of
    [CppAST]).

    A file is assembled out of chunks the driver moves around -- a module's
    struct to the top, a concept ahead of everything, a member definition to
    the end -- and some declarations are only due once that is settled: a
    synthesised template goes in front of the first chunk, in the order the
    file is finally written, holding a declaration that writes it.  Where
    that is can only be read off the assembled file, so the file has to be
    a value that says, for every chunk, what it is and what it needs.

    This is that value.  It records only what placing a declaration reads:
    where a chunk at namespace scope begins ({!Top_level}), where a member of
    a module's struct begins ({!Member}), and each declaration with what it
    needs in front of it ({!Decl}).  Everything else is text, already
    formatted: a declaration's own text is still the printer's, and the
    struct and concept text around it is the driver's. *)

open Names

(** What placing the declarations a written declaration needs reads off it,
    each by the name it is declared under. *)
module Needs : sig
  type t = {
    templates : string list;  (** The synthesised templates it writes. *)
    names : string list;
        (** Of the structs the file forward-declares as constrained
            templates, those it names or defines. *)
    defines : string list;  (** Of those, the ones it defines. *)
  }

  val none : t
  val is_none : t -> bool
end

type t = private
  | Text of Pp.t  (** Written as it is; nothing is placed by it. *)
  | Decl of {text : Pp.t; needs : Needs.t}  (** A declaration, as printed. *)
  | Seq of t list  (** One after the other. *)
  | Top_level of t
      (** A chunk at namespace scope: a namespace-scope declaration due
          before it goes in front of it.  Never empty. *)
  | Member of ModPath.t * t
      (** A member of the struct of the module: a template homed in the
          module goes in front of it.  Never empty. *)

val text : Pp.t -> t
val empty : t
val decl : needs:Needs.t -> Pp.t -> t
val seq : t list -> t

(** [t] as a chunk at namespace scope; nothing, if [t] is. *)
val top_level : t -> t

(** [t] as a member of the struct of [mp]; nothing, if [t] is. *)
val member : ModPath.t -> t -> t

(** Whether [t] writes nothing, which is whether its text is empty: a
    declaration needing something is not. *)
val is_empty : t -> bool

(** [concat sep l] writes [l] with [sep ()] between each two, as
    [Pp.prlist_with_sep]. *)
val concat : (unit -> Pp.t) -> t list -> t

(** [t] as a document, for reading. *)
val to_pp : t -> Pp.t

(** {2 Transitional}

    The tags the assembled document carries for {!Cpp.place_due_declarations},
    which reads the slots and needs back out of the printed file. *)

val top_slot_tag : string
val member_slot_tag : string

type carried =
  | Writes of string list
  | Names of string list
  | Defines of string list

val carried_by : string -> carried option
