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

    This is that value.  It records what placing a declaration reads: where
    a chunk at namespace scope begins ({!Top_level}), the body of each module
    with the struct written around it, if any, and each of its members
    ({!Module}), and each declaration with what it needs in front of it
    ({!Decl}).  Everything else is text, already formatted: a declaration's
    own text is still the printer's, and the concept text around a struct is
    the driver's. *)

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
  val union : t -> t -> t
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
  | Module of {module_ : ModPath.t; enclosure : enclosure; fields : t; members : t list}
      (** The body of [module_] as the file writes it: [fields], then its
          elements, each a member of it that a template homed in [module_]
          goes in front of -- in order, none empty -- inside the struct
          [enclosure] writes, if any.  Empty only where no struct is
          written and there is nothing in it. *)
  | Declarations of Pp.t list
      (** Declarations {!schedule} placed in front of what follows it; no
          tree built before scheduling has one. *)

(** Where the members of a module's body are written. *)
and enclosure =
  | Struct of {head : Pp.t; tail : Pp.t}
      (** In the header, inside the module's struct, which [head] opens and
          [tail] closes. *)
  | Out_of_line
      (** In the implementation, which writes no struct: they are defined
          out of line, by the struct the header declares. *)
  | In_enclosing_scope
      (** In the header, where a class concept takes the module's name: in
          whatever scope encloses the module, with no struct of its own. *)

val text : Pp.t -> t
val empty : t
val decl : needs:Needs.t -> Pp.t -> t
val seq : t list -> t

(** [t] as a chunk at namespace scope; nothing, if [t] is. *)
val top_level : t -> t

(** [t] as a member of the struct of [mp]; nothing, if [t] is. *)
val member : ModPath.t -> t -> t

(** The elements of a module's body as written, before the file decides
    what encloses them. *)
type body

(** [module_body mp l] is the body of the module [mp] whose elements are written
    [l], in order; the empty ones write nothing and are not members. *)
val module_body : ModPath.t -> t list -> body

(** Whether [body] has no members. *)
val body_is_empty : body -> bool

(** [module_ enclosure ~fields body] writes [body] as {!Module}; nothing, if
    that writes nothing. *)
val module_ : enclosure -> ?fields:t -> body -> t

(** Whether [t] writes nothing, which is whether its text is empty: a
    declaration needing something is not. *)
val is_empty : t -> bool

(** [concat sep l] writes [l] with [sep ()] between each two, as
    [Pp.prlist_with_sep]. *)
val concat : (unit -> Pp.t) -> t list -> t

(** What the declarations of [t] need, together. *)
val needs : t -> Needs.t

(** Whether the first text [t] writes opens a doc comment, scheduled
    declarations aside; a soft break, which may print as nothing, is no
    text. *)
val starts_with_doc_comment : t -> bool

(** [t] as a document, for reading. *)
val to_pp : t -> Pp.t

(** The break between two declaration groups.  It is a break hint, not a
    forced newline, so the vertical box the whole file is printed in
    ([Extract_env]) decides where it falls; clang-format keeps the blank
    lines it leaves. *)
val cut2 : unit -> Pp.t

(** {2 Translation units} *)

(** A synthesised template a file declares: by its name, the module whose
    struct it is declared in if any, and whether it is a holder -- a struct
    -- rather than an alias. *)
type template = {name : string; home : ModPath.t option; holder : bool; declaration : Pp.t}

(** A constrained template's forward declaration, by the name of the struct
    it declares. *)
type forward = {struct_ : string; forward_declaration : Pp.t}

(** A file as the driver assembled it: what opens it, and its sections, in
    the order written. *)
type translation_unit = {prologue : Pp.t; sections : t list}

(** A translation unit with every due declaration placed. *)
type scheduled

(** [schedule ~templates ~forwards u] places each of [templates], in the
    order given, and each of [forwards] in front of the chunk of [u] that
    first needs it, reading the chunks in the order written.

    A template goes in front of the innermost chunk holding the first
    declaration that writes it: one homed in a module in front of that
    member of the module's struct, any other in front of the innermost
    chunk at namespace scope, holders in front of aliases.  One written
    outside every chunk goes after the prologue; one nothing writes, nowhere.
    A forward declaration goes in front of the innermost chunk at namespace
    scope holding the first declaration that names its struct, unless that
    chunk defines the struct. *)
val schedule : templates:template list -> forwards:forward list -> translation_unit -> scheduled

(** The scheduled unit as a document. *)
val print : scheduled -> Pp.t

(** [u] with each module's body written as it was before {!Module}: struct
    text around a member list, for checking. *)
val legacy_unit : translation_unit -> translation_unit
