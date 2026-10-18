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
    ({!Decl}, {!Unprinted}).  A declaration is either printed already, or
    printed by {!print} as the tree says it is spelled: as an element of the
    module a group of declarations was generated in ({!Elements}), or as a
    member of the struct around it ({!Module}).  Everything else is text,
    already formatted: the concept text around a struct is the driver's. *)

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

(** How a declaration not yet printed is spelled, which is what printing it
    reads off where the tree puts it. *)
type spelling =
  | Element_of of ModPath.t
      (** As the header spells an element of the module: in the visibility
          planned for its body and in its planned header scope, wherever it
          is written. *)
  | Member_of of ModPath.t
      (** As a member of the module's struct: as the header spells an
          element of the module, but inside the struct whatever its planned
          header scope says -- a library module writes its types at
          namespace scope and its functions in a struct of its name. *)

(** A declaration not yet printed, in the name environment it is printed
    in, with what placing the declarations it needs reads -- planned, so
    known before it is printed. *)
type unprinted = {env : Common.env; declaration : Cpp_erasure.settled; needs : Needs.t}

type t = private
  | Text of Pp.t  (** Written as it is; nothing is placed by it. *)
  | Decl of {text : Pp.t; needs : Needs.t}  (** A declaration, as printed. *)
  | Unprinted of unprinted
      (** A declaration {!print} prints, spelled as the innermost {!Elements}
          or struct {!Module} around it says. *)
  | Elements of {source : ModPath.t; elements : t}
      (** Declarations generated in the module [source], written here and
          spelled as its elements are. *)
  | Seq of t list  (** One after the other. *)
  | Top_level of t
      (** A chunk at namespace scope: a namespace-scope declaration due
          before it goes in front of it.  Never empty. *)
  | Module of {module_ : ModPath.t; enclosure : enclosure; fields : t; members : t list}
      (** The body of [module_] as the file writes it: [fields], then its
          elements, each a member of it that a template homed in [module_]
          goes in front of -- in order, none empty -- inside the struct
          [enclosure] writes, if any, which closes them on a line of its
          own.  Empty only where no struct is written and there is nothing
          in it. *)
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

(** [unprinted ~needs env d] is [d], printed in [env] where the tree puts
    it. *)
val unprinted : needs:Needs.t -> Common.env -> Cpp_erasure.settled -> t

(** [elements ~source t] is [t], spelled as the elements of [source] are. *)
val elements : source:ModPath.t -> t -> t
val seq : t list -> t

(** [t] as a chunk at namespace scope; nothing, if [t] is. *)
val top_level : t -> t

(** The elements of a module's body as written, before the file decides
    what encloses them. *)
type body

(** [module_body mp l] is the body of the module [mp] whose elements are written
    [l], in order; the empty ones write nothing and are not members. *)
val module_body : ModPath.t -> t list -> body

(** Whether [body] has no members. *)
val body_is_empty : body -> bool

(** [module_ enclosure ~fields body] writes [body] as {!Module}; nothing, if
    that writes nothing.
    @raise Invalid_argument if [enclosure] is a struct and [fields] or a
    member holds a {!Top_level} chunk: nothing inside a struct is at
    namespace scope. *)
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
    text.
    @raise Invalid_argument if that is a declaration not yet printed. *)
val starts_with_doc_comment : t -> bool

(** [t] as a document, for reading.
    @raise Invalid_argument if it holds a declaration not yet printed. *)
val to_pp : t -> Pp.t

(** [t] as a document, each declaration not yet printed printed by [write],
    in the order written, as the tree spells it.
    @raise Invalid_argument if one is outside every {!Elements} and struct
    {!Module}: nothing says how it is spelled. *)
val print_tree : write:(spelling -> unprinted -> Pp.t) -> t -> Pp.t

(** The break between two declaration groups.  It is a break hint, not a
    forced newline, so the vertical box the whole file is printed in
    ([Extract_env]) decides where it falls; clang-format keeps the blank
    lines it leaves. *)
val cut2 : unit -> Pp.t

(** {2 Translation units} *)

(** A synthesised template a file declares: by its name, whether it is
    homed -- declared in the struct of the module whose member writes it,
    because its body names what only that struct declares -- and whether it
    is a holder -- a struct -- rather than an alias. *)
type template = {name : string; homed : bool; holder : bool; declaration : Pp.t}

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
    declaration that writes it: a homed one, in each module struct whose
    members write it, in front of the innermost member holding it, any
    other in front of the innermost chunk at namespace scope, holders in
    front of aliases.  One written
    outside every chunk goes after the prologue; one nothing writes, nowhere.
    A forward declaration goes in front of the innermost chunk at namespace
    scope holding the first declaration that names its struct, unless that
    chunk defines the struct. *)
val schedule : templates:template list -> forwards:forward list -> translation_unit -> scheduled

(** The scheduled unit as a document, as {!print_tree} writes each
    section. *)
val print : write:(spelling -> unprinted -> Pp.t) -> scheduled -> Pp.t
