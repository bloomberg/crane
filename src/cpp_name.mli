(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A C++ name as resolution settled it, before it is flattened to text
    (docs/Pipeline-Disentangling-Plan.md, Milestone 9, the seed of
    [CppAST.Name]).

    Callers used to recover facts about a name from its printed string:
    testing for a [':'] to see whether it came out qualified, capitalising
    whatever follows the last ["::"], or scanning a rendered declaration for
    the identifier in front of each ["::"] to decide what the declaration
    asks of the file.  The string cannot say what a qualifier {e is} -- a
    namespace, a struct, a template parameter -- and those are different
    questions for the compiler reading it: naming into a namespace asks only
    that the name be declared, naming into a struct asks that the struct be
    complete, and naming into a template parameter asks nothing until the
    template is instantiated.  The code that writes the qualifier knows
    which; this type is how it says so. *)

(** What a qualifier written in front of a name is. *)
type scope =
  | Global  (** The global namespace: a leading [::] alone. *)
  | Namespace of string
      (** A namespace: a library's ([std], [crane]) or a file's. *)
  | Class of string
      (** A struct: a module's, an inductive's, a record's, a collision
          wrapper's. *)
  | Parameter of string
      (** A template parameter, or a member of one: a functor's argument
          module, a type class instance. *)

(** A name: resolved, its qualifiers outermost first, or the replacement text
    of a custom extraction, which is written verbatim and is whatever the
    user wrote. *)
type t = private
  | Name of {scopes : scope list; base : string}
  | Foreign of string

(** [name scopes base] is [base] qualified by [scopes], outermost first.  A
    namespace, struct or parameter whose text is empty is no qualifier at
    all -- a monolithic extraction's file -- and is dropped, as the printed
    text drops it. *)
val name : scope list -> string -> t

(** An unqualified name. *)
val unqualified : string -> t

(** The replacement text of a custom extraction. *)
val foreign : string -> t

(** The text a qualifier is written with, without its trailing [::]. *)
val scope_text : scope -> string

(** The qualifiers, outermost first; a foreign name has none it can name. *)
val scopes : t -> scope list

(** The final component: the base of a resolved name, and for a foreign one
    the text after its last [::]. *)
val base : t -> string

(** Whether the name comes out with a [::] qualifier.  For a foreign name,
    whether its text contains one. *)
val is_qualified : t -> bool

(** [s] in front of the name's qualifiers; in front of a foreign name's
    text, which stays foreign. *)
val within : scope -> t -> t

(** [inside outer kind n] is [n] written inside [outer], whose final
    component becomes a qualifier of the kind [kind]: [List] and [list] make
    [List::list].  A foreign [outer] or [n] leaves only text to join, and the
    result is foreign. *)
val inside : t -> (string -> scope) -> t -> t

(** The name with its final component replaced by [f] of it. *)
val map_base : (string -> string) -> t -> t

(** The name with its innermost qualifier taken as its final component:
    [A::b] is [A].  [None] for an unqualified or foreign name. *)
val enclosing : t -> t option

(** The name as text. *)
val to_string : t -> string

(** The name as a document, each qualifier tagged with what it is, so that
    {!written} can read the kinds back from a rendered declaration.
    [template_keyword] writes the [template] disambiguator in front of the
    final component of a qualified name: [C::template f]. *)
val pp : ?template_keyword:bool -> t -> Pp.t

(** A qualifier as a document, tagged, with its trailing [::]. *)
val pp_scope : scope -> Pp.t

(** Qualifiers as a document, outermost first. *)
val pp_scopes : scope list -> Pp.t

(** [n] written as the qualifier of what follows it, its final component a
    qualifier of the kind [kind]: [List] in [List::cons]. *)
val pp_qualifier : (string -> scope) -> t -> Pp.t

(** A rendered type written as the qualifier of what follows it, as a
    qualifier of the kind [kind] whose text is the rendering: [_tcI0] in
    [typename _tcI0::addr].  The qualifiers written inside the rendering are
    its own business, and {!written} does not look inside it. *)
val pp_type_qualifier : (string -> scope) -> Pp.t -> Pp.t

val equal : t -> t -> bool

(** What a rendered document qualifies its names by, in the order written. *)
type written =
  | Scope of scope  (** a qualifier written through {!pp} *)
  | Foreign_text of string  (** a foreign name's text *)
  | Untagged of string
      (** a run of text no qualifier was tagged in, which may still contain
          a ["::"] some other path wrote *)

val written : Pp.t -> written list
