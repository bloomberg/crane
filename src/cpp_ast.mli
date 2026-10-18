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
    already formatted: the head and tail of a struct are the driver's. *)

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
      (** As an element of the module, wherever it is written: in its body
          as planned -- the visibility, the inductives it spells bare, and
          what the module frames around it demote and hold back -- and in
          the header's planned scope for it, or, in the implementation, at
          file scope, where a definition is qualified by its own plan. *)
  | Member_of of ModPath.t
      (** As a member of the module's struct, which only the header writes:
          as an element of the module, but inside the struct whatever its
          planned header scope says -- a library module writes its types
          at namespace scope and its functions in a struct of its name. *)

(** What a declaration not yet printed declares. *)
type declaration =
  | Declaration of {env : Common.env; settled : Cpp_erasure.settled}
      (** A finished declaration, printed in the name environment [env]. *)
  | Fields of {record : GlobRef.t; vars : Id.t list; fields : (string * Minicpp.cpp_type) list}
      (** The fields of the eponymous record [record] merged into its
          module's struct, each by its name and type, the type variables
          they name named [vars]: no declaration holds them. *)
  | Modtype_concept of {path : ModPath.t; params : ModPath.t list; concept : Modtype_concept.t}
      (** The concept the module type at [path] becomes, generated as
          [concept], over the parameters [params] of a functor declaring
          it. *)
  | Global_alias of global_alias
      (** [using N = ::N;]: a member standing in for a type declared under
          the same name at namespace scope, where the file moved it, so that
          the struct still names it.  Not a declaration of the program's:
          one of the file's layout. *)
  | Assertion of assertion
      (** [static_assert(C<S>);], on a line of its own: that a module or an
          instance satisfies a concept. *)

(** That [subject] satisfies [concept], each named as written where the
    assertion is: a subject declared in a struct the assertion follows is
    qualified by it. *)
and assertion = {concept : asserted; subject : subject}

(** The concept an {!assertion} asserts. *)
and asserted =
  | Of_module_type of ModPath.t  (** That of the module type at the path. *)
  | Of_class of GlobRef.t  (** That of the type class. *)

(** What an {!assertion} asserts it of. *)
and subject =
  | Module of ModPath.t  (** The struct the module is written as. *)
  | Instance of {instance : GlobRef.t; args : Minicpp.cpp_type list}
      (** The instance, as a type, with the class's further arguments. *)

(** What a {!Global_alias} stands in for. *)
and global_alias =
  | Alias_of_type of {target : GlobRef.t; tparams : (Minicpp.template_type * Id.t) list}
      (** The type [target] declares, over [tparams], which the alias
          repeats: [template <tparams> using N = ::N<tparams>;]. *)
  | Alias_of_module of ModPath.t
      (** The struct a module is written as. *)

(** A declaration not yet printed, with what placing the declarations it
    needs reads -- planned, so known before it is printed. *)
type unprinted = {declaration : declaration; needs : Needs.t}

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
  | Joined of t list
      (** One after the other, each two separated by a break, or by a
          newline where what follows opens with a doc comment -- which
          {!print} reads once every declaration in it is printed.  At least
          two, none empty. *)
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
  | Struct of {head : struct_head; layout : layout}
      (** In the header, inside the module's struct, which [head] opens and
          [};] closes. *)
  | Out_of_line
      (** In the implementation, which writes no struct: they are defined
          out of line, by the struct the header declares. *)
  | In_enclosing_scope
      (** In the header, where a class concept takes the module's name: in
          whatever scope encloses the module, with no struct of its own. *)

(** What a struct's head declares, each name in it as spelled where the
    struct is written: [template <template> struct name : public base]. *)
and struct_head = {
  template : template_param list;  (** None if the struct is no template. *)
  name : Pp.t;
  base : Pp.t option;  (** The class it derives from, if any. *)
}

(** A parameter of a struct's template, by its name. *)
and template_param =
  | Typename of Pp.t  (** [typename T]. *)
  | Constrained of {concept : Pp.t; param : Pp.t}
      (** [C<..> M], the concept applied to any further arguments. *)

(** How a struct's braces are laid out. *)
and layout =
  | Block  (** The body opens on a line of its own. *)
  | One_line  (** [struct N {};]: there is no body. *)

val text : Pp.t -> t
val empty : t

(** [template<..>] and a line break, if [params] is not empty; nothing
    otherwise. *)
val pp_template_head : template_param list -> Pp.t
val decl : needs:Needs.t -> Pp.t -> t

(** [unprinted ~needs env d] is [d], printed in [env] where the tree puts
    it. *)
val unprinted : needs:Needs.t -> Common.env -> Cpp_erasure.settled -> t

(** [fields ~needs ~record ~vars fields] is {!Fields}, printed where the
    tree puts it. *)
val fields : needs:Needs.t -> record:GlobRef.t -> vars:Id.t list -> (string * Minicpp.cpp_type) list -> t

(** [modtype_concept ~path ~params c] is {!Modtype_concept}, printed where
    the tree puts it.  It needs nothing placed in front of it. *)
val modtype_concept : path:ModPath.t -> params:ModPath.t list -> Modtype_concept.t -> t

(** [global_alias a] is {!Global_alias}, printed where the tree puts it.
    It writes no synthesised template and names no constrained struct but
    the one it stands in for, which it does not define. *)
val global_alias : global_alias -> t

(** [assertion a] is {!Assertion}, printed where the tree puts it.  It
    needs nothing placed in front of it. *)
val assertion : assertion -> t

(** [elements ~source t] is [t], spelled as the elements of [source] are. *)
val elements : source:ModPath.t -> t -> t
val seq : t list -> t

(** [joined l] is the non-empty ones of [l] as {!Joined}; the one, if only
    one is; nothing, if none is. *)
val joined : t list -> t

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
    namespace scope; or if it is a struct laid out on one line and [fields]
    or [body] writes anything. *)
val module_ : enclosure -> ?fields:t -> body -> t

(** Whether [t] writes nothing, which is whether its text is empty: a
    declaration needing something is not. *)
val is_empty : t -> bool

(** [concat sep l] writes [l] with [sep ()] between each two, as
    [Pp.prlist_with_sep]. *)
val concat : (unit -> Pp.t) -> t list -> t

(** What the declarations of [t] need, together. *)
val needs : t -> Needs.t

(** What [t] declares in the scope it is written in, in the order written:
    a declaration not yet printed, or a module's struct -- nothing inside
    one. *)
type declared = Declared of declaration | Struct_of of ModPath.t

val declared : t -> declared list

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

(** A file as the driver assembled it, in the order written: the forward
    declarations of the structs it names ahead of their definitions, then
    one section after another, each a chunk at namespace scope.  A section
    of groups writes nothing if every group is empty, and otherwise its
    non-empty groups, with a break between each two -- a line break between
    erased aliases -- and one after the last. *)
type translation_unit = {
  forward_declarations : Pp.t list;
  erased_aliases : t list;
      (** Erasure landing pads ([using X = std::any;]) and the imports of
          promoted aliases, ahead of the concepts that spell them. *)
  concept_prerequisites : t list;  (** The top-level elements the concepts cannot be read without. *)
  concepts : t list;  (** The concepts only namespace scope can hold. *)
  hoisted_structs : t list;  (** The structs of the modules declared ahead of the file. *)
  lifted_specs : t list;
      (** The declarations of lifted helpers, ahead of everything that could
          call them. *)
  body : t;  (** The modules, each at its turn. *)
  deferred_definitions : t list;  (** Out-of-line definitions, each after a break. *)
  deferred_members : t list;
      (** Datatype members whose bodies name a module's struct, last of
          all, after a break. *)
}

(** A translation unit with every due declaration placed. *)
type scheduled

(** [schedule ~templates ~forwards u] places each of [templates], in the
    order given, and each of [forwards] in front of the chunk of [u] that
    first needs it, reading the chunks in the order written.

    A template goes in front of the innermost chunk holding the first
    declaration that writes it: a homed one, in each module struct whose
    members write it, in front of the innermost member holding it, any
    other in front of the innermost chunk at namespace scope, holders in
    front of aliases.  One nothing writes is declared nowhere.
    A forward declaration goes in front of the innermost chunk at namespace
    scope holding the first declaration that names its struct, unless that
    chunk defines the struct. *)
val schedule : templates:template list -> forwards:forward list -> translation_unit -> scheduled

(** The scheduled unit as a document, as {!print_tree} writes each
    section. *)
val print : write:(spelling -> unprinted -> Pp.t) -> scheduled -> Pp.t
