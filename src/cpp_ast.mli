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

(** A parameter of a template, by its name. *)
type template_param =
  | Typename of Pp.t  (** [typename T]. *)
  | Constrained of {concept : Pp.t; param : Pp.t}
      (** [C<..> M], the concept applied to any further arguments. *)

(** The name a reference is written with where the declaration holding it
    is written, once {!resolve} has resolved it there. *)
type resolution = Unresolved | Resolved of Cpp_name.t

(** A module a declaration names, by its path, and its name where the
    declaration is written. *)
type module_ref = {path : ModPath.t; name : resolution}

(** A global a declaration names, and its name where the declaration is
    written. *)
type global_ref = {global : GlobRef.t; name : resolution}

(** [module_ref path] is the module at [path], not yet resolved. *)
val module_ref : ModPath.t -> module_ref

(** [global_ref r] is the global [r], not yet resolved. *)
val global_ref : GlobRef.t -> global_ref

(** The concept of a module type a declaration names, by the module type's
    path, and its name where the declaration is written. *)
type concept_ref = {module_type : ModPath.t; name : resolution}

(** [concept_ref path] is the concept of the module type at [path], not yet
    resolved. *)
val concept_ref : ModPath.t -> concept_ref

(** How {!resolve} names what a declaration names where it is written, at
    a frame inside it. *)
type resolver = Cpp_resolution.frame -> Cpp_resolution.key -> Cpp_name.t

(** What a declaration not yet printed declares. *)
type declaration =
  | Declaration of {env : Common.env; settled : Cpp_erasure.settled}
      (** A finished declaration, printed in the name environment [env]. *)
  | Absorbed of {env : Common.env; settled : Cpp_erasure.settled}
      (** A member of the struct a declaration writes around a wrapper
          module's declarations, printed in [env].  What it needs is placed
          with that declaration, which is what was planned. *)
  | Fields of {record : GlobRef.t; vars : Id.t list; fields : (string * Minicpp.cpp_type) list}
      (** The fields of the eponymous record [record] merged into its
          module's struct, each by its name and type, the type variables
          they name named [vars]: no declaration holds them. *)
  | Modtype_concept of {
      path : ModPath.t;
      params : ModPath.t list;
      concept : Modtype_concept.t;
      names : Cpp_resolution.table;
    }
      (** The concept the module type at [path] becomes, generated as
          [concept], over the parameters [params] of a functor declaring
          it, naming what [names] names. *)
  | Global_alias of global_alias
      (** [using N = ::N;]: a member standing in for a type declared under
          the same name at namespace scope, where the file moved it, so that
          the struct still names it.  Not a declaration of the program's:
          one of the file's layout. *)
  | Assertion of assertion
      (** [static_assert(C<S>);], on a line of its own: that a module or an
          instance satisfies a concept. *)
  | Module_alias of {name : Pp.t; target : module_expr}
      (** [using name = target;]: a module defined as another, inside a
          class template a qualified name in [target] being a dependent
          one. *)
  | Functor_alias of {name : Pp.t; functor_ : module_ref; params : (template_param * module_ref) list}
      (** [template <params> using name = functor_<params>;]: a functor
          defined as another, which Rocq reduces to the other's name, over
          its own parameters, each as declared and as a module. *)
  | Derived_functor of {template : template_param list; name : Pp.t; base : module_expr}
      (** [template <template> struct name : base {};]: a functor whose body
          is another module, its own parameters visible to [base]. *)

(** A module expression a declaration writes. *)
and module_expr =
  | Module_named of module_ref  (** The module. *)
  | Applied of application

(** A functor applied to modules. *)
and application = {functor_ : module_ref; args : module_ref list}

(** That [subject] satisfies [concept], each named as written where the
    assertion is: a subject declared in a struct the assertion follows is
    qualified by it. *)
and assertion = {concept : asserted; subject : subject}

(** The concept an {!assertion} asserts. *)
and asserted =
  | Of_module_type of concept_ref  (** That of the module type. *)
  | Of_class of global_ref  (** That of the type class. *)

(** What an {!assertion} asserts it of. *)
and subject =
  | Module of module_ref  (** The struct the module is written as. *)
  | Instance of {instance : global_ref; args : Minicpp.cpp_type list}
      (** The instance, as a type, with the class's further arguments. *)

(** What a {!Global_alias} stands in for. *)
and global_alias =
  | Alias_of_type of {
      target : global_ref;
      definition : definition;
      tparams : (Minicpp.template_type * Id.t) list;
    }
      (** The type [target] declares, as [definition] declares it, over
          [tparams], which the alias repeats:
          [template <tparams> using N = ::N<tparams>;]. *)
  | Alias_of_module of module_ref
      (** The struct a module is written as. *)

(** How the type an {!Alias_of_type} stands in for is declared, which is
    the name it is declared under. *)
and definition = Cpp_resolution.definition = Enum_definition | Struct_definition | Alias_definition

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
  | Wrapper_struct of {name : string; module_ : ModPath.t; fields : t}
      (** The struct [name] a declaration writes around the declarations of
          the wrapper module [module_]: its own members, [fields], then that
          module's body, which the translation unit holds
          ({!translation_unit.wrapper_bodies}) and {!schedule} writes in.  The
          body is built apart from the declaration, which only knows, from the
          plan, that it is written into it. *)
  | Concept_group of {position : concept_position; concepts : t list}
      (** Concepts a module's struct is written beside, each on a line of
          its own, laid out as [position] says.  At least one. *)
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

(** How a struct's braces are laid out. *)
and layout =
  | Block  (** The body opens on a line of its own. *)
  | One_line  (** [struct N {};]: there is no body. *)

(** Where a {!Concept_group} is written beside its module's struct, which
    is how it is laid out: a blank line after the last concept, and in
    front of the first nothing, a line break, or a blank line. *)
and concept_position =
  | Classes_ahead  (** The module's classes' concepts, ahead of it, after a line break. *)
  | Module_types_ahead  (** Its module types' concepts, ahead of it. *)
  | After_struct  (** Concepts naming its members, after it, after a blank line. *)

val text : Pp.t -> t
val empty : t

(** [concept_group position l] is {!Concept_group}; nothing, if [l] is
    empty. *)
val concept_group : concept_position -> t list -> t

(** [template<..>] and a line break, if [params] is not empty; nothing
    otherwise. *)
val pp_template_head : template_param list -> Pp.t
val decl : needs:Needs.t -> Pp.t -> t

(** [unprinted ~needs env d] is [d], printed in [env] where the tree puts
    it. *)
val unprinted : needs:Needs.t -> Common.env -> Cpp_erasure.settled -> t

(** [absorbed env d] is {!Absorbed}, printed where the tree puts it. *)
val absorbed : Common.env -> Cpp_erasure.settled -> t

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

(** [module_alias ~name target] is {!Module_alias}, printed where the tree
    puts it.  It needs nothing placed in front of it. *)
val module_alias : name:Pp.t -> module_expr -> t

(** [functor_alias ~name functor_ params] is {!Functor_alias}, printed where
    the tree puts it.  It needs nothing placed in front of it. *)
val functor_alias : name:Pp.t -> module_ref -> (template_param * module_ref) list -> t

(** [derived_functor ~template ~name base] is {!Derived_functor}, printed
    where the tree puts it.  It needs nothing placed in front of it. *)
val derived_functor : template:template_param list -> name:Pp.t -> module_expr -> t

(** [wrapper_struct ~name ~module_ ~fields] is {!Wrapper_struct}. *)
val wrapper_struct : name:string -> module_:ModPath.t -> fields:t -> t

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

(** The names of the {!Wrapper_struct}s in [t], in the order written. *)
val wrapper_structs : t -> string list

(** [fill_wrappers bodies t] is [t] with each {!Wrapper_struct} written as
    {!module_} writes the struct around its fields and the body [bodies]
    gives under its name.
    @raise Invalid_argument if [bodies] gives none, or one of another
    module. *)
val fill_wrappers : (string * body) list -> t -> t

(** [t] as a document, for reading.
    @raise Invalid_argument if it holds a declaration not yet printed. *)
val to_pp : t -> Pp.t

(** [resolve_tree ~requested ~resolve t] is [t] with what each declaration
    not yet printed names resolved -- its modules, the concepts and the
    instance an assertion names, the type a member alias stands in for, and
    whatever else [requested] says it names, at a frame inside it -- each as
    [resolve spelling] names it where a declaration spelled [spelling] is
    written.
    @raise Invalid_argument as {!print_tree} does. *)
val resolve_tree :
  requested:(declaration -> (Cpp_resolution.frame * Cpp_resolution.key) list) ->
  resolve:(spelling -> resolver) ->
  t ->
  t

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
  wrapper_bodies : (string * body) list;
      (** The body of each wrapper module a {!Wrapper_struct} writes, by the
          struct's name. *)
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
    chunk defines the struct.  Each {!Wrapper_struct} is filled in first
    ({!fill_wrappers}). *)
val schedule : templates:template list -> forwards:forward list -> translation_unit -> scheduled

(** {!resolve_tree} over each section of a scheduled unit. *)
val resolve :
  requested:(declaration -> (Cpp_resolution.frame * Cpp_resolution.key) list) ->
  resolve:(spelling -> resolver) ->
  scheduled ->
  scheduled

(** The scheduled unit as a document, as {!print_tree} writes each
    section. *)
val print : write:(spelling -> unprinted -> Pp.t) -> scheduled -> Pp.t
