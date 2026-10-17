(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Rendering MiniCpp as C++ source text.

    The declaration printer's input is a settled declaration (see
    {!Cpp_erasure.settled}): it runs no compiler pass.  The registries below
    are the printer's remaining state: forward declarations and synthesised
    aliases it mints while rendering and the assembly drains. *)

open Names
open Minicpp

(** {2 Rendering} *)

(** [pp_cpp_decl env decl] renders a settled declaration, its text carrying
    the synthesised templates the declaration writes
    ({!ctor_aliases_carried}). *)
val pp_cpp_decl : Common.env -> Cpp_erasure.settled -> Pp.t

(** How a member is written: in the struct with or without its body, or out
    of line. *)
type member_mode

(** [pp_cpp_field env f] renders a struct member.  [struct_name] is the
    enclosing struct's name, for constructors and destructors. *)
val pp_cpp_field :
  ?struct_name:Pp.t -> ?mode:member_mode -> Common.env -> cpp_field -> Pp.t

(** [pp_cpp_type par vl t] renders a type; [par] asks for parentheses where
    precedence needs them, [vl] names the type variables by index.  [~lead:false]
    drops the leading [typename] of a dependent name about to be embedded in a
    longer one. *)
val pp_cpp_type : ?lead:bool -> bool -> Id.t list -> cpp_type -> Pp.t

(** Whether one thing a rendering writes ({!Cpp_name.written}) is a
    qualifier naming into a struct or a template parameter rather than a
    namespace: a tagged scope by its kind, untagged text by the identifier in
    front of each [::], which passes only as an included library's
    namespace. *)
val writes_into_a_struct : Cpp_name.written -> bool

(** Whether a declaration, written as a member of a struct body, is a static
    function declaration ending at its semicolon. *)
val is_static_member_declaration : cpp_decl -> bool

(** Whether a function declaration writes a qualifier into a struct or a
    template parameter, in its name, result or parameters, asked of the
    declaration rather than of its rendering: each name is the one
    {!pp_cpp_type} writes, from the same heads, in the render context the
    caller has set.  [None] for anything but a function declaration, and
    where only the rendering can tell -- an expression's type, a type
    constructor named as a template argument. *)
val declaration_names_into_a_struct : cpp_decl -> bool option

(** Doc-comment lines for [name], or nothing when none is registered. *)
val pp_doc_comment_for_name : ?indent:string -> string -> Pp.t

(** The break between two declaration groups; see the vertical box in
    [Extract_env]. *)
val cut2 : unit -> Pp.t

(** {2 Custom type templates} *)


(** [render_type_template ~hole text] fills hole [i] with [hole i], writing an
    unfillable hole back out as a placeholder. *)
val render_type_template : hole:(int -> Pp.t option) -> string -> Pp.t

(** {2 Wrapper structs} *)

(** The name the struct wrapping an inductive at namespace scope is written
    under. *)
val nspace_wrapper_name : GlobRef.t -> string

(** Whether the inductive is written inside a wrapper other declarations were
    queued against, and so is spelled [List::list] rather than [List]. *)
val nested_in_wrapper : GlobRef.t -> bool

(** The names of the wrapper structs a declaration writes around something
    other than a sole struct merged into them, in the order it writes them:
    the structs another wrapper's declarations can be written into. *)
val unmerged_wrappers_written : Cpp_erasure.settled -> string list

(** [writing_wrapper_members members f] runs [f], writing an element whose
    wrapper structs of the names [members] gives hold, after their own
    members, the declarations it gives with them: those of the wrapper
    modules of those names. *)
val writing_wrapper_members : (string * Pp.t) list -> (unit -> 'a) -> 'a

(** Take the names of the wrapper structs that took a wrapper module's
    declarations since the last call, under [CRANE_CHECK_IR]. *)
val take_absorbed_wrappers : unit -> string list

(** The assertions a declaration holds back, in the order it writes them:
    those that a class's concept holds of an instance where the concept is
    declared after the struct being written.  Each is the concept held back,
    its name, and what it is asserted of. *)
val held_back_assertions : Cpp_erasure.settled -> (Cpp_state.held_concept * Pp.t * Pp.t) list

(** {2 Forward declarations} *)

(** A forward declaration of a struct or scoped enum defined at namespace
    scope: the name it declares, its text, and whether it is a constrained
    template -- one whose [requires] clause or concept-kinded parameter names
    a concept, which the header's prologue need not have declared. *)
type forward_declaration = {
  fwd_ref : GlobRef.t;  (** The struct or enum it declares. *)
  fwd_struct : string;
  fwd_text : Pp.t;
  fwd_constrained : bool;
}

(** [forward_declarations env d] is the forward declaration of each struct
    and scoped enum [d] defines at namespace scope, in the order it defines
    them, printed in the current scope as the definition prints its head. *)
val forward_declarations : Common.env -> Cpp_erasure.settled -> forward_declaration list

(** The using-declaration a unit needs for a promoted type variable whose
    file-scope alias another file declares, under separate extraction. *)
val promoted_alias_import : Names.Id.t -> string option

(** {2 Synthesised aliases} *)

(** A template synthesised to stand where a type constructor is written as a
    template template argument but has no template name of its own: an alias
    template, or a holder -- a struct over the enclosing declaration's
    parameters the body names, with the alias as its member [c]. *)
type ctor_alias = private {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : bool;
  ca_home : ModPath.t option;
      (** The module struct it is declared in, or [None] for namespace
          scope. *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared. *)
}

(** The synthesised templates the finished declaration written in [file]
    writes, in the order written, in the scope being written. *)
val ctor_aliases_written : file:Common.file -> Cpp_erasure.settled -> ctor_alias list

(** The synthesised templates the type [t] writes in [file], its type
    variables read as [vl]. *)
val ctor_aliases_of_type : file:Common.file -> vl:Id.t list -> cpp_type -> ctor_alias list

(** [plan_ctor_aliases written] plans the templates each file writes,
    [written file] being those of [file], read off what it writes
    ({!ctor_aliases_written}): the header's, then the implementation's. *)
val plan_ctor_aliases : (Common.file -> ctor_alias list) -> unit

(** The name of a template, as planned. *)
val ctor_alias_name : ctor_alias -> string

(** The declaration of a template. *)
val ctor_alias_declaration : ctor_alias -> Pp.t

(** The templates the file [file] declares, each once, in the order
    planned: the aliases it writes, and, in the header, every holder the
    unit writes. *)
val ctor_aliases_declared_in : file:Common.file -> ctor_alias list

(** Under [CRANE_CHECK_IR], start recording the templates the file about
    to be written spells. *)
val start_ctor_alias_census : unit -> unit

(** Under [CRANE_CHECK_IR], check what the file [file] spelled against the
    plan. *)
val check_ctor_alias_plan : file:Common.file -> unit

(** The names of the synthesised templates the declarations whose text
    [doc] holds write, in the order first carried ({!pp_cpp_decl}). *)
val ctor_aliases_carried : Pp.t -> string list

(** The structs the file being written has constrained forward declarations
    of, each by its reference and the name its declaration declares; a
    declaration's text carries those it names or defines. *)
val constrained_structs : (GlobRef.t * string) list ref

(** The names, of the {!constrained_structs}, that the declarations whose
    text [doc] holds name or define. *)
val structs_named : Pp.t -> string list

(** The names, of the {!constrained_structs}, that the declarations whose
    text [doc] holds define. *)
val structs_defined_in : Pp.t -> string list

(** The type names the file being written introduces at file scope, as
    planned: a definition written out of line leaves them unqualified. *)
val file_scope_type_names : CString.Set.t ref

(** The type names a declaration written at namespace scope introduces
    there, as they are written. *)
val file_scope_types : Cpp_erasure.settled -> string list

(** Under [CRANE_CHECK_IR], start recording the type names the file about
    to be written introduces at file scope. *)
val start_file_scope_census : unit -> unit

(** Under [CRANE_CHECK_IR], check those against {!file_scope_type_names}. *)
val check_file_scope_types : file:Common.file -> unit

(** Whether an expression is a lambda that captures nothing, or one such
    invoked at once with no argument: the same value wherever it is evaluated
    (see {!Cpp_constants}). *)
val closed_lambda : Minicpp.cpp_expr -> bool
