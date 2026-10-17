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

(** [pp_cpp_decl env decl] renders a settled declaration. *)
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

(** {2 Forward declarations} *)

(** A forward declaration of a struct or scoped enum defined at namespace
    scope: the name it declares, its text, and whether it is a constrained
    template -- one whose [requires] clause or concept-kinded parameter names
    a concept, which the header's prologue need not have declared. *)
type forward_declaration = {
  fwd_struct : string;
  fwd_text : Pp.t;
  fwd_constrained : bool;
}

(** [forward_declarations env d] is the forward declaration of each struct
    and scoped enum [d] defines at namespace scope, in the order it defines
    them, printed in the current scope as the definition prints its head. *)
val forward_declarations : Common.env -> Cpp_erasure.settled -> forward_declaration list

(** The using-declarations this rendering pass needs for promoted type
    variables whose file-scope alias another file declares, emptying the set. *)
val take_promoted_alias_imports : unit -> string list

(** {2 Synthesised aliases} *)

(** Take the alias templates minted since the last call, as declarations;
    [select] keeps only the names it accepts. *)
val take_ctor_alias_decls :
  ?select:(string -> bool) -> is_header:bool -> unit -> Pp.t list

(** The synthesised names minted but not yet declared. *)
val pending_ctor_alias_names : unit -> string list

(** [record_ctor_alias_home name body] notes the module struct [name] must be
    declared in, when [body] names one of its globals. *)
val record_ctor_alias_home : string -> cpp_type -> unit

(** The pending synthesised names whose home is [mp]. *)
val pending_ctor_aliases_homed_in : ModPath.t -> string list

(** Forget which aliases were emitted, for a new file. *)
val reset_ctor_alias_emitted : unit -> unit

(** Whether [text] spells [name] as a whole identifier. *)
val mentions_name : string -> string -> bool

(** Whether an expression is a lambda that captures nothing, or one such
    invoked at once with no argument: the same value wherever it is evaluated
    (see {!Cpp_constants}). *)
val closed_lambda : Minicpp.cpp_expr -> bool
