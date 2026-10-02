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

(** {2 Forward declarations} *)

(** Take the struct forward declarations accumulated since the last call. *)
val take_forward_struct_decls : unit -> Pp.t list

(** Record a forward declaration for a struct about to be rendered at global
    scope.  A constrained template's waits in
    {!constrained_forward_struct_decls} until a chunk needs it. *)
val register_forward_struct_decl :
  env:Common.env ->
  name:Pp.t ->
  tparams:(template_type * Id.t) list ->
  cstr:cpp_constraint option ->
  unit

(** Pending forward declarations of constrained templates, by struct name. *)
val constrained_forward_struct_decls : (string * Pp.t) list ref

(** The pending constrained forward declarations [text] needs, taken out of
    the registry. *)
val take_constrained_forward_decls : string -> Pp.t list

(** Forget the constrained forward declarations no chunk asked for. *)
val reset_constrained_forward_decls : unit -> unit

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
