(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Pretty-printing utilities, name resolution, and renaming for extracted code.
*)

open Names
open Miniml

(** {2 Generic utility functions (string, list)} *)

(** [contains_substring haystack needle] checks if [haystack] contains [needle].
*)
val contains_substring : string -> string -> bool

(** [last lst] returns the last element of a non-empty list.
    @raise Failure if the list is empty. *)
val last : 'a list -> 'a

(** [last_two lst] returns the last two elements of a list.
    @raise Failure if the list has fewer than two elements. *)
val last_two : 'a list -> 'a * 'a

(** [extract_at_pos pos lst] extracts the element at position [pos] from [lst].
    Returns (Some element, remaining_list) or (None, original_list). *)
val extract_at_pos : int -> 'a list -> 'a option * 'a list

(** [intersperse sep lst] inserts [sep] between each element of [lst]. *)
val intersperse : 'a -> 'a list -> 'a list

(** [prepend_to_all sep lst] prepends [sep] before each element of [lst]. *)
val prepend_to_all : 'a -> 'a list -> 'a list

(** By default, in module Format, you can do horizontal placing of blocks even
    if they include newlines, as long as the number of chars in the blocks are
    less that a line length. To avoid this awkward situation, we attach a big
    virtual size to [fnl] newlines. *)

(** Forced newline. *)
val fnl : unit -> Pp.t

(** Two consecutive newlines. *)
val fnl2 : unit -> Pp.t

(** Space if true, empty otherwise. *)
val space_if : bool -> Pp.t

(** Wrap in parentheses if the boolean is true. *)
val pp_par : bool -> Pp.t -> Pp.t

(** [pp_apply] : a head part applied to arguments, possibly with parenthesis *)
val pp_apply : Pp.t -> bool -> Pp.t list -> Pp.t

val pp_apply_cpp : Pp.t -> Pp.t list -> Pp.t

(** Same as [pp_apply], but with also protection of the head by parenthesis *)
val pp_apply2 : Pp.t -> bool -> Pp.t list -> Pp.t

(** Print elements as a tuple; single elements are not parenthesized. *)
val pp_tuple_light : (bool -> 'a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as a comma-separated tuple with parens. *)
val pp_tuple : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as comma-separated list without parens. *)
val pp_list : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as comma-separated list with newlines between. *)
val pp_list_newline : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as newline-separated statements. *)
val pp_list_stmt : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as semicolon-separated array. *)
val pp_array : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print elements as a boxed tuple with line-break hints. *)
val pp_boxed_tuple : ('a -> Pp.t) -> 'a list -> Pp.t

(** Print a list of identifiers as space-separated bindings. *)
val pr_binding : Id.t list -> Pp.t

(** Find a fresh name for [id] by incrementing subscript until no collision. *)
val rename_id : Id.t -> Id.Set.t -> Id.t

(** {2 de Bruijn environments} *)

(** de Bruijn environment: names in scope and set of avoided names. *)
type env = Id.t list * Id.Set.t

(** Create a fresh de Bruijn environment with current global ids. *)
val empty_env : unit -> env

(** Replace prime characters (') with underscores. *)
val remove_prime_id : Id.t -> Id.t

(** Rename a list of variables to fresh lowercase names. *)
val rename_vars : Id.Set.t -> Id.t list -> env

(** Rename type variables to fresh lowercase names. *)
val rename_tvars : Id.Set.t -> Id.t list -> Id.t list

(** Push new variable names into the de Bruijn environment. *)
val push_vars : Id.t list -> env -> Id.t list * env

(** Like {!push_vars} but for typed variable pairs. *)
val push_vars' : (Id.t * ml_type) list -> env -> (Id.t * ml_type) list * env

(** Look up a de Bruijn index in the environment. *)
val get_db_name : int -> env -> Id.t

(** {2 Extraction phases and renaming} *)

type phase =
  | Pre
  | Impl
  | Intf  (** Extraction phase: pre-scan, implementation, or interface. *)

(** Set the current extraction phase. *)
val set_phase : phase -> unit

(** Get the current extraction phase. *)
val get_phase : unit -> phase

(** Compute which libraries should be opened initially. *)
val opened_libraries : unit -> ModPath.t list

type kind =
  | Term
  | Type
  | Cons
  | Mod  (** Kind of global identifier: term, type, constructor, or module. *)

(** Print a reference using a specific kernel name key. *)
val pp_global_with_key : kind -> KerName.t -> GlobRef.t -> string

(** Print a reference using its canonical kernel name. Has side effects on the
    renaming tables. *)
val pp_global : kind -> GlobRef.t -> string

(** Print just the short name of a reference (for declarations). *)
val pp_global_name : kind -> GlobRef.t -> string

(** Print the type name for an eponymous record reference.  Returns the
    enclosing module name for consistent struct/type naming. *)
val pp_type_name_capitalized : GlobRef.t -> string

(** Print a module path. *)
val pp_module : ModPath.t -> string

(** Get the module path of the innermost visible layer. *)
val top_visible_mp : unit -> ModPath.t

(** Push a module onto the visibility stack. The [module_path list] corresponds
    to module parameters, the innermost one coming first in the list. *)
val push_visible : ModPath.t -> ModPath.t list -> unit

(** Pop the innermost visible layer. *)
val pop_visible : unit -> unit

(** Get the duplicate wrapper name for a (module path, label) pair, if any. *)
val get_duplicate : ModPath.t -> Label.t -> string option

type reset_kind =
  | AllButExternal
  | Everything
      (** What to reset: all renaming tables, or also external file content. *)

(** Reset all renaming tables. *)
val reset_renaming_tables : reset_kind -> unit

(** Set the set of reserved keywords for the target language. *)
val set_keywords : Id.Set.t -> unit

(** Get the set of reserved keywords for the target language. *)
val get_keywords : unit -> Id.Set.t

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then the constants are
    directly turned into chars *)

val is_native_char : ml_ast -> bool

val get_native_char : ml_ast -> char

val pp_native_char : ml_ast -> Pp.t

(** Special hack for constants of type String.string : if an
    [Extract Inductive string => string] has been declared, then the constants
    are directly turned into string literals *)

val is_native_string : ml_ast -> bool

val get_native_string : ml_ast -> string

val pp_native_string : ml_ast -> Pp.t

(** Registered name for the sig type (used for existential type extraction). *)
val sig_type_name : string

(** {2 Synthetic name generators}

    Centralized naming conventions for generated C++ identifiers. Each function
    takes an integer index and returns a string or [Id.t]. *)

val tvar_name : int -> string

val tvar_id : int -> Id.t

val anon_tvar_name : int -> string

val anon_tvar_id : int -> Id.t

val fun_tparam_name : int -> string

val fun_tparam_id : int -> Id.t

val field_param_name : int -> string

val field_param_id : int -> Id.t

(** {2 Constructor Field Name Registry}

    See {!Common.ctor_field_names} for design rationale. *)

(** Register a named field for a constructor struct. *)
val register_ctor_field_name : string -> int -> Id.t -> unit

(** Look up the field name; falls back to [d_a{idx}] if unregistered. *)
val lookup_ctor_field_name : string -> int -> Id.t

(** Clear the registry between extraction passes. *)
val reset_ctor_field_names : unit -> unit

val eta_param_name : int -> string

val eta_param_id : int -> Id.t

val tc_instance_name : int -> string

val tc_instance_id : int -> Id.t

val ctor_fallback_name : int -> string

val ctor_fallback_id : int -> Id.t

val db_fallback_name : int -> string

val db_fallback_id : int -> Id.t

val tparam_name : Id.t -> Id.t

val enum_ctor_name : string -> string

val capitalize_last_component : string -> string
