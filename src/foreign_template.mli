(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The placeholder syntax of custom mappings, parsed into tokens, once per
    text and category.  Literal C++ between placeholders stays opaque. *)

(** One token of a parsed mapping. *)
type custom_case =
  | CCscrut  (** [%scrut]: the scrutinee of a match template *)
  | CCty  (** [%ty]: the matched type *)
  | CCbody of int  (** [%br{i}]: branch [i]'s statements *)
  | CCty_arg of int  (** [%t{i}]: type argument [i] *)
  | CCelem of int  (** [%elem{i}]: type argument [i], boxed where it recurses *)
  | CCbr_var of int * int  (** [%b{i}a{j}]: branch [i]'s binder [j] *)
  | CCbr_var_ty of int * int  (** [%b{i}t{j}]: the type of that binder *)
  | CCstring of string  (** literal text *)
  | CCarg of int  (** [%a{i}]: value argument [i] *)

(** The tokens of a type template: [%t{i}] and [%elem{i}] holes. *)
val type_template : string -> custom_case list

(** The tokens of a term template: a type template's holes and [%a{i}]. *)
val term_template : string -> custom_case list

(** The tokens of an inductive's match template. *)
val match_template : string -> custom_case list

(** One token of a [Drain "..."] template: literal statements, or a
    [%yield(e)] with its argument text. *)
type drain_token = Drain_text of string | Drain_yield of string

(** The tokens of a container's [Drain "..."] template. *)
val drain_template : string -> drain_token list

(** [Some i] when a term template is its value argument [i] and nothing
    else ([%a0]): the mapped term is that argument, in whatever position the
    term itself stands. *)
val passes_through : string -> int option

(** Whether a term template is a pair projection: [%a0.first] or
    [%a0.second]. *)
val is_pair_projection : string -> bool

(** The member of a pair the template [s] projects its one argument onto
    ([first] for ["%a0.first"]), when it is a pair projection. *)
val pair_projection_field : string -> string option

(** How many times the template [s] splices its [i]-th value argument.  An
    argument past the last one it splices is applied to what it expands to,
    as a call's argument, and so is evaluated once -- every argument of a
    template that splices none, which is a callee. *)
val arg_mentions : string -> int -> int

(** Whether the template [s] splices each of its value arguments at most
    once, so that the C++ it expands to evaluates each exactly once. *)
val mentions_each_arg_once : string -> bool

(** [with_result name s] is [s] with every [%result] spelled [name]. *)
val with_result : string -> string -> string

(** A mapping that names a template without saying where its arguments go
    takes them in order: ["Sum1"] at two arguments is ["Sum1<%t0, %t1>"]. *)
val custom_template_with_args : string -> int -> string
