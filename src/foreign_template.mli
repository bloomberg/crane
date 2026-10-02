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

(** [with_result name s] is [s] with every [%result] spelled [name]. *)
val with_result : string -> string -> string

(** A mapping that names a template without saying where its arguments go
    takes them in order: ["Sum1"] at two arguments is ["Sum1<%t0, %t1>"]. *)
val custom_template_with_args : string -> int -> string
