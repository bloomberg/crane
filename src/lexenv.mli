(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The lexical environment of a Core body: every binder in scope, innermost
    first, so that de Bruijn index [i] names the [i]th entry.

    A binder's type is not on the [MLrel] that names it; it is written down
    where the binder is bound.  A pass that reads an argument's type through
    a variable therefore needs the environment the argument is typed in, and
    takes it as this value rather than reading whichever scope a traversal
    happens to be in. *)

(** What a binder stands for.  A declaration's parameter at a class type is
    its [Dictionary]: the instance, which C++ takes as a template argument
    rather than a value.  Every other binder, a class-typed one bound inside a
    body included, is a [Value]. *)
type role =
  | Value
  | Dictionary

type binder = {
  eb_id : Names.Id.t;
  eb_type : Miniml.ml_type;
  eb_role : role;
}

type t = private binder list

val empty : t

(** [push bs env] binds [bs], innermost first, inside [env]. *)
val push : binder list -> t -> t

(** The binder at de Bruijn index [i] (1-based), or [None] when [i] is out of
    range or non-positive. *)
val binder : t -> int -> binder option

(** The ML type of the binder at index [i], as {!binder}. *)
val type_opt : t -> int -> Miniml.ml_type option

(** The number of binders in scope. *)
val depth : t -> int
