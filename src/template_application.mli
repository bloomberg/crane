(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The explicit template arguments a call writes, planned against the
    callee's {!Callable_abi} (docs/Type-Argument-Numbering-Refactor-Plan.md,
    section 3.4).

    The one conversion from what a use means -- a value for some of the
    callee's scheme variables and class dictionaries -- to what C++ is told:
    the shortest prefix of the declaration's head that writes every value,
    each parameter found by its origin, never by a position in some other
    list.  A position before the last written one that has no value takes
    the filler the plan sanctions for it, or ends the prefix there, the rest
    left to deduction; nothing is shifted, truncated by count, or padded with
    a stand-in the plan does not name. *)

type t = private
  | Deduce_all
  | Explicit_prefix of Minicpp.cpp_type list  (** never empty *)

(** [plan abi ~instance ~scheme] writes, at each parameter of [abi]'s head in
    order, the value its origin has: [instance k] for the [k]th dictionary,
    [scheme v] for a scheme variable, nothing for a deduced callable or a
    parameter the declaration derives.  A value is adapted to the
    parameter's kind: a template-template parameter takes a template name
    ([Ttyctor]), a type parameter a type.  A phantom parameter is always
    written, with its filler where it has no value: nothing deduces it. *)
val plan :
  Callable_abi.t ->
  instance:(int -> Minicpp.cpp_type option) ->
  scheme:(Scheme.Var.t -> Minicpp.cpp_type option) ->
  t

(** The arguments as a list, [[]] for {!Deduce_all}. *)
val to_list : t -> Minicpp.cpp_type list

(** The invariants of section 8.1: no longer than the head, each argument
    kind-correct for the parameter it stands at, no erased placeholder
    written where a type was required.  As violations. *)
val validate : Callable_abi.t -> t -> string list
