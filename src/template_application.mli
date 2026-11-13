(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The explicit template arguments a call writes, planned against the
    callee's {!Callable_abi}: each parameter of the callee's template head
    is matched to the value a use gives it by the parameter's origin.

    The one conversion from what a use means -- a value for some of the
    callee's scheme variables and class dictionaries -- to what C++ is told:
    the shortest prefix of the declaration's head that writes every value,
    each parameter found by its origin, never by a position in some other
    list.  A position before the last written one that has no value takes
    the filler the plan sanctions for it, or ends the prefix there, the rest
    left to deduction; nothing is shifted, truncated by count, or padded with
    a stand-in the plan does not name. *)

(** The template arguments a call writes. *)
type t = private
  | Deduce_all
      (** none: C++ deduces every parameter *)
  | Explicit_prefix of Cpp_ir.Lowered.Type.t list  (** the arguments for a
      prefix of the head, in order; never empty *)

(** [plan abi ~instance ~scheme] writes, at each parameter of [abi]'s head in
    order, the value its origin has: [instance k] for the [k]th dictionary,
    [scheme v] for a scheme variable, nothing for a deduced callable or a
    parameter the declaration derives.  A value is adapted to the
    parameter's kind: a template-template parameter takes a template name
    ([Type_constructor]), a type parameter a type.  A phantom parameter is always
    written, with its filler where it has no value: nothing deduces it. *)
val plan :
  Callable_abi.t ->
  instance:(int -> Cpp_ir.Lowered.Type.t option) ->
  scheme:(Scheme.Var.t -> Cpp_ir.Lowered.Type.t option) ->
  t

(** The arguments as a list, [[]] for {!Deduce_all}. *)
val to_list : t -> Cpp_ir.Lowered.Type.t list

(** The invariants a written argument list keeps: no longer than the head, each argument
    kind-correct for the parameter it stands at, no erased placeholder
    written where a type was required.  As violations. *)
val validate : Callable_abi.t -> t -> string list
