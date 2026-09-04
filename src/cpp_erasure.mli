(** Erasure decisions over the MiniCpp IR.

    A value that crosses into a [std::any] has to be read back out at the shape
    it was written in, and how to do that is not always knowable where the cast
    is built.  This module owns that decision, and with it the single answer to
    "is this type spelled [std::any]".

    See [docs/nanopass-plan.md]. *)

open Names
open Minicpp

(** {2 Axiom types}

    A Rocq axiom has no computational content, so its type extracts to
    [std::any].  The registry is populated by {!Cpp_ind} as declarations are
    processed. *)

(** Register a GlobRef as an axiom type. *)
val register_axiom_type : GlobRef.t -> unit

(** Whether a GlobRef has been registered as an axiom type. *)
val is_axiom_type_ref : GlobRef.t -> bool

(** {2 The boxedness oracle} *)

(** Names introduced by [using X = std::any;], accumulated in emission order. *)
val any_type_aliases : Id.Set.t ref

(** [is_any_shaped ty] — [ty] is spelled [std::any] in the generated code,
    whether directly, through a type modifier, through a [using] alias, or
    because it is an axiom type. *)
val is_any_shaped : cpp_type -> bool

(** [erased_list_shape ty] is the shape a value of list type [ty] physically
    has once it has been through a [std::any]: its elements were boxed one at a
    time, so the container holds [std::any] however concrete [ty]'s element
    type is.  Returns the list's global alongside the shape, because only a
    generated list has the converting constructor [List<A>(const List<_U>&)]
    that recovers the concrete-element container from it; a custom-extracted
    one stays flat.

    [None] for anything that is not a list, and for a list whose elements are
    erased already. *)
val erased_list_shape : cpp_type -> (Names.GlobRef.t * cpp_type) option

(** The two method-registry queries {!resolve_casts} needs to tell whether an
    initialiser hands back a box.  The registry sits above this module in the
    dependency order, so {!Cpp_print} installs them at load time. *)
type method_queries = {
  mq_returns_any : Names.GlobRef.t -> bool;
      (** is the global's result declared [std::any]? *)
  mq_is_method : Names.GlobRef.t -> bool;
      (** is the global called as a method? *)
}

val method_queries : method_queries ref

(** {2 The pass} *)

(** A declaration whose types are all spelled the way they will be written
    out: every {!Minicpp.Topaque} has been settled into {!Minicpp.Tany}.

    This is the printable phase of {!Minicpp.cpp_decl}.  {!materialise} is its
    only producer, so a declaration cannot reach {!Cpp_print.pp_cpp_decl_raw}
    without having crossed the seam -- the invariant is carried by the type
    rather than re-checked. *)
type settled = private Minicpp.cpp_decl

(** [resolve_casts decl] rewrites every {!Minicpp.CPPany_cast} in [decl] to say
    which caster the printer should emit: dropped where the cast is the
    identity, {!Minicpp.CPPany_cast_tolerant} where the shape is only knowable
    when C++ instantiates the surrounding template, and left alone otherwise.

    Call it on declarations in emission order: [using] aliases are recorded as
    they are met, mirroring where C++ would have them in scope. *)
val resolve_casts : settled -> settled

(** [materialise decl] replaces every {!Minicpp.Topaque} in [decl] with
    {!Minicpp.Tany}.

    [Topaque] means "the representation is unknown here" — it prints as
    [std::any] but licenses no box and no cast.  That is the honest answer
    while a type is still being inferred, but writing [std::any] down in a
    header is the act that decides the representation, and from then on the
    value {e is} boxed.  Running this once on the way out of translation saves
    every declaration emitter from having to remember
    {!Ml_type_util.materialise_opaque}, and is print-neutral by construction. *)
val materialise : cpp_decl -> settled
