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

(** {2 Building and reading boxes}

    Three ways of writing a box down are always mistakes.  These are the only
    constructors of {!Minicpp.CPPbox} and {!Minicpp.CPPany_cast}, and each is
    the identity on the term that would have been wrong, so none of the three
    arises. *)

(** [converting_ctor ty args] is the converting constructor [ty(args)].  When
    [ty] is erased and there is one argument, that is a box.

    A box built around a box is two sites each believing they owned the
    boundary; the inner value is then unreachable, because the consumer casts
    once.  So boxing a box re-boxes what was inside it instead. *)
val converting_ctor : cpp_type -> cpp_expr list -> cpp_expr

(** [unbox ty e] reads [e] back out of its box at type [ty].

    Two readings are no reading at all, and neither is built.  [any_cast] to
    an erased type does not unwrap the box -- it asks whether the box holds a
    {e further} box, and throws when it does not -- so an erased [ty] gives
    [e] itself.  A cast applied straight to a freshly built box is dead work,
    so it gives back what was boxed. *)
val unbox : cpp_type -> cpp_expr -> cpp_expr

(** [unbox_tolerant ty e] is {!unbox} through the [crane_any_cast] runtime
    helper, which recovers a value component by component and passes through
    anything that was never boxed.  For a shape that is only knowable once C++
    instantiates the surrounding template. *)
val unbox_tolerant : cpp_type -> cpp_expr -> cpp_expr

(** {2 The pass} *)

(** A declaration whose types are all spelled the way they will be written
    out: every {!Minicpp.Topaque} has been settled into {!Minicpp.Tany}.

    This is the printable phase of {!Minicpp.cpp_decl}.  {!materialise} is its
    only producer, so a declaration cannot reach {!Cpp_print.pp_cpp_decl_raw}
    without having crossed the seam -- the invariant is carried by the type
    rather than re-checked. *)
type settled = private Minicpp.cpp_decl

(** [settled_child ~parent d] is the sub-declaration [d] of [parent], at
    [parent]'s phase.  The seam is hereditary -- {!materialise} rewrites a
    declaration together with everything nested inside it -- so descending
    into a settled declaration does not cross it again.  Holding [parent] is
    the evidence for that, which is why it is an argument. *)
val settled_child : parent:settled -> Minicpp.cpp_decl -> settled

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
