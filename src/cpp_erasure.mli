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

(** [empty_box] is the value an erased argument is passed as: [std::any{}].

    An argument extraction erased still occupies the slot of a parameter
    declared at the erased type, and that slot is evaluated, so it cannot hold
    the [CPPabort] a genuinely unreachable erased position gets. *)
val empty_box : cpp_expr

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

(** A settled declaration taken apart one level.  The seam is hereditary --
    {!materialise} rewrites a declaration together with everything nested
    inside it -- so the children a view hands out are settled too, and they are
    the only settled values it hands out: there is no way to call an unrelated
    declaration settled. *)
type view =
  | Template of
      (Minicpp.template_type * Names.Id.t) list
      * Minicpp.cpp_constraint option
      * settled
  | Namespace of Names.GlobRef.t option * settled list
  | Decl of Minicpp.cpp_decl  (** Any other declaration: none nested inside. *)

val view : settled -> view

(** {!Minicpp.split_definition} of a settled definition.  Dropping a body
    removes types and adds none, so both halves are settled. *)
val split_definition : settled -> (settled * settled) option

(** {!Minicpp.strip_template_defaults} of a settled declaration. *)
val strip_template_defaults : settled -> settled

(** [resolve_casts decl] rewrites every {!Minicpp.CPPany_cast} in [decl] to say
    which caster the printer should emit: dropped where the cast is the
    identity, {!Minicpp.CPPany_cast_tolerant} where the shape is only knowable
    when C++ instantiates the surrounding template, and left alone otherwise.

    Call it on declarations in emission order: [using] aliases are recorded as
    they are met, mirroring where C++ would have them in scope. *)
val resolve_casts : settled -> settled

(** [bind_free_tvars decl] spells [std::any] every type variable a body names
    that nothing in scope declares -- the head's own parameters, the enclosing
    struct's and namespace's, the signature's, and any lambda's along the way.
    Only bodies are rewritten; a signature short of a parameter is the same
    defect but wants the opposite repair. *)
val bind_free_tvars : settled -> settled

(** [lower_boxed_reads decl] makes every read of a boxed value that the
    context needs at a concrete type an explicit {!Minicpp.CPPunbox}: at a
    custom template's arguments and scrutinee, and at each use of a custom
    pair match's branch parameter when the pair was boxed.  Which binders hold
    boxes is read off their declared types. *)
val lower_boxed_reads : settled -> settled

(** [supply_template_args decl] gives every inline mapping applied in
    [decl] -- a mapped type or global, a block template, a custom match --
    each type argument its template names.  Translation supplies those the
    application writes; where erasure dropped them, the ones it does not
    supply are erased, and are written down here as {!Minicpp.Tany} rather
    than left for the printer to assume.  A type constructor named unapplied
    ({!Minicpp.Ttyctor}) is not an application, and is left alone. *)
val supply_template_args : settled -> settled

(** [lower_method_calls decl] writes each call of a function the method
    registry made a member of its receiver's struct as the
    {!Minicpp.CPPmethod_call} it is: the receiver taken out of the argument
    list, reached with [.] or [->], and the template arguments the struct
    carries left off.  Every other reference to such a function names it as
    a value, and becomes the {!Minicpp.CPPmethod_value} lambda calling it on
    its receiver.  The last pass, so every pass before it sees the call as
    translation built it. *)
val lower_method_calls : settled -> settled

(** [lower_projections decl] writes each record projection the same way:
    applied to its record, as the {!Minicpp.CPPprojection} reading its field;
    named as a value, as the {!Minicpp.CPPprojection_value} lambda reading it
    from its argument.  After {!lower_method_calls}, so a projection made a
    method of its record is called as one. *)
val lower_projections : settled -> settled

(** [lower_conditionals decl] writes a lambda invoked at once that only
    chooses between two values -- a match of one alternative against the
    rest, an [if], or a mapped two-way case whose template is an [if] -- as
    the {!Minicpp.CPPcond} it computes.  A choice with a string literal in a
    branch keeps its lambda, whose return type converts the literal. *)
val lower_conditionals : settled -> settled

(** [lower_access_moves decl] moves what a member read reads rather than
    the object it reads it from: [std::move(x).f] is [std::move(x.f)],
    through [.] and [->] alike, and a member function is called on the
    object itself, so a move of its receiver goes.  Last, after every pass
    that writes a move or a member read. *)
val lower_access_moves : settled -> settled

(** [is_literal_type ty] holds when [ty] is a C++ literal type, so a value of
    it can be a constant expression: not an allocation ([shared_ptr]), not
    [void], not a type known only at instantiation, not an axiom's type
    (whose stubs throw), not [std::function] or [decltype], and no type it is
    made of fails to be one. *)
val is_literal_type : Minicpp.cpp_type -> bool

(** [decide_constexpr decl] decides, for every function, method and variable
    [decl] defines, whether it may be [constexpr]
    ({!Minicpp.constexpr_eligibility}).  Last, once every type is final. *)
val decide_constexpr : settled -> settled

(** [materialise decl] replaces every {!Minicpp.Topaque} in [decl] with
    {!Minicpp.Tany}.

    [Topaque] means "the representation is unknown here" — it prints as
    [std::any] but licenses no box and no cast.  That is the honest answer
    while a type is still being inferred, but writing [std::any] down in a
    header is the act that decides the representation, and from then on the
    value {e is} boxed.  Running this once on the way out of translation saves
    every declaration emitter from having to remember
    {!Ml_type_util.materialise_opaque}, and is print-neutral by construction.

    So is the type of a variable a branch of a custom match binds, where it
    has no C++ spelling ({!Ml_type_util.has_no_cpp_spelling}): a type from a
    module [Crane Extract Skip Module] left out has no declaration to name,
    and the honest answer is that the type is not known, which [std::any]
    says.  A template reading the binder's type can then treat the two cases
    alike.  A [Crane Extract Skip] behind it is warned about. *)
val materialise : cpp_decl -> settled

(** Whether a custom match in [decl] writes down a binder's type that C++
    cannot spell, which {!materialise} would have made [std::any]. *)
val writes_unspellable_binder : settled -> bool
