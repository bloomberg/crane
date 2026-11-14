(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global calls elaborated from Core, ahead of translation
    (docs/Pipeline-Disentangling-Plan.md, section 4.7): each global
    application of a unit's frozen program, with the role each of its
    arguments has, elaborated in a lexical environment of the walk's own.

    Transitional.  The roles are installed for the unit, by the occurrence of
    the use naming the callee ({!Miniml.Occurrence}), which the annotation
    rewrites a body goes through before it is translated keep, and emission
    takes a call's roles from there when it translates that application; a
    call translation built itself -- a global a let-bound alias names,
    applied where the alias is -- is elaborated where it is translated, in
    the traversal's environment.  Under [CRANE_CHECK_IR] every elaboration
    taken from here is checked against that one.  The same holds of each
    call's instantiation ({!instantiation}), planned where the walk meets the
    call at the ML types the walk gives its position. *)

(** [elaborate_arguments ~lex use args] -- the call [use args] as Core
    elaborates it from the call alone: which arguments are dictionaries,
    regular, or past the callee's arity and so applied to its result.  A
    variable argument is read off the binder it names in [lex].  The holes
    the call's context states are not resolved here. *)
val elaborate_arguments : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** [instantiate ~lex ~expected_ml ~stated_ml ~caller ~scope call] -- the
    semantic half of planning [call] (section 3.4's [ElaboratedCall]): the
    holes of its reading that its context states resolved -- an event family
    the ML type its position expects ([expected_ml]) or states
    ([stated_ml]) for its result names, a type-level function a dictionary
    argument's type names -- then, for a partial application in a
    declaration other than [caller], the variables the lambda it is
    eta-expanded into would misread erased, and the callee's types
    instantiated at that reading.  [scope] is the type variables the
    position is generated under, by name: a variable of the callee's is
    misread where it is spelled like one of them.

    Everything it reads is Core: the call, the ML types [lex] binds, the
    callee's declared type, [caller]'s -- whose constraints name a
    dictionary binder's class where its recorded type lost it -- and its
    position's ML types; no C++ type is decided or read, and nothing of the
    traversal that asks. *)
val instantiate :
  lex:Lexenv.t ->
  expected_ml:Miniml.ml_type option ->
  stated_ml:Miniml.ml_type option ->
  caller:Names.GlobRef.t option ->
  scope:Names.Id.t list ->
  Elaborated_call.t ->
  Elaborated_call.instantiated

(** A unit's elaborated calls. *)
type t

(** [structure ~methods s] elaborates every global application in [s]'s
    declarations, in each body as it is generated -- a function generated as
    a method of its inductive ([methods kn ind] gives each, with the
    inductive's variables) in its body renumbered as the method's
    ({!Method_registry.renumbering}), an instance's methods as
    {!Instance_methods} elaborates them, not its record as written -- and in
    the terms custom types are applied to in the types they write, a match
    branch's result type and the declared type of every global they call
    included; and every global named there unapplied, as its call with no
    arguments.  Each application is so elaborated where it is generated, at
    the variables it is generated under, and instantiated ({!instantiate})
    at the ML types its position expects and states as translation threads
    them: a regular argument at its parameter's type (its call's, where that
    has an erasure in it), an argument past the arity or of a local callee
    at its call's, a lambda's body past the lambda's arrows, a let-bound
    value at the binder's annotation, a bound lambda and every other
    recursion translation makes without a position at none. *)
val structure :
  methods:(Names.MutInd.t -> Miniml.ml_ind -> (Names.Id.t list * Method_registry.method_candidate) list) ->
  Miniml.ml_structure ->
  t

(** [declaration_scope ty body] is the lexical environment a definition of
    type [ty] generates its body [body] in, its parameters bound at the
    types the body is generated with, and the body under them.  In a
    normalized program ({!Core_phase.normalize}) that body is the one generated:
    eta-expanded, its let-bound lambdas as {!generated_definition} puts
    them. *)
val declaration_scope : Miniml.ml_type -> Miniml.ml_ast -> Lexenv.t * Miniml.ml_ast

(** [generated_definition ty body] is the definition [body] of type [ty],
    eta-expanded ({!Normalize.eta_expand}), with every let-bound lambda in
    it as it is generated ({!Core_query.let_lambda}): an alias of a
    polymorphic function put in place of its uses, one used at a single
    instance bound at it, and one bound as a value given a binder for each
    value arrow of its type ({!Core_query.eta_bound_lambda}).  An
    inlined alias binds nothing, so a binder after one is a level shallower
    than in the body as written. *)
val generated_definition : Miniml.ml_type -> Miniml.ml_ast -> Miniml.ml_ast

(** Every global the declarations walked name, applied or not, in their
    bodies or in a term a custom type is applied to in any type the unit
    writes, specifications' and the declared types of the globals they
    call included. *)
val referenced : t -> Names.GlobRef.t list

(** [roles t use n] -- the roles of the arguments of the application, with
    [n] arguments, that names its callee by [use], as [t] elaborated it; none
    for an application [t] did not walk. *)
val roles : t -> Miniml.global_use -> int -> Elaborated_call.role list option

(** Make [t] the unit's elaborations, the ones {!elaboration} reads.  They
    are installed before the unit's callables are planned, so planning reads
    them too; until then every answer below is decided where it is asked. *)
val install : t -> unit

(** [elaboration ~lex use args] -- the elaboration of the call [use args]
    while emitting: its arguments in the roles the installed elaborations
    have for the application naming its callee by [use], or, where they have
    none, as elaborated here in [lex] -- which under [CRANE_CHECK_IR] is a
    violation: every call emission translates was elaborated from Core.
    Planning takes the installed roles alike, and elaborates a call they
    have none for itself, which is no violation there. *)
val elaboration : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** [instantiation ~lex ~expected_ml ~stated_ml ~caller ~scope use args]
    -- the semantic half of the call [use args] while emitting: the
    instantiation the installed elaborations planned for the application
    naming its callee by [use], at the position the walk gave it, taken at
    the argument nodes being translated ({!Elaborated_call.at_call}); or,
    where they planned none or disagree, {!instantiate} of its
    {!elaboration} here, with the ML types the traversal says its position
    expects and states -- which under [CRANE_CHECK_IR] is a violation, bar a
    call translation extended itself.  Under [CRANE_CHECK_IR] a planned one
    is checked against that one.  Planning takes a planned instantiation
    alike, and instantiates a call it has none for itself, which is no
    violation there. *)
val instantiation :
  lex:Lexenv.t ->
  expected_ml:Miniml.ml_type option ->
  stated_ml:Miniml.ml_type option ->
  caller:Names.GlobRef.t option ->
  scope:Names.Id.t list ->
  Miniml.global_use ->
  Miniml.ml_ast list ->
  Elaborated_call.instantiated

(** [planned_instantiation use args] -- the instantiation the installed walk
    planned for the call [use args], at its argument nodes, where it planned
    one with the roles it gave the call; none otherwise.  Unlike
    {!instantiation} it neither counts nor checks the lookup: it is for a
    planner reading the walk, not for lowering. *)
val planned_instantiation : Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.instantiated option

(** [closed_instance_call ~lex use args] -- whether the call [use args]
    builds a typeclass instance from nothing but instance parameters, so
    that it is the same value every time it is evaluated: as the walk
    decided it where it met the application naming its callee by [use],
    from the call and the binders of its own environment.  Where the walk
    made no single decision there, or is not installed yet, it is decided
    from the call and [lex]; under [CRANE_CHECK_IR] a planned decision is
    checked against that one. *)
val closed_instance_call : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> bool

(** [static_projection_call ~lex use args] -- where the call [use args]
    calls a class field as a static member of the instance it projects
    through: which argument that instance is, the member's value
    parameters, and the operands the call leaves out
    ({!Core_query.static_projection}), as the walk decided it where
    it met the application, from the call and the binders of its own
    environment.  Where the walk made no single decision there, or is not
    installed yet, it is decided from the call and [lex]; under
    [CRANE_CHECK_IR] a planned decision is checked against that one. *)
val static_projection_call :
  lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.static_projection option

(** [closed_head_call ~lex use args] -- whether the call [use args] applies
    arguments past its callee's arity to a head, the callee applied to the
    rest, that names no value but instance parameters: a function built from
    nothing the call can change, the same every time the call is evaluated.
    As the walk decided it where it met the application, from the call and
    the binders of its own environment; where the walk made no single
    decision there, or is not installed yet, decided from the call and
    [lex]; under [CRANE_CHECK_IR] a planned decision is checked against that
    one. *)
val closed_head_call : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> bool

(** [member_template_call ~lex use args] -- whether the call [use args]
    projects a class field through its one dictionary argument, an instance
    Crane kept ({!Core_query.kept_instance_of_projection}), whose class
    declares the field as a member template, so the instance's own method can
    stand for the field's dispatcher.  Decided, and checked, as
    {!closed_head_call} is. *)
val member_template_call : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> bool

(** [singleton_dictionary_call ~live occ] -- the class and its one method
    where the variable read at the occurrence [occ], at the head of an
    application, is a singleton class's dictionary: as the walk decided it
    for that occurrence, from the binder its environment has for it.  Until
    the walk is installed it is [live ()], translation's own reading; under
    [CRANE_CHECK_IR] a planned decision is checked against that one. *)
val singleton_dictionary_call :
  live:(unit -> (Names.GlobRef.t * Names.GlobRef.t) option) ->
  Miniml.Occurrence.t ->
  (Names.GlobRef.t * Names.GlobRef.t) option

(** [shared_constant e] -- whether the construction [e] is a closed
    constructor term of a shared variant with fields, built from
    constructors, literals and erased arguments only, so the same value
    every time it is evaluated: as the walk decided it for the
    construction's occurrence.  Where the walk made no single decision
    there, or is not installed yet, decided from [e]; under [CRANE_CHECK_IR]
    a planned decision is checked against that one.  [false] of anything
    but a construction. *)
val shared_constant : Miniml.ml_ast -> bool

(** [match_kind ty branches occ] -- how the match annotated [ty] with
    [branches] at the occurrence [occ] is lowered ({!Match_kind.classify}):
    as the walk decided it for that occurrence.  Where the walk made no
    single decision there, or is not installed yet, decided from [ty] and
    [branches]; under [CRANE_CHECK_IR] a planned decision is checked against
    that one. *)
val match_kind : Miniml.ml_type -> Miniml.ml_branch array -> Miniml.Occurrence.t -> Match_kind.t

(** How many calls the unit elaborated ahead, and how many emission found
    there or elaborated itself. *)
val report : unit -> string
