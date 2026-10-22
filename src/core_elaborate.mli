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
    taken from here is checked against that one. *)

(** [elaborate_arguments ~lex use args] -- the call [use args] as Core
    elaborates it from the call alone: which arguments are dictionaries,
    regular, or past the callee's arity and so applied to its result.  A
    variable argument is read off the binder it names in [lex].  The holes
    the call's context states are not resolved here. *)
val elaborate_arguments : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** A unit's elaborated calls. *)
type t

(** [structure s] elaborates every global application in [s]'s
    declarations -- in their bodies, in an instance's methods as
    {!Instance_methods} elaborates them, and in the terms custom types are
    applied to in the types they write, a match branch's result type and
    the declared type of every global they call included -- and every
    global named there unapplied, as its call with no arguments. *)
val structure : Miniml.ml_structure -> t

(** [declaration_scope ty body] is the lexical environment a definition of
    type [ty] generates its body [body] in, its parameters bound at the
    types the body is generated with and those an eta-expansion adds after
    them, and the body as generated: applied to the added parameters. *)
val declaration_scope : Miniml.ml_type -> Miniml.ml_ast -> Lexenv.t * Miniml.ml_ast

(** [generated_scope ty body] is {!declaration_scope}, with every
    let-bound lambda in the body as translation generates it
    ({!Translation_support.let_lambda}): an alias of a polymorphic function
    put in place of its uses, and a lambda bound as a value given a binder
    for each value arrow of its type
    ({!Translation_support.eta_bound_lambda}).  This is the term translation
    generates, whose binders are the ones it declares: an inlined alias binds
    nothing, so a binder after one is at a level the body as written puts it
    one deeper, and the binders an eta-expansion adds put those inside it
    deeper still. *)
val generated_scope : Miniml.ml_type -> Miniml.ml_ast -> Lexenv.t * Miniml.ml_ast

(** Every global the declarations walked name, applied or not, in their
    bodies or in a term a custom type is applied to in any type the unit
    writes, specifications' and the declared types of the globals they
    call included. *)
val referenced : t -> Names.GlobRef.t list

(** [roles t use n] -- the roles of the arguments of the application, with
    [n] arguments, that names its callee by [use], as [t] elaborated it; none
    for an application [t] did not walk. *)
val roles : t -> Miniml.global_use -> int -> Elaborated_call.role list option

(** Make [t] the unit's elaborations, the ones {!elaboration} reads. *)
val install : t -> unit

(** [elaboration ~lex use args] -- the elaboration of the call [use args]
    while emitting: its arguments in the roles the installed elaborations
    have for the application naming its callee by [use], or, where they have
    none, as elaborated here in [lex] -- which under [CRANE_CHECK_IR] is a
    violation: every call emission translates was elaborated from Core.
    Planning elaborates every call itself. *)
val elaboration : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** How many calls the unit elaborated ahead, and how many emission found
    there or elaborated itself. *)
val report : unit -> string
