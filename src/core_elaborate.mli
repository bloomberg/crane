(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global calls elaborated from Core, ahead of translation
    (docs/Pipeline-Disentangling-Plan.md, section 4.7): each global
    application of a unit's frozen program, with the role each of its
    arguments has, elaborated in a lexical environment of the walk's own.

    Transitional.  The roles are kept per unit by the occurrence of the use
    naming the callee ({!Miniml.Occurrence}), which the annotation rewrites a
    body goes through before it is translated keep, and emission takes a
    call's roles from here
    when it translates that application; a call translation built itself --
    a flattened spine, arguments pushed into a branch, a term inside a type
    -- is elaborated where it is translated, in the traversal's
    environment.  Under [CRANE_CHECK_IR] every elaboration taken from here
    is checked against that one. *)

(** [elaborate_arguments ~lex use args] -- the call [use args] as Core
    elaborates it from the call alone: which arguments are dictionaries,
    regular, or past the callee's arity and so applied to its result.  A
    variable argument is read off the binder it names in [lex].  The holes
    the call's context states are not resolved here. *)
val elaborate_arguments : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** [structure s] elaborates every global application in [s]'s
    declarations -- in their bodies, and in the terms custom types are
    applied to in the types they write -- and every global named there
    unapplied, as its call with no arguments, replacing the unit's previous
    elaborations. *)
val structure : Miniml.ml_structure -> unit

(** Every global the declarations {!structure} walked name, applied or not,
    in their bodies or in a term a custom type is applied to in any type the
    unit writes, specifications' included. *)
val referenced : unit -> Names.GlobRef.t list

(** [elaboration ~lex use args] -- the elaboration of the call [use args]
    while emitting: its arguments in the roles {!structure} found for the
    application naming its callee by [use], or, where it found none, as
    elaborated here in [lex].  Planning elaborates every call itself. *)
val elaboration : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** How many calls the unit elaborated ahead, and how many emission found
    there or elaborated itself. *)
val report : unit -> string
