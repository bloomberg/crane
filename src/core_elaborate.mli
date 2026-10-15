(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global calls elaborated from Core, ahead of translation
    (docs/Pipeline-Disentangling-Plan.md, section 4.7): each global
    application of a unit's frozen program, with the role each of its
    arguments has, elaborated in a lexical environment of the walk's own.

    Transitional.  The roles are kept per unit by the [MLglob] node naming
    the callee, which survives the annotation rewrites a body goes through
    before it is translated, and emission takes a call's roles from here
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
    declarations, replacing the unit's previous elaborations. *)
val structure : Miniml.ml_structure -> unit

(** [elaboration ~lex use args] -- the elaboration of the call [use args]
    while emitting: its arguments in the roles {!structure} found for the
    application naming its callee by [use], or, where it found none, as
    elaborated here in [lex].  Planning elaborates every call itself. *)
val elaboration : lex:Lexenv.t -> Miniml.global_use -> Miniml.ml_ast list -> Elaborated_call.t

(** How many calls the unit elaborated ahead, and how many emission found
    there or elaborated itself. *)
val report : unit -> string
