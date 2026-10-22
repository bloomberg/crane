(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane's functional Core IR: an extracted program, at a named phase.

    The phases share MiniML's grammar.  What tells them apart is which passes
    have run, and the type says it: a backend entry point takes a
    [normalized program], and a structure only becomes one through
    {!optimize}, {!freeze} and then {!normalize}.  Selecting whole top-level
    modules keeps the phase; nothing else builds a program.

    Transitional.  {!freeze} checks the structural invariants that hold
    today.  It leaves no metavariable in the program: each solved one is
    replaced by its solution and each unsolved one by an immutable open
    annotation ({!Miniml.Topen}), read as erased.  A local definition's open
    types are minted before it ({!Local_types}), and a slot filling a hole
    hands the answer to the terms that mention the hole.  [CRANE_CHECK_IR]
    checks that, as it does that rendering leaves the program it was planned
    against unchanged; {!structure} is the read-only view unconverted
    consumers take. *)

type extracted
type optimized
type frozen
type normalized

type 'phase program

(** The immediate result of extraction. *)
val extracted : Miniml.ml_structure -> extracted program

(** [optimize passes p] runs the Core passes over [p]. *)
val optimize : (Miniml.ml_structure -> Miniml.ml_structure) -> extracted program -> optimized program

(** [freeze p] is [p], checked: every recursive group is nonempty and its
    selected member exists, no reference is declared twice, and every
    polymorphic use is instantiated at its callee's own scheme with no
    metavariable in its instantiation.  Its annotations hold no metavariable
    either: each is replaced by its solution, or by an open annotation where
    extraction left it unsolved, and from here until the extraction ends none
    is made or solved.  Under [CRANE_TRACE_PIPELINE] it reports how many open
    annotations the program holds. *)
val freeze : optimized program -> frozen program

(** [normalize pass p] is [p] in the form control lowering reads: [pass]
    ({!Normalize.structure}) binds each call a function Loopify transforms
    makes to its own recursive group, where it is evaluated strictly and not
    in tail position, to a temporary of its own, in evaluation order.  It
    runs on the frozen program and so solves nothing: a temporary whose type
    the call does not say is given an open annotation.  Under
    [CRANE_CHECK_IR] the result is a fixed point of [pass] -- normalizing it
    again rewrites no top-level element -- which is what says that no such
    call was left unbound. *)
val normalize : (Miniml.ml_structure -> Miniml.ml_structure) -> frozen program -> normalized program

(** The structure, for the consumers not converted to the phase types. *)
val structure : 'phase program -> Miniml.ml_structure

(** [partition keep p] splits [p]'s top-level modules by [keep]. *)
val partition : (Names.ModPath.t -> bool) -> 'phase program -> 'phase program * 'phase program

(** Each top-level module of [p], as a program of its own. *)
val modules : 'phase program -> (Names.ModPath.t * 'phase program) list

(** The open annotations reachable from [p]'s annotations
    ({!Miniml.Topen}), each counted once. *)
val open_annotations : 'phase program -> int
