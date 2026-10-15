(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane's functional Core IR: an extracted program, at a named phase.

    The phases share MiniML's grammar.  What tells them apart is which passes
    have run, and the type says it: a backend entry point takes a [frozen
    program], and a structure only becomes one through {!optimize} and then
    {!freeze}.  Selecting whole top-level modules keeps the phase; nothing
    else builds a program.

    Transitional.  {!freeze} checks the structural invariants that hold
    today.  Nothing solves a metavariable after it -- a local definition's
    open types are minted before it ({!Local_types}), and a slot filling a
    hole hands the answer to the terms that mention the hole instead of
    writing it -- and [CRANE_CHECK_IR] enforces that, as it does that
    rendering leaves the program it was planned against unchanged.  The
    metavariables extraction left unsolved are still reachable, read as
    erased: {!freeze} reports how many, and {!structure} is the read-only
    view unconverted consumers take. *)

type extracted
type optimized
type frozen

type 'phase program

(** The immediate result of extraction. *)
val extracted : Miniml.ml_structure -> extracted program

(** [optimize passes p] runs the Core passes over [p]. *)
val optimize : (Miniml.ml_structure -> Miniml.ml_structure) -> extracted program -> optimized program

(** [freeze p] is [p], checked: every recursive group is nonempty and its
    selected member exists, and no reference is declared twice.  From here
    until the extraction ends no metavariable is solved.  Under
    [CRANE_TRACE_PIPELINE] it reports the unsolved metavariables still
    reachable. *)
val freeze : optimized program -> frozen program

(** The structure, for the consumers not converted to the phase types. *)
val structure : 'phase program -> Miniml.ml_structure

(** [partition keep p] splits [p]'s top-level modules by [keep]. *)
val partition : (Names.ModPath.t -> bool) -> 'phase program -> 'phase program * 'phase program

(** Each top-level module of [p], as a program of its own. *)
val modules : 'phase program -> (Names.ModPath.t * 'phase program) list

(** The unsolved metavariables reachable from [p]'s annotations, each
    counted once. *)
val unsolved_metas : 'phase program -> int
