(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Instrumentation and boundary checks for the type-argument numbering
    refactor (docs/Type-Argument-Numbering-Refactor-Plan.md).

    A probe records that a guarded or repairing code path was taken, so a
    corpus sweep can say how often each still fires.  Lines go to the file
    named by [CRANE_PROBE], appended one per hit, so that parallel [coqc]
    runs share one log; with the variable unset a probe costs a lazy check.
    [Feedback] is not used: it collapses identical messages, which would hide
    the count. *)

(** Whether [CRANE_PROBE] names a log. *)
val enabled : unit -> bool

(** [hit tag detail] appends ["tag detail"] to the log; [detail] is only
    computed when probing is on. *)
val hit : string -> (unit -> string) -> unit

(** [hit_at tag r] records a hit naming the global [r]. *)
val hit_at : string -> Names.GlobRef.t -> unit

(** [changed tag r ~before after] is [after], recording a hit at [r] when it
    differs from [before]: a repair that fired. *)
val changed : string -> Names.GlobRef.t -> before:'a -> 'a -> 'a

(** Whether [CRANE_LOOPIFY_CENSUS] names a log: the census of what the
    checks report with Loopify on everywhere, which
    [scripts/loopify-census.sh] takes.  Loopify is opt-in, so without it the
    recursion plan is checked against the few functions that ask for it.  A
    census turns Loopify on for every function not excluded by name, records
    each violation in the log instead of failing, and writes no files: what
    it extracts is not what the tests compile.  Named [write:<log>], it does
    write them, into the directories the tests name, for
    [scripts/loopify-census.sh --compile] to compile. *)
val census : unit -> bool

(** Whether a census is being taken that writes no files. *)
val census_dry : unit -> bool

(** [census_unit ()] records in the census log that the library being
    compiled extracted a unit, so that a census that reached nothing does
    not pass for one that found nothing. *)
val census_unit : unit -> unit

(** Whether [CRANE_CHECK_IR] is set, or a census is being taken. *)
val checking : unit -> bool

(** [violation what detail] fails extraction under [CRANE_CHECK_IR] with a
    report naming the invariant [what], records it in a census, and does
    nothing otherwise. *)
val violation : string -> Pp.t -> unit
