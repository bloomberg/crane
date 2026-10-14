(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The pipeline's pass order as data.

    A stage that runs a sequence of passes declares it as a list of {!pass}
    values and runs it with {!run}.  The list is then the one statement of the
    order: the stage executes it, [CRANE_TRACE_PIPELINE] reports it as it
    executes, and [unit_tests/pipeline_manifest.ml] prints it for a golden
    file, so a change to the count or order of passes shows up in a diff
    rather than having to be noticed. *)

(** A named pass over ['a]. *)
type 'a pass = { name : string; run : 'a -> 'a }

(** [pass name run] is the pass [run] called [name]. *)
val pass : string -> ('a -> 'a) -> 'a pass

(** [effect name f] is a pass that observes its input without rewriting it:
    an analysis that records its result elsewhere. *)
val effect : string -> ('a -> unit) -> 'a pass

(** The names of [passes], in order. *)
val names : 'a pass list -> string list

(** Whether [CRANE_TRACE_PIPELINE] is set. *)
val enabled : unit -> bool

(** [event stage what] reports that [what] happened in [stage], under
    [CRANE_TRACE_PIPELINE]. *)
val event : string -> string -> unit

(** [run ~stage passes x] applies [passes] to [x] in order, reporting each
    under [CRANE_TRACE_PIPELINE]. *)
val run : stage:string -> 'a pass list -> 'a -> 'a
