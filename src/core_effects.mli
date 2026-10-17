(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The effect operations of a unit's program, elaborated from Core ahead of
    translation (docs/Pipeline-Disentangling-Plan.md, section 4.7): which
    applications are a registered monad's [bind] or [ret] ([Crane Extract
    Monad]), and how each is generated.

    How is the declaration's: one whose codomain is a monad the extraction
    keeps as a tree is generated in {!Reified} mode, where [bind] and [ret]
    are calls building it; every other one in {!Sequential} mode, where the
    tree is erased, [bind m k] is [m] run and then [k]'s body continuing
    where the bind stands -- its tail position the enclosing one -- and
    [ret v] is [v].

    Transitional.  The operations are installed for the unit, by the
    occurrence of the use naming the operation ({!Miniml.Occurrence}), and
    translation takes an application's from there; under [CRANE_CHECK_IR]
    each is checked against the global's registration and the mode the
    generation translating it is in. *)

type mode =
  | Sequential  (** the monad erased: [bind] is sequencing, [ret] its value *)
  | Reified  (** the monad kept as a tree: [bind] and [ret] build it *)

type operation =
  | Bind
  | Return

type effect = {operation : operation; mode : mode}

(** The mode a monad's computations are generated in: {!Reified} for one
    extracted as a tree ({!Table.is_monad_reified}). *)
val mode_of_monad : Names.GlobRef.t -> mode

(** The operation the global is registered as, if it is one. *)
val operation_of : Names.GlobRef.t -> operation option

(** A unit's effect operations. *)
type t

val empty : t

(** [analyze s] -- every use of a [bind] or [ret] in [s]'s declarations'
    bodies, each with the mode of the declaration it is written in. *)
val analyze : Miniml.ml_structure -> t

val equal : t -> t -> bool

(** Make [t] the unit's operations, the ones {!find} reads. *)
val install : t -> unit

(** [lookup t use] -- the operation of the use [use] among [t], if the
    analysis reached it; [None] for a use it did not, or one whose copies a
    rewrite duplicated were found in two modes. *)
val lookup : t -> Miniml.global_use -> effect option

(** [find use] -- {!lookup} among the installed operations. *)
val find : Miniml.global_use -> effect option

(** Record that translation took an operation from the installed ones
    ([true]) or decided it itself ([false]), for {!report}. *)
val tally : found:bool -> unit

(** How many operations the unit analysed, and how many translation found
    there or decided itself. *)
val report : unit -> string
