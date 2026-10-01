(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The one registry of mutable cells that must be emptied between runs.  A
    cell enrols where it is defined, with the scope it lives for. *)

(** How long a cell's contents are good for.
    - [Extraction]: one [Crane Extraction] command.
    - [Unit]: one generated file; also emptied when an extraction starts. *)
type scope = Extraction | Unit

(** Enrol a reset action.  Actions of one scope run in enrolment order. *)
val on_reset : scope -> (unit -> unit) -> unit

(** Run every action enrolled for [scope]. *)
val reset : scope -> unit

(** A ref restored to its initial value by {!reset}. *)
val cell : scope -> 'a -> 'a ref

(** A hash table emptied by {!reset}. *)
val table : scope -> int -> ('a, 'b) Hashtbl.t
