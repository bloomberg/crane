(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Type]: Core type expressions -- arrows, applied globals, type
    variables, metavariables, holes, open annotations and erased slots. *)

include Grammar.Type

(** A type of the frozen program ({!Phase.frozen}). *)
type t = Phase.frozen at

(** A type of the extracted program, which may hold metavariables. *)
type extracted = Phase.extracted at
