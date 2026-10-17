(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A unit's declarations finished for the printer, as one program.

    Every declaration a file writes is finished ({!Cpp_pipeline.finish})
    once, ahead of the files, by the driver ({!finish}): the walk that
    generates the unit's declarations says what each needs finished, and
    the driver finishes all of it into a program, each result recorded by
    the physical identity of what was finished, with the headers the
    finished declarations need.  The driver installs the program
    ({!install}); the files read the results from it ({!find}); nothing else
    finishes a declaration. *)

(** A declaration to finish, with the physical identity of what it was made
    of, which its result is recorded by. *)
type job

(** [job d] is [d] to finish, recorded by [d] itself. *)
val job : Minicpp.cpp_decl -> job

(** [job_of key d] is [d] to finish, recorded by [key]: a declaration
    assembled from a generation, by the generation. *)
val job_of : 'a -> Minicpp.cpp_decl -> job

(** A unit's finished program. *)
type t

(** [finish jobs] is the program of [jobs], each finished once, in order. *)
val finish : job list -> t

(** The headers the declarations of a program need for what they write down
    ({!Cpp_demands}). *)
val demands : t -> Table.header list

(** The globals the declarations of a program write the names of
    ({!Cpp_demands.globals_of_decl}). *)
val globals : t -> Names.GlobRef.t list

(** {!globals} of the installed program. *)
val installed_globals : unit -> Names.GlobRef.t list

(** The promoted type variables the installed program's declarations write
    ({!Cpp_demands.promoted_of_decl}), in the order they were finished. *)
val installed_promoted : unit -> Names.Id.t list

(** Make [t] the unit's program, the one {!find} reads. *)
val install : t -> unit

(** [refinish jobs] finishes [jobs] again, in order, and fails unless each
    comes out as it is in the installed program. *)
val refinish : job list -> unit

(** What [job] is finished as in the installed program, if it is there. *)
val find : job -> Cpp_erasure.settled option

(** [finishes_as job f] is whether finishing [job] again gives [f]. *)
val finishes_as : job -> Cpp_erasure.settled -> bool
