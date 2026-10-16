(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A unit's declarations finished for the printer, as one program.

    Every declaration a file writes is finished ({!Cpp_pipeline.finish})
    once, ahead of the files, by the driver ({!finish}): the walk that
    generates the unit's declarations says what each needs finished, and
    the driver finishes all of it, each result recorded by the physical
    identity of what was finished.  The files read the results from here
    ({!find}); nothing else finishes a declaration. *)

(** A declaration to finish, with the physical identity of what it was made
    of, which its result is recorded by. *)
type job

(** [job d] is [d] to finish, recorded by [d] itself. *)
val job : Minicpp.cpp_decl -> job

(** [job_of key d] is [d] to finish, recorded by [key]: a declaration
    assembled from a generation, by the generation. *)
val job_of : 'a -> Minicpp.cpp_decl -> job

(** [finish jobs] finishes every one of [jobs], in order, once each. *)
val finish : job list -> unit

(** [refinish jobs] finishes [jobs] again, in order, and fails unless each
    comes out as {!finish} finished it. *)
val refinish : job list -> unit

(** What {!finish} finished [job] as, if it did. *)
val find : job -> Cpp_erasure.settled option

(** [finishes_as job f] is whether finishing [job] again gives [f]. *)
val finishes_as : job -> Cpp_erasure.settled -> bool
