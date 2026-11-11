(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A unit's declarations finished for the printer, as one program.

    Every declaration a file writes is finished ({!Cpp_pipeline.finish})
    once, ahead of the files, by the driver ({!finish}): the walk that
    generates the unit's declarations says what each needs finished and
    whose generation it belongs to, and the driver finishes all of it into a
    program -- the finished declarations in the order they were finished,
    each under its {!id}, with the headers they need.  The driver installs
    the program ({!install}); nothing else finishes a declaration.

    This is the seed of the plan's [CppIR.Resolved.program]
    (docs/Pipeline-Disentangling-Plan.md, Milestone 8): a value holding every
    declaration of the unit, helpers included, each under an identity that
    does not depend on the order anything was generated or finished in.  It
    is a top-level module rather than a member of a [src/cpp_ir/] directory
    on purpose: a directory is one node of the dependency graph, and this
    module reaches the whole MiniCpp pipeline ({!Cpp_pipeline},
    {!Cpp_erasure}), so as a member it would keep every pass from ever naming
    [Cpp_ir].

    A file's render finds a declaration by its {!id}: the render takes the
    generation it writes from the walk ahead of the files, and numbers its
    declarations as the walk did when it said what to finish. *)

(** Which of its owner's declarations a declaration is. *)
type part =
  | Declaration of int
      (** the [n]th declaration its owner's generation gives to finish *)
  | Methods
      (** the methods of the owner, an eponymous record, as the members of
          the struct they are merged into: a generation of their own *)

(** The identity of a declaration of the program: the entity it belongs to
    ({!Generated_program.id}: a source declaration, or a helper lifted out
    of one, by its {!Generated_entity_id}), and which of its declarations it
    is. *)
type id = {
  owner : Generated_program.id;
  part : part;
}

val pp_id : id -> Pp.t

(** A declaration to finish, under the identity it gets in the program. *)
type job

(** [job id d] is [d], to finish as the declaration [id]. *)
val job : id -> Minicpp.cpp_decl -> job

(** A declaration of a program. *)
type declaration = {
  id : id;
  finished : Cpp_erasure.settled;
}

(** A unit's finished program. *)
type t

(** [finish jobs] is the program of [jobs], each finished once, in order: a
    job whose {!id} an earlier one finished already is that declaration.
    Under [CRANE_CHECK_IR], two different declarations under one {!id} are a
    violation. *)
val finish : job list -> t

(** The declarations of a program, in the order they were finished. *)
val declarations : t -> declaration list

(** The helpers of a program: its declarations owned by a generated entity
    ({!Generated_program.Generated}), in the order they were finished. *)
val helpers : t -> (Generated_entity_id.t * Cpp_erasure.settled) list

(** The headers the declarations of a program need for what they write down
    ({!Cpp_demands}). *)
val demands : t -> Table.header list

(** The globals the declarations of a program write the names of
    ({!Cpp_demands.globals_of_decl}). *)
val globals : t -> Names.GlobRef.t list

(** Under [CRANE_CHECK_IR], fail unless the declarations of [t] belong to
    exactly the entities of the unit's generated program
    ({!Generated_program.generated_ahead_ids}) that have anything to finish:
    each owner one of them, and each helper among them finished. *)
val check_against_generated : t -> unit

(** {!globals} of the installed program. *)
val installed_globals : unit -> Names.GlobRef.t list

(** The declarations of the installed program, in the order they were
    finished. *)
val installed_declarations : unit -> Cpp_erasure.settled list

(** The promoted type variables the installed program's declarations write
    ({!Cpp_demands.promoted_of_decl}), in the order they were finished. *)
val installed_promoted : unit -> Names.Id.t list

(** Make [t] the unit's program, the one {!find} reads. *)
val install : t -> unit

(** [refinish jobs] finishes [jobs] again, in order, and fails unless each
    comes out as it is in the installed program, under the same {!id}. *)
val refinish : job list -> unit

(** The declaration [id] of the installed program, if it is there. *)
val find : id -> Cpp_erasure.settled option

(** [finishes_as d f] is whether finishing [d] again gives [f]. *)
val finishes_as : Minicpp.cpp_decl -> Cpp_erasure.settled -> bool
