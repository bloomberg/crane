(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A unit's program: what it generated and what that finished as, one
    value keyed by one kind of id.

    The walk ahead of the files generates every declaration the files write,
    and records each source declaration's generation as an {!entity}
    ({!record_ahead}), with the helpers lifted out of its bodies
    ({!record_lifted_ahead}); nothing records a helper as it is lifted.  An
    entity names the declarations its generation gives to finish by their
    {!id}.  The driver then finishes all of them at once ({!finish}), each
    {!Cpp_pipeline.finish}ed once under its id, and installs the program
    ({!install}); nothing else finishes a declaration.  A file's render
    finds what it writes by id ({!find}): it takes the generation it writes
    from the walk ahead of the files, and numbers its declarations as the
    walk did.

    Each file's render records the entities it takes ({!record}).
    {!check_against_ahead} holds them to the entities and declarations
    generated ahead, and {!check_against_plan} holds every unit to
    "emission generates what the unit declares, and the helpers lifted out
    of it".  Both run once a unit's files are written ([Extract_env]).

    It is a top-level module rather than a member of a [src/cpp_ir/]
    directory on purpose: a directory is one node of the dependency graph,
    and this module reaches the whole MiniCpp pipeline ({!Cpp_pipeline},
    {!Cpp_erasure}), so as a member it would keep every pass from ever
    naming [Cpp_ir]. *)

(** {2 Ids} *)

(** Whose generation a declaration belongs to: a source declaration's, or a
    helper lifted out of one. *)
type owner =
  | Source of Entity_id.t
  | Generated of Generated_entity_id.t

(** Source entities before helpers, each kind by its own order. *)
val compare_owner : owner -> owner -> int

val pp_owner : owner -> Pp.t

(** Sets of owners, ordered by {!compare_owner}. *)
module Owner_set : Set.S with type elt = owner

(** Which of its owner's declarations a declaration is. *)
type part =
  | Declaration of int
      (** the [n]th declaration its owner's generation gives to finish *)
  | Methods
      (** the methods of the owner, an eponymous record, as the members of
          the struct they are merged into.  Each method is an entity of its
          own, and all of them name this one declaration: they are finished
          together, because they pass through every stage a member of the
          struct does. *)

(** The identity of a declaration of the program. *)
type id = {
  owner : owner;
  part : part;
}

val pp_id : id -> Pp.t

(** {2 Generations} *)

(** A helper lifted out of a body. *)
type helper = {
  helper_id : Generated_entity_id.t;
      (** The helper's identity, made from its {!Lifted.t}. *)
  helper_decl : Minicpp.cpp_decl;
      (** The declaration that defines it. *)
}

(** [helper d] is the helper [d] declares, if [d] is a lifted helper. *)
val helper : Minicpp.cpp_decl -> helper option

(** [helper_declaration h] is the id of [h]'s declaration: the only one of
    its own generation. *)
val helper_declaration : helper -> id

(** One source declaration's generation. *)
type entity = {
  entity_id : Entity_id.t;
      (** The source declaration generated. *)
  declarations : id list;
      (** The declarations generating it gave to finish, in order: its own,
          or, for a method of an eponymous record, its record's
          {!Methods}. *)
  helpers : helper list;
      (** The helpers lifted out of its bodies that this generation claimed:
          a helper another entity lifted first in the same file is that
          entity's. *)
}

(** The globals [decls] name ({!Minicpp.iter_globrefs}): what has to be
    declared before them. *)
val dependencies : Minicpp.cpp_decl list -> Entity_id.Set.t

(** {2 The program} *)

(** A declaration to finish, under its id. *)
type job

(** [job id d] is [d], to finish as the declaration [id]. *)
val job : id -> Minicpp.cpp_decl -> job

(** A finished declaration of a program. *)
type declaration = {
  id : id;
  finished : Cpp_erasure.settled;
}

(** A unit's program. *)
type t

(** The source declarations' generations of a program, in the order they
    were recorded. *)
val entities : t -> entity list

(** The finished declarations of a program, in the order they were
    finished. *)
val declarations : t -> declaration list

(** The finished helpers of a program, in the order they were finished. *)
val helpers : t -> (Generated_entity_id.t * Cpp_erasure.settled) list

(** The headers the declarations of a program need for what they write down
    ({!Cpp_demands}). *)
val demands : t -> Table.header list

(** The globals the declarations of a program write the names of
    ({!Cpp_demands.globals_of_decl}). *)
val globals : t -> Names.GlobRef.t list

(** {2 Building the unit's program}

    The unit's program is accumulated as the walk ahead of the files
    generates it, finished, and installed; it is emptied with the other
    per-unit state. *)

(** [record_ahead e] adds [e], and the helpers lifted out of it, to the
    unit's program as the walk ahead of the files generates it. *)
val record_ahead : entity -> unit

(** [record_lifted_ahead ds] adds the helpers among [ds], lifted by some
    generation of the walk ahead of the files, to the unit's program.  Under
    [CRANE_CHECK_IR] a helper is lifted by one generation: a second
    declaration of one already recorded is a violation, the same declaration
    handed on to another generation is not. *)
val record_lifted_ahead : Minicpp.cpp_decl list -> unit

(** [finish jobs] is the unit's program with [jobs] finished, each once, in
    order: a job whose {!id} an earlier one finished already is that
    declaration.  Under [CRANE_CHECK_IR], two different declarations under
    one id are a violation, and so is a finished declaration that does not
    convert to CppIR ({!Legacy_minicpp_to_cpp_ir}). *)
val finish : job list -> t

(** Under [CRANE_CHECK_IR], fail unless [t] finished exactly the
    declarations its generations gave: those its entities name, and each
    lifted helper's. *)
val check_finished : t -> unit

(** Make [t] the unit's program, the one {!find} reads. *)
val install : t -> unit

(** {2 Reading the installed program} *)

(** The declaration [id] of the installed program, if it is there. *)
val find : id -> Cpp_erasure.settled option

(** [finishes_as d f] is whether finishing [d] again gives [f]. *)
val finishes_as : Minicpp.cpp_decl -> Cpp_erasure.settled -> bool

(** [refinish jobs] finishes [jobs] again, in order, and fails unless each
    comes out as it is in the installed program, under the same {!id}. *)
val refinish : job list -> unit

(** {!globals} of the installed program. *)
val installed_globals : unit -> Names.GlobRef.t list

(** The declarations of the installed program, in the order they were
    finished. *)
val installed_declarations : unit -> Cpp_erasure.settled list

(** The promoted type variables the installed program's declarations write
    ({!Cpp_demands.promoted_of_decl}), in the order they were finished. *)
val installed_promoted : unit -> Names.Id.t list

(** {2 Checking what the files took} *)

(** [record e] adds [e] to what the files have taken, and returns it.
    Nothing is generated while planning. *)
val record : entity -> entity

(** Under [CRANE_CHECK_IR], fail unless every entity generated ahead of the
    files or taken by them is one the unit [declares], and every helper was
    lifted out of an entity the unit declares or generated, or out of none:
    emission generates what was planned, and the helpers its bodies lift. *)
val check_against_plan : declares:(Names.GlobRef.t -> bool) -> unit

(** Under [CRANE_CHECK_IR], fail unless the entities the two files took,
    with the helpers they claimed and the declarations they name, are
    exactly those generated ahead of them: the walk ahead generates what the
    renders write, and nothing else. *)
val check_against_ahead : unit -> unit
