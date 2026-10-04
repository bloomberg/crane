(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The spelling of the names Crane invents.

    C++ reserves to the implementation, in every scope, an identifier that
    begins with an underscore and an uppercase letter, or that holds two
    consecutive underscores.  So the types and template parameters Crane
    invents -- loop frames, conversion parameters, carrier aliases' element
    parameters -- are spelled [Crane<Role>] ([CraneEnter], [CraneU0]), and the
    locals it derives from another name are joined to it without doubling an
    underscore.  A local keeps its leading underscore and lowercase letter,
    which only the global namespace reserves.

    Every invented name of these kinds is spelled here, so the convention has
    one statement. *)

(** [s] with no two underscores side by side: the second of a pair is spelled
    [p] -- the prime that, in [acc''], became the pair in the first place.  The
    one rule every spelling here and every escaped source name obeys.  A name
    this changes may land on another one, which the caller resolves as for
    every other escaped name. *)
val separate_underscores : string -> string

(** [role r] is the name of the invented entity whose role is [r]: an
    identifier beginning with an uppercase letter, such as ["Enter"]. *)
val role : string -> string

(** {!role} as an identifier. *)
val id : string -> Names.Id.t

(** [indexed r i] is the [i]-th of a family of entities of role [r]
    ([CraneU0], [CraneU1]). *)
val indexed : string -> int -> Names.Id.t

(** [member r ~of_:n i] is the [i]-th of [n] entities of role [r]: {!id} when
    there is only one, {!indexed} otherwise ([CraneU], or [CraneU0] and
    [CraneU1]). *)
val member : string -> of_:int -> int -> Names.Id.t

(** [companion x r] is the generated companion of the member [x] in role [r]
    ([cons_crane_reuse], the reuse factory beside [cons]).  The [_crane_]
    infix marks it as generated; a source name would have to spell it out to
    collide. *)
val companion : Names.Id.t -> string -> Names.Id.t

(** [prefixed p x] is a local derived from [x] and marked by [p] (a prefix
    such as ["_loop"], with no trailing underscore): [_loop_x], or [_loop_self]
    for [x = _self] rather than [_loop__self]. *)
val prefixed : string -> Names.Id.t -> Names.Id.t
