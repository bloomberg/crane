(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The identity of a helper Crane lifts out of a declaration body.

    A lifted helper is not a Rocq declaration, but it is emitted as a C++
    function and called like one, so it needs a [GlobRef.t] to travel under.
    What it must not have is an identity that {i is} that reference's spelling:
    two helpers lifted out of two different declarations are two helpers even
    when they were bound to the same name, and keying them by spelling alone
    silently merged them -- one definition emitted, the other's call sites left
    pointing at it.

    Here the identity is the pair the helper actually came from, the
    declaration it was lifted out of and the binder it was bound to there, and
    the spelling is derived from the identity rather than the other way round.
    {!make} is injective by construction: a spelling already taken by a
    different identity is not reused. *)

type t

(** [make ~origin ~binder] is the identity of the helper bound to [binder]
    inside [origin], creating it if this is the first time it is asked for and
    returning the same identity -- and so the same spelling -- on every later
    call, which is what lets the header and implementation passes agree.

    The helper's C++ name is decided in the unit being extracted by the same
    call, so nothing generated after the helper is made can miss it.

    [origin] is [None] only for a helper lifted outside any declaration.
    [fixpoint] is the Core fixpoint and the member of it the helper lowers,
    as the first call making the helper says. *)
val make :
  fixpoint:(Miniml.Occurrence.t * int) option -> origin:Names.GlobRef.t option -> binder:Names.Id.t -> t

(** The reference the helper is emitted and called under. *)
val ref_of : t -> Names.GlobRef.t

(** The helper a reference denotes, or [None] if it denotes something that is
    not a lifted helper. Exact: only references minted by {!make} are known,
    so an ordinary declaration that happens to be spelled like one does not
    answer here. *)
val of_ref : Names.GlobRef.t -> t option

(** The C++ name the helper is emitted under. *)
val name : t -> Names.Id.t

(** The declaration the helper was lifted out of. *)
val origin : t -> Names.GlobRef.t option

(** The binder the helper was bound to in {!origin}. *)
val binder : t -> Names.Id.t

(** The Core fixpoint, and the member of it, the helper lowers. *)
val fixpoint : t -> (Miniml.Occurrence.t * int) option

val equal : t -> t -> bool
