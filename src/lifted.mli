(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The identity of a helper Crane lifts out of a declaration body.

    A lifted helper is not a Rocq declaration, but it is emitted as a C++
    function and called like one, so it needs a [GlobRef.t] to travel under.
    What it must not have is an identity that {i is} that reference's spelling:
    two helpers lifted out of two different declarations are two helpers even
    when they were bound to the same name, and keying them by spelling alone
    silently merged them -- one definition emitted, the other's call sites left
    pointing at it.  Nor is the name of its binder enough: one declaration
    may bind two lambdas to one name, in two branches, and those are two
    helpers too.

    Here the identity is where the helper actually came from: the
    declaration it was lifted out of, the binder it was bound to there, and
    the Core term that bound it ({!site}).  The spelling is derived from the
    identity rather than the other way round.  {!make} is injective by
    construction: a spelling already taken by a different identity is not
    reused. *)

type t

(** The Core term a helper was bound by: a let binding a lambda, by the
    let's occurrence, or a member of a local fixpoint, by the fixpoint's
    occurrence and the member's index.  A copy of a term keeps its
    occurrence, so the helpers lifted from two copies of one let are one. *)
type site =
  | Let of Miniml.Occurrence.t
  | Fixpoint of Miniml.Occurrence.t * int

(** [make ~origin ~binder site] is the identity of the helper bound to
    [binder] by [site] inside [origin], creating it if this is the first time
    it is asked for and returning the same identity -- and so the same
    spelling -- on every later call, which is what lets the header and
    implementation passes agree.  An identity lasts for the extraction its
    site was made in.

    The helper's C++ name is decided in the unit being extracted by the same
    call, so nothing generated after the helper is made can miss it.

    [origin] is [None] only for a helper lifted outside any declaration. *)
val make : origin:Names.GlobRef.t option -> binder:Names.Id.t -> site -> t

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

(** The Core term that bound the helper. *)
val site : t -> site

(** The Core fixpoint, and the member of it, the helper lowers, if it
    lowers one. *)
val fixpoint : t -> (Miniml.Occurrence.t * int) option

(** Helpers ordered by origin and binder; two of one origin bound to one
    name, which no source order tells apart, in the order they were made. *)
val compare : t -> t -> int

val equal : t -> t -> bool
