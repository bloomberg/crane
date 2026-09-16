(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Last-use move insertion.

    A generated body threads owned values -- a [shared_ptr] to an inductive
    node, an [immer] vector, a pair of the two -- through a chain of locals,
    and reads each one for the last time when it hands it on.  Written as a
    plain read, that last hand-off copies: a reference count up here and back
    down there, for a value nobody looks at again.  This pass finds those
    reads and writes [std::move] around them.

    It is a backward liveness walk over one function body.  A read of [x]
    becomes a move when [x] is a local or by-value parameter worth moving,
    nothing after the read looks at [x] again, and the read is the only one in
    its statement -- C++ does not say in which order a call evaluates its
    arguments, so two reads in one statement cannot be ordered against each
    other.

    Everywhere it cannot see the whole picture it declines: a body containing
    raw C++ is left alone entirely, and so is any variable captured by a
    lambda, bound to a reference, passed to an inline custom (whose template
    string may mention it twice), or destructured by a match.

    Runs on MiniCpp after {!Loopify} and {!Cpp_depth}, so it sees the frame
    stacks and the flattened temporaries that carry most of the traffic, and
    before erasure, which does not move code around.  [Unset Crane
    MoveLastUse] turns it off. *)

open Minicpp

val transform_decl : cpp_decl -> cpp_decl
(** Rewrite the bodies of every function, method and destructor in [d],
    descending through templates, namespaces and structs.  Anything else is
    returned unchanged. *)
