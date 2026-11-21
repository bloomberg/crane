(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Moves of a frame machine's loop invariants on its final path.

    A Loopify frame machine keeps a parameter the recursion passes on
    unchanged out of its frames: it is a loop invariant, read in place by
    every activation, so its moves are dropped.  One kind of machine runs
    exactly one final activation, after every other read of the invariant:
    each path of the entry handler pushes at most one entry frame, and no
    other handler pushes one or reads the invariant.  The entry frames then
    form a chain, one pending at a time, ending in the one activation that
    pushes none.  A path of the entry handler that pushes no entry frame and
    that no push follows is that activation's, and a move of the invariant
    there is its last use, as it was in the source's deepest call.  A test
    or a scrutinee is read before its branch is chosen, and a loop or a
    closure may run a path more than once: those keep no move.

    An entry frame is pushed by [_stack.emplace_back(E{...})], [E] the entry
    frame's struct.  Loopify keeps the moves ({!keep_final_moves}) and
    {!Move_check} accepts them ({!erase_final_moves}), each deciding from the
    machine's handlers by {!movable}. *)

type stmt = Cpp_ir.Lowered.Stmt.t

(** Whether a statement may push the entry frame [entry], anywhere in it. *)
val pushes : entry:Names.Id.t -> stmt -> bool

(** [movable ~entry ~entry_body ~others candidates]: the [candidates] the
    final path may move, given the entry handler's body and the other
    handlers' bodies; empty unless the machine has the shape above. *)
val movable :
  entry:Names.Id.t -> entry_body:stmt list -> others:stmt list list -> Names.Id.Set.t -> Names.Id.Set.t

(** Whether a frame struct declared among [stmts] keeps a pointer, which may
    point into a local the final path moves. *)
val frames_point : stmt list -> bool

(** [keep_final_moves ~entry keep stmts]: the entry handler [stmts] with the
    moves of [keep] dropped everywhere except on its final paths. *)
val keep_final_moves : entry:Names.Id.t -> Names.Id.Set.t -> stmt list -> stmt list

(** [stmts] with the final-path moves of every frame machine in it that
    {!movable} allows read as reads, for a check that does not follow the
    machine's protocol.  A machine is recognised as Loopify builds it: the
    push of its entry frame, then [while] over a frame binding and a match
    on the frame; one taking an address anywhere, or followed by a read of
    the local, is left alone. *)
val erase_final_moves : stmt list -> stmt list
