(** Found by Ephyra (round 19). [Crane Bake] of a long list (30000 cells)
    under [Set Crane Loopify].  The list is baked and read back at static
    initialisation; [count = 30000].

    Fixed: the program crashed before [main] with a stack overflow in
    [crane::bake::reader::get]: the reader decoded a generated inductive
    node by node recursively ([get<List<bool>>] -> [get_fields<Cons>] ->
    [get<std::shared_ptr<List<bool>>>] -> ...), one group of frames per
    cell, and the writer recursed the same way.  Both now walk the fields of
    a node that hold a node of its own type with an explicit stack, for any
    self-recursive inductive and whichever field holds the spine. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

Module BakeLongList.

Definition flags : list bool := repeat true 30000.

Definition count : nat := List.length (filter (fun b => b) flags).

End BakeLongList.

Crane Bake BakeLongList.flags.

Crane Extraction "bake_long_list" BakeLongList.
