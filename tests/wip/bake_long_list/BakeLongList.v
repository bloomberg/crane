(** Found by Ephyra (round 19). [Crane Bake] of a long list (30000 cells)
    under [Set Crane Loopify].

    Expected: the list is baked and read back at static initialisation;
    [count = 30000]. Without [Crane Bake] the same program prints 30000.

    Actual: the bake itself succeeds, but the program crashes before [main]
    (SIGSEGV; under ASan "stack-overflow" in [crane::bake::reader::get]).
    The reader decodes a generated inductive node by node recursively
    ([get<List<bool>>] -> [get_fields<Cons>] -> [get<std::shared_ptr<List<bool>>>]
    -> [get<List<bool>>] ...), so its stack depth is the length of the list.
    A list-shaped (right-recursive) value needs an iterative read, as Loopify
    gives the program itself. 20000 cells already overflow an 8 MB stack at
    -O0. *)
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
