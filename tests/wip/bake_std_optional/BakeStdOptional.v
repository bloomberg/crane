(** Found by Ephyra (round 19). [Crane Bake] of a closed constant of an
    [option] type under [Mapping.Std] (so [std::optional]).

    Expected: the baked constants read back as [Some 5] and [Some (Node Leaf
    3 Leaf)], and the program prints 5 and 3.

    Actual: the image is written correctly (presence word, then the value:
    [{1, 5}] for [Some 5]), but reading aborts at static initialisation:
    "crane::bake: the baked image does not match its type (too long)" for
    [option nat], "(a shared node)" for [option tree]. The global is
    copy-initialised from the [crane::bake::value] proxy, and
    [std::optional<T>]'s converting constructor wins over the proxy's
    [operator T]: it converts the proxy to the payload type, which reads the
    image as a bare [T] (the presence word as the payload). *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.

Module BakeStdOptional.

Inductive tree : Type := Leaf | Node (l : tree) (x : nat) (r : tree).

Definition num : option nat := Some 5.

Definition node : option tree := Some (Node Leaf 3 Leaf).

Definition num_value : nat := match num with Some n => n | None => 0 end.

Definition node_value : nat :=
  match node with Some (Node _ x _) => x | _ => 0 end.

End BakeStdOptional.

Crane Bake BakeStdOptional.num BakeStdOptional.node.

Crane Extraction "bake_std_optional" BakeStdOptional.
