(** Found by Ephyra (round 19). [Crane Bake] of a closed constant of an
    [option] type under [Mapping.Std] (so [std::optional]).  The baked
    constants read back as [Some 5] and [Some (Node Leaf 3 Leaf)], and the
    program prints 5 and 3.

    Fixed: reading aborted at static initialisation ("the baked image does
    not match its type (too long)").  The global was copy-initialised from
    the [crane::bake::value] proxy, and [std::optional<T>]'s converting
    constructor won over the proxy's [operator T]: it converted the proxy to
    the payload type, which read the image as a bare [T].  A baked global
    is now initialised with [crane::bake::read<T>(image)] at its declared
    type (CppIR [Baked_value]). *)
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
