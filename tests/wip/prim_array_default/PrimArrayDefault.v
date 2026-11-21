(** Found by Ephyra (round 20). [PrimArray.default] under [Mapping.Std]
    (which maps [PrimArray.array] to [persistent_array] through
    [Mapping.Shared]).

    Expected: [dflt = 7], the default element given to [make].

    Actual: extraction succeeds, but the C++ throws at static
    initialisation: "unrealized axiom: Corelib.Array.PrimArray.default".
    [Mapping.Shared] maps [make], [get], [set], [length], [copy] (and
    [max_length] is a constant), not [default], although [persistent_array]
    stores its default element. Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimInt63 PrimArray.
Open Scope uint63_scope.

Module PrimArrayDefault.

Definition arr : array nat := PrimArray.make 2 7%nat.

Definition dflt : nat := PrimArray.default arr.

End PrimArrayDefault.

Crane Extraction "prim_array_default" PrimArrayDefault.
