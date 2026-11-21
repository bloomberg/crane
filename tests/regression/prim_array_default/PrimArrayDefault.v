(** Found by Ephyra (round 20). [PrimArray.default] under [Mapping.Std]
    (which maps [PrimArray.array] to [persistent_array] through
    [Mapping.Shared]).

    Expected: [dflt = 7], the default element given to [make].

    Fixed: the C++ threw at static initialisation: "unrealized axiom:
    Corelib.Array.PrimArray.default".  [Mapping.Shared] mapped [make],
    [get], [set], [length], [copy], not [default]; it is now
    [persistent_array::default_value()].  The audit of the other primitive
    types found PrimInt63 and PrimFloat primitives unmapped too, now mapped
    and tested in [prim_int63_float_ops]; the BDE [persistent_array] did not
    clamp [make]'s length to [max_length] and now does.  Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimInt63 PrimArray.
Open Scope uint63_scope.

Module PrimArrayDefault.

Definition arr : array nat := PrimArray.make 2 7%nat.

Definition dflt : nat := PrimArray.default arr.

End PrimArrayDefault.

Crane Extraction "prim_array_default" PrimArrayDefault.
