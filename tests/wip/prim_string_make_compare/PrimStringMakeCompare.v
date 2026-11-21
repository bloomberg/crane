(** Found by Ephyra (round 19). [PrimString.make] and [PrimString.compare]
    under [Mapping.Std], which maps Rocq's primitive [string] to
    [std::string].

    Expected: [make 3 0] is three NUL bytes (its length is 3) and
    [compare "ab" "b"] is [Lt]; the program prints [1 1].

    Actual: extraction succeeds, but the C++ throws at static
    initialisation: "unrealized axiom: Corelib.Strings.PrimString.make" (and
    "... PrimString.compare" once [make] is gone). [Mapping.Std] maps only
    [length], [cat], [get] and [sub]; the other primitives of the mapped type
    are left as axioms. Also on main (legacy [Mapping.Std]). *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString PrimInt63.
Open Scope uint63_scope.

Module PrimStringMakeCompare.

Definition nuls : PrimString.string := PrimString.make 3 0.

Definition nul_length : bool := PrimInt63.eqb (PrimString.length nuls) 3.

Definition cmp_lt : bool :=
  match PrimString.compare "ab"%pstring "b"%pstring with Lt => true | _ => false end.

End PrimStringMakeCompare.

Crane Extraction "prim_string_make_compare" PrimStringMakeCompare.
