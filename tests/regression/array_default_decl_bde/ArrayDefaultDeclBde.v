(** Found by Ephyra (round 21, BDE flavour). A [PrimArray] value chosen
    by a match whose scrutinee is a known constructor, passed to a lambda,
    under [Mapping.BDE].

    Expected: compiles; [result = 5].

    Fixed: "calling a private constructor of class
    'persistent_array<unsigned int>'".  The BDE flavour lowers the argument
    as [persistent_array<unsigned int> w; unsigned int n = 5u; w = ...;], a
    default-constructed declaration assigned later, and the BDE
    [persistent_array] (theories/cpp_bde) kept its default constructor
    private, with a null vector.  Like the std one it now has a public
    default constructor building the empty array. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Corelib Require Import PrimInt63 PrimArray.
Open Scope uint63_scope.
Module ArrayDefaultDeclBde.
Definition result : nat :=
  (fun w : array nat => PrimArray.get w 0)
    (match @inr bool nat 5%nat with inl _ => PrimArray.make 1 1%nat | inr n => PrimArray.make 2 n end).
End ArrayDefaultDeclBde.
Crane Extraction "array_default_decl_bde" ArrayDefaultDeclBde.
