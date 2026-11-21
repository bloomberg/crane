(** Found by Ephyra (round 19). [Crane Bake] under [Set Crane BoxedFields]
    of a constant whose constructor has a boxed field ([inl [4; 5]] of
    [sum (list nat) nat]: the [list] field is a [crane::field_box]).  The
    constant is baked and [total = 2].

    Fixed: the bake driver did not compile ("crane::bake: no way to write a
    value of this type" for [crane::field_box<List<unsigned long long>>]).
    The image writer and reader saw through [std::shared_ptr],
    [crane::shared_box] and [crane::rc] but not [crane::field_box]; all four
    are now one [handle] trait in crane_bake.h. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane BoxedFields.

Module BakeBoxedField.

Definition choice : sum (list nat) nat := inl [4; 5].

Definition total : nat := match choice with inl l => List.length l | inr n => n end.

End BakeBoxedField.

Crane Bake BakeBoxedField.choice.

Crane Extraction "bake_boxed_field" BakeBoxedField.
