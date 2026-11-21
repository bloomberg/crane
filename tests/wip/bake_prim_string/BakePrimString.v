(** Found by Ephyra (round 19). [Crane Bake] of closed constants whose type
    holds Rocq's primitive [string], which [Mapping.Std] maps to
    [std::string] with a typed mapping.

    Expected: both constants are baked (docs/Crane-Bake.md: an opaque type
    is data when it is mapped or primitive, and the image format writes a
    [std::string] as its length and bytes), and the program prints
    [abcd] and [ab].

    Actual: the bake check refuses them: "Crane Bake: BakePrimString.greeting
    is a value of the opaque type Corelib.Strings.PrimString.string, which has
    no definition to bake". [Bake.check] accepts an opaque constant only when
    its body is [Primitive] or it has a legacy custom extraction
    ([Table.is_custom]); a typed [TypeMapping] is not consulted. Inside a
    constructor field the message also repeats ", in a constructor field,". *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.

Module BakePrimString.

Definition greeting : PrimString.string := PrimString.cat "ab"%pstring "cd"%pstring.

Definition words : list PrimString.string := ["ab"%pstring; "cde"%pstring].

Definition first_word : PrimString.string := hd ""%pstring words.

End BakePrimString.

Crane Bake BakePrimString.greeting BakePrimString.words.

Crane Extraction "bake_prim_string" BakePrimString.
