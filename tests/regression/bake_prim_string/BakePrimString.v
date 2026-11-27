(** Found by Ephyra (round 19). [Crane Bake] of closed constants whose type
    holds Rocq's primitive [string], which [Mapping.Std] maps to
    [std::string] with a typed mapping.  Both constants are baked and the
    program prints [abcd] and [ab].

    Fixed: the bake check refused them ("is a value of the opaque type
    Corelib.Strings.PrimString.string, which has no definition to bake").
    [Bake.check] ran before any extraction had discovered the typed
    mappings, so [Table.is_custom] saw no [TypeMapping] instance; it now
    discovers them first, and accepts a primitive type.  Inside a
    constructor field the refusal also repeated ", in a constructor field,"
    once per level. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
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
