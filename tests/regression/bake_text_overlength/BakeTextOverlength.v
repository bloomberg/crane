(** Found by Ephyra round 23 (there: a baked [PrimString.make] of
    [max_length + 7] bytes). Here 70 strings of 1000 bytes, one of which
    falls across a 65535-byte cut.
    Expected: compiles, [total = 70000].
    Fixed: the readable bake image (one node per row) wrote every baked
    string's bytes into one text array initialised by adjacent string
    literals, so once they totalled more than 65536 bytes the concatenated
    literal was over clang's limit ("string literal of length 70000
    exceeds maximum length 65536 that C++ compilers are required to
    support", [-Woverlength-strings], an error under [-Werror]). The text
    is now a table of character arrays of at most 65535 bytes each
    ([crane::bake::image::text], [std::string_view] chunks), a string split
    across two where it falls on a cut, and the reader reads a string
    across chunks. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimString.
Import ListNotations.

Module BakeTextOverlength.

Definition n2i (n : nat) : PrimInt63.int := Uint63.of_Z (Z.of_nat n).

Definition words : list PrimString.string :=
  map (fun k => PrimString.make (n2i 1000) (n2i (48 + k))) (seq 0 70).

Definition total : nat :=
  fold_left (fun a s => a + Z.to_nat (Uint63.to_Z (PrimString.length s))) words 0.

End BakeTextOverlength.

Crane Bake BakeTextOverlength.words.
Crane Extraction "bake_text_overlength" BakeTextOverlength.
