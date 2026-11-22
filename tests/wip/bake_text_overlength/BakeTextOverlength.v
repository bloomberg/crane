(** Found by Ephyra round 23 (there: a baked [PrimString.make] of
    [max_length + 7] bytes). The readable bake image (one node per row)
    writes every baked string's bytes into one text array initialised by
    adjacent string literals, [crane_baked_..._text[] = "..." "..." ...;]
    (the image before it packed the bytes into words). Once the baked
    strings total more than 65536 bytes, the concatenated literal is over
    clang's limit: here 70 strings of 1000 bytes.
    Expected: compiles, [total = 70000].
    Actual: "string literal of length 70000 exceeds maximum length 65536
    that C++ compilers are required to support", an error under the
    suite's [-Werror] ([-Woverlength-strings]). *)
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
