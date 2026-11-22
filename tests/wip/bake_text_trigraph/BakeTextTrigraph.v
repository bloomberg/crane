(** Found by Ephyra round 23. [Crane Bake] of a list of primitive strings
    one of which is the trigraph sequence [??=]. A variant of
    [string_literal_trigraph] (round 19, fixed for string literals in
    generated code): the readable bake image (one node per row) writes
    the baked strings' bytes into a text array of string literals (the
    image before it packed them into words), unescaped:
    [crane_baked_words_..._text[] = "??" "a" "??=";].
    Expected: compiles, [total = 6] (lengths 3 + 1 + 2).
    Actual: clang's [-Wtrigraphs] ("trigraph ignored") is an error under
    the suite's [-Werror]. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimString.
Import ListNotations.
Local Open Scope pstring_scope.

Module BakeTextTrigraph.

Definition words : list PrimString.string := ["??="; "a"; "??"].

Definition total : nat :=
  fold_left (fun a s => a + Z.to_nat (Uint63.to_Z (PrimString.length s))) words 0.

End BakeTextTrigraph.

Crane Bake BakeTextTrigraph.words.
Crane Extraction "bake_text_trigraph" BakeTextTrigraph.
