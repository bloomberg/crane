(** Found by Ephyra round 23. [Crane Bake] of a list of primitive strings
    holding trigraph sequences ([??=], [??/], [??)], [???]). A variant of
    [string_literal_trigraph] (round 19, fixed for string literals in
    generated code).
    Expected: compiles, [total = 24].
    Fixed: the readable bake image (one node per row) wrote the baked
    strings' bytes into its text array of string literals unescaped,
    [..._text[] = "??" "a" "??=";], and clang's [-Wtrigraphs] ("trigraph
    ignored") is an error under the suite's [-Werror]. The image writer
    ([crane::bake::detail::quoted]) now writes a [?] after a [?] as [\?],
    as Crane's printer does ([escape_cpp_string]), in the text and in the
    rows' comments. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimString.
Import ListNotations.
Local Open Scope pstring_scope.

Module BakeTextTrigraph.

Definition words : list PrimString.string :=
  ["??="; "a"; "??"; "??/"; "???"; "?""?"; "??)"; "a\b"; "?"; "?="].

Definition total : nat :=
  fold_left (fun a s => a + Z.to_nat (Uint63.to_Z (PrimString.length s))) words 0.

End BakeTextTrigraph.

Crane Bake BakeTextTrigraph.words.
Crane Extraction "bake_text_trigraph" BakeTextTrigraph.
