(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extracts [Ascii.ascii] to C++ [char], as OCaml's [ExtrOcamlString]
    extracts it to OCaml's [char].

    An [ascii] is otherwise a record of eight [bool]s, and comparing two of
    them goes through [N_of_ascii]: a list of their bits, then a binary
    natural built from it.  Code that compares identifiers character by
    character pays that for every character.  Mapped, a character is one
    byte and comparing two is one instruction.

    The constructor packs its eight bits, least significant first; a match
    unpacks them.  [compare], [eqb] and [ascii_dec] compare bytes.
    [compare]'s result is the [comparison] enum, whose constructors are
    numbered in declaration order ([Eq], [Lt], [Gt]); [%ret] names the enum
    whatever the generator calls it. *)
From Crane Require Extraction.
From Stdlib Require Import Ascii.

Crane Extract Inductive ascii =>
  "char"
  [ "static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0))" ]
  "const bool %b0a0 = (static_cast<unsigned char>(%scrut) & 1) != 0; const bool %b0a1 = (static_cast<unsigned char>(%scrut) & 2) != 0; const bool %b0a2 = (static_cast<unsigned char>(%scrut) & 4) != 0; const bool %b0a3 = (static_cast<unsigned char>(%scrut) & 8) != 0; const bool %b0a4 = (static_cast<unsigned char>(%scrut) & 16) != 0; const bool %b0a5 = (static_cast<unsigned char>(%scrut) & 32) != 0; const bool %b0a6 = (static_cast<unsigned char>(%scrut) & 64) != 0; const bool %b0a7 = (static_cast<unsigned char>(%scrut) & 128) != 0; %br0".

Crane TriviallyCopyable ascii.

Crane Extract Inlined Constant Ascii.compare =>
  "[](char _x, char _y) { return static_cast<%ret>(_x == _y ? 0 : (static_cast<unsigned char>(_x) < static_cast<unsigned char>(_y) ? 1 : 2)); }(%a0, %a1)".
Crane Extract Inlined Constant Ascii.eqb => "std::equal_to<char>{}(%a0, %a1)" From "functional".
Crane Extract Inlined Constant Ascii.ascii_dec => "std::equal_to<char>{}(%a0, %a1)" From "functional".
