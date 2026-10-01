From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.AsciiChar.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import Ascii String.
Open Scope string_scope.

(** With [Mapping.AsciiChar], a character is a C++ [char]: identifier
    comparison compares bytes instead of building a binary natural per
    character.  The constructor packs bits and a match unpacks them, so
    code that looks inside a character still works. *)
Module AsciiAsChar.

  Fixpoint cmp (a b : string) : comparison :=
    match a, b with
    | EmptyString, EmptyString => Eq
    | EmptyString, _ => Lt
    | _, EmptyString => Gt
    | String x a', String y b' =>
        match Ascii.compare x y with Eq => cmp a' b' | c => c end
    end.

  Fixpoint same (a b : string) : bool :=
    match a, b with
    | EmptyString, EmptyString => true
    | String x a', String y b' => Ascii.eqb x y && same a' b'
    | _, _ => false
    end.

  (** Looks inside a character: its low bit. *)
  Definition odd_code (c : ascii) : bool :=
    match c with Ascii b0 _ _ _ _ _ _ _ => b0 end.

  Definition decide (a b : ascii) : bool := if ascii_dec a b then true else false.

  Definition check (_ : unit) : bool :=
    match cmp "load" "loop", cmp "store" "store", cmp "zext" "add" with
    | Lt, Eq, Gt =>
        same "phi" "phi" && negb (same "phi" "phj")
        && odd_code "a" && negb (odd_code "b")
        && decide "x" "x" && negb (decide "x" "y")
        && Nat.eqb (nat_of_ascii "A") 65
    | _, _, _ => false
    end.

End AsciiAsChar.

Crane Extraction "ascii_as_char" AsciiAsChar.
