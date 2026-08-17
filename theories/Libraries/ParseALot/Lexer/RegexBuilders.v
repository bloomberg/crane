(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import String.
Open Scope string_scope.
From Stdlib Require Import Ascii.

From Crane.Libraries.ParseALot.Utils Require Import AsciiSigma.

(** Functor providing combinators for building regexes from characters and strings. *)
Module RegexBuilders (Import R : Regex.T).

  Import Ty.
  Export Helpers.

  (** Regex matching the single ASCII character with code [n]. *)
  Definition char_of_nat (n : nat) : regex :=
    Char (ascii2Sigma (ascii_of_nat n)).

  (** Regex matching any one character from the list [bs]. *)
  Definition ascii_union (bs : list ascii) : regex :=
    IterUnion (map (fun x => Char (ascii2Sigma x)) bs).

  (** Regex matching any one character from the string [bs]. *)
  Definition string_union (bs : string) : regex :=
    ascii_union (list_ascii_of_string bs).

  (** Regex matching the sequence of characters in [bs] in order. *)
  Definition ascii_app (bs : list ascii) : regex :=
    IterApp (map (fun x => Char (ascii2Sigma x)) bs).

  (** Regex matching the exact string [bs] as a concatenation of character regexes. *)
  Definition string_app (bs : string) : regex :=
    ascii_app (list_ascii_of_string bs).


End RegexBuilders.

(** Functor providing commonly used prebuilt regexes (whitespace, numbers, strings). *)
Module PrebuiltRegexes (Import R : Regex.T).

  Module Export Builders := RegexBuilders R.

  (*** Whitespace ***)
  (** Definitions of whitespace characters and their regexes. *)
  Module Export Whitespace.

    Definition tab_ascii : ascii := ascii_of_nat 9.              (* \t *)
    Definition linebreak_ascii : ascii := ascii_of_nat 10.       (* \n *)
    Definition carriage_return_ascii : ascii := ascii_of_nat 13. (* \r *)
    Definition space_ascii : ascii := ascii_of_nat 32.

    (* Includes tab \t, newline \n, and space *)
    (** List of whitespace characters: tab, newline, and space. *)
    Definition ws_chars : list ascii :=
      [tab_ascii; linebreak_ascii; space_ascii].
    (** Regex matching one or more whitespace characters (tab, newline, space). *)
    Definition ws_re : regex := Plus (ascii_union ws_chars).

    (* Includes tab \t, newline \n, carriage return \r, and space *)
    (** List of whitespace characters including carriage return. *)
    Definition ws_carr_chars : list ascii :=
      [tab_ascii; linebreak_ascii; carriage_return_ascii; space_ascii].
    (** Regex matching one or more whitespace characters including carriage return. *)
    Definition ws_carr_re : regex := Plus (ascii_union ws_carr_chars).

  End Whitespace.


  (*** Numbers ***)
  (** Definitions of numeric regexes (digits, naturals, integers, decimals). *)
  Module Export Numbers.

    (** Regex matching a single decimal digit 0-9. *)
    Definition digit_re := string_union "0123456789".
    (** Regex matching a single non-zero decimal digit 1-9. *)
    Definition nz_digit_re := string_union "123456789".
    (** Regex matching the literal character '0'. *)
    Definition zero_re := string_app "0".

    (** * * Leading zeros denoted by lz * **)


    (** Positives exclude 0 **)
    (** Regex for positive integers allowing leading zeros. *)
    Definition pos_lz_re := IterApp [(Star digit_re); nz_digit_re; (Star digit_re)].
    (** Regex for positive integers without leading zeros. *)
    Definition pos_re := App nz_digit_re (Star digit_re).


    (** Naturals include 0 **)
    (** Regex for natural numbers (including 0) allowing leading zeros. *)
    Definition nat_lz_re := Plus digit_re.
    (** Regex for natural numbers (including 0) without leading zeros. *)
    Definition nat_re := Union zero_re pos_re.


    (** Integers; Be sure to handle -0 appropriately for your language **)
    (** Regex for integers allowing leading zeros, with optional minus sign. *)
    Definition int_lz_re := App (Optional (string_app "-")) nat_lz_re.
    (** Regex for integers without leading zeros, with optional minus sign. *)
    Definition int_re := App (Optional (string_app "-")) nat_re.
    (** Regex for integers excluding negative zero, allowing leading zeros. *)
    Definition int_no_neg0_lz_re := Union zero_re (App (Optional (string_app "-")) pos_lz_re).
    (** Regex for integers excluding negative zero, without leading zeros. *)
    Definition int_no_neg0_re := Union zero_re (App (Optional (string_app "-")) pos_re).


    (** Decimal numbers;
        Note: One or both of the integer/decimal part may be optional
        for your language **)
    (** Regex for the fractional part of a decimal number (dot followed by digits). *)
    Definition dec_part_re := App (string_app ".") nat_lz_re.

    (* Optional decimal part *)
    (** Regex for a decimal number with optional fractional part, allowing leading zeros. *)
    Definition dec_lz_re := App int_lz_re (Optional dec_part_re).
    (** Regex for a decimal number with optional fractional part, no leading zeros. *)
    Definition dec_re := App int_re (Optional dec_part_re).
    (** Regex for a decimal number excluding negative zero, optional fraction, leading zeros allowed. *)
    Definition dec_no_neg0_lz_re := App int_no_neg0_lz_re (Optional dec_part_re).
    (** Regex for a decimal number excluding negative zero, optional fraction, no leading zeros. *)
    Definition dec_no_neg0_re := App int_no_neg0_re (Optional dec_part_re).

    (* Required decimal part *)
    (** Regex for a decimal number with a required fractional part, leading zeros allowed. *)
    Definition proper_dec_lz_re := App int_lz_re dec_part_re.
    (** Regex for a decimal number with a required fractional part, no leading zeros. *)
    Definition proper_dec_re := App int_re dec_part_re.
    (** Regex for a decimal number excluding negative zero, required fraction, leading zeros allowed. *)
    Definition proper_dec_no_neg0_lz_re := App int_no_neg0_lz_re dec_part_re.
    (** Regex for a decimal number excluding negative zero, required fraction, no leading zeros. *)
    Definition proper_dec_no_neg0_re := App int_no_neg0_re dec_part_re.

    (* Optional integer part, required decimal part *)
    (** * * For later * **)
  End Numbers.


  (*** Strings ***)

  (** Definitions of character-class and string regexes. *)
  Module Export StringsRegex.

    (** Regex matching any uppercase ASCII letter A-Z. *)
    Definition AZ_re := string_union "ABCDEFGHIJKLMNOPQRSTUVWXYZ".
    (** Regex matching any lowercase ASCII letter a-z. *)
    Definition az_re := string_union "abcdefghijklmnopqrstuvwxyz".
    (* Does not include white space, double quote, backslash, or ascii 0-31 *)
    (** Regex matching common punctuation characters (excluding whitespace, double quote, backslash). *)
    Definition punc_re := string_union "!#$%&()*+,-./:;<=>?@[]^_`{¦}~'".
    (** Regex matching the double-quote character. *)
    Definition quote_re := char_of_nat 34.
    (** Regex matching an escaped double-quote sequence. *)
    Definition esc_quote_re := App (string_app "\") quote_re.
    (** Regex matching an escaped backslash sequence. *)
    Definition esc_bslash_re := string_app "\\".
    (** * * Your language may vary in what is a character, *)
    (** *   what is escaped and how, and what delimits a string. * *)
    (** Regex matching a single valid string character (letters, digits, whitespace, punctuation, escapes). *)
    Definition char_re :=
      IterUnion [AZ_re; az_re; digit_re; ws_re; punc_re; esc_quote_re; esc_bslash_re].
    (** Regex matching a double-quoted string of zero or more valid characters. *)
    Definition string_re := IterApp [quote_re; (Star char_re); quote_re].

  End StringsRegex.

End PrebuiltRegexes.
