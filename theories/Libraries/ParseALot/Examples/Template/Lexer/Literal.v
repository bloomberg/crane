(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import Ascii.
From Stdlib Require Import String.
Open Scope string_scope.

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

(** < Core imports **)
From Crane.Libraries.ParseALot.Lexer Require Import State. (* Label lives here, maybe it shouldn't. *)
From Crane.Libraries.ParseALot.Utils Require Import AsciiSigma.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import ConcreteLexer.
From Crane.Libraries.ParseALot.Lexer Require Import RegexBuilders.
(** /> **)

(** Label type defined here **)
(** Token labels for the template literal lexer (mirrors the JSON label set). *)
Module Export Labels <: Label.

  (** Variant for each template token kind. *)
  Inductive Label' : Type :=
  | INT
  | FLOAT
  | STRING
  | TRUE
  | FALSE
  | NULL
  | COLON
  | COMMA
  | LEFT_BRACKET
  | RIGHT_BRACKET
  | LEFT_BRACE
  | RIGHT_BRACE
  | WS.

  (** Alias for the label type. *)
  Definition Label : Type := Label'.
  (** Default label used as a fallback value. *)
  Definition defLabel : Label := WS.
  (** Decidable equality on template token labels. *)
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End Labels.

(** Here is where the lexer is compiled **)
(* Alphabet is the Sigma object from AsciiSigma *)
(** Instantiation of the lexer functor for the template literal lexer. *)
Module Export LXR := LexerFn Alphabet Labels.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := PrebuiltRegexes R.


(** White Space **)
(* [ \t\n\r] *)
(* ws_carr_re includes \r; ws_re does not *)
(** Lexer rule matching whitespace (space, tab, newline, carriage return). *)
Definition ru_ws : Rule := (WS, ws_carr_re).


(** Numbers **)
(** Regex for the exponent part of a number (e/E followed by optional sign and digits). *)
Definition exp_part_re := IterApp [(string_union "Ee"); (Optional (string_union "+-")); nat_re].
(** Regex for a floating-point number (decimal with optional exponent). *)
Definition float_re := App dec_re (Optional exp_part_re).

(** Lexer rule matching a floating-point number. *)
Definition ru_float := (FLOAT, float_re).
(** Lexer rule matching an integer. *)
Definition ru_int := (INT, int_re).


(** STRING **)
(** Lexer rule matching a double-quoted string literal. *)
Definition ru_string := (STRING, string_re).


(** keywords **)
(** Lexer rule matching the keyword [true]. *)
Definition ru_true := (TRUE, string_app "true").
(** Lexer rule matching the keyword [false]. *)
Definition ru_false := (FALSE, string_app "false").
(** Lexer rule matching the keyword [null]. *)
Definition ru_null := (NULL, string_app "null").


(** brack, brace, colon, comma **)
(** Lexer rule matching a colon [':']. *)
Definition ru_colon := (COLON, string_app ":").
(** Lexer rule matching a comma [',']. *)
Definition ru_comma := (COMMA, string_app ",").
(** Lexer rule matching a left bracket ['[']. *)
Definition ru_lbrack := (LEFT_BRACKET, string_app "[").
(** Lexer rule matching a right bracket [']']. *)
Definition ru_rbrack := (RIGHT_BRACKET, string_app "]").
(** Lexer rule matching a left brace ['{']. *)
Definition ru_lbrace := (LEFT_BRACE, string_app "{").
(** Lexer rule matching a right brace ['}']. *)
Definition ru_rbrace := (RIGHT_BRACE, string_app "}").


(** Compile rules and extract **)
(** Ordered list of all template lexer rules. *)
Definition rus : list Rule :=
  [ru_ws;ru_int;ru_float;ru_string;ru_true;ru_false;ru_null;
  ru_colon;ru_comma;ru_lbrack;ru_rbrack;ru_lbrace;ru_rbrace].
