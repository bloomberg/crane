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
(** Token labels for the XML literal lexer. *)
Module Export Labels <: Label.

  (** Variant for each XML token kind. *)
  Inductive Label' : Type :=
  | OPEN
  | XMLDeclOpen
  | CLOSE
  | SPECIAL_CLOSE
  | SLASH_CLOSE
  | SLASH
  | EQUALS
  | STRING
  | NAME
  | SEA_WS.

  (** Alias for the label type. *)
  Definition Label : Type := Label'.
  (** Default label used as a fallback value. *)
  Definition defLabel : Label := SEA_WS.
  (** Decidable equality on XML token labels. *)
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End Labels.

(** Here is where the lexer is compiled **)
(* Alphabet is the Sigma object from AsciiSigma *)
(** Instantiation of the lexer functor for the XML literal lexer. *)
Module Export LXR := LexerFn Alphabet Labels.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := PrebuiltRegexes R.

(** Regex matching a single XML whitespace character. *)
Definition S_re := ascii_union ws_carr_chars.
(** Regex matching one or more XML whitespace characters. *)
Definition SEA_WS_re := Plus S_re.
(** Lexer rule matching XML whitespace. *)
Definition SEA_WS_ru := (SEA_WS, SEA_WS_re).

(** Regex matching an XML open-tag bracket ['<']. *)
Definition OPEN_re := string_app "<".
(** Lexer rule matching an XML open-tag bracket. *)
Definition OPEN_ru := (OPEN, OPEN_re).

(** Regex matching an XML declaration open token [<?xml] followed by whitespace. *)
Definition XMLDeclOpen_re := App (string_app "<?xml") S_re.
(** Lexer rule matching an XML declaration open token. *)
Definition XMLDeclOpen_ru := (XMLDeclOpen, XMLDeclOpen_re).

(** Regex matching an XML close-tag bracket ['>']. *)
Definition CLOSE_re := string_app ">".
(** Lexer rule matching an XML close-tag bracket. *)
Definition CLOSE_ru := (CLOSE, CLOSE_re).

(** Regex matching an XML processing-instruction close token ['?>']. *)
Definition SPECIAL_CLOSE_re := string_app "?>".
(** Lexer rule matching an XML processing-instruction close token. *)
Definition SPECIAL_CLOSE_ru := (SPECIAL_CLOSE, SPECIAL_CLOSE_re).

(** Regex matching a self-closing slash-close token ['/>']. *)
Definition SLASH_CLOSE_re := string_app "/>".
(** Lexer rule matching a self-closing slash-close token. *)
Definition SLASH_CLOSE_ru := (SLASH_CLOSE, SLASH_CLOSE_re).

(** Regex matching a forward slash ['/']. *)
Definition SLASH_re := string_app "/".
(** Lexer rule matching a forward slash. *)
Definition SLASH_ru := (SLASH, SLASH_re).

(** Regex matching an equals sign ['=']. *)
Definition EQUALS_re := string_app "=".
(** Lexer rule matching an equals sign. *)
Definition EQUALS_ru := (EQUALS, EQUALS_re).

(* No double quotation mark or opening angle bracket *)
(** Regex for punctuation characters allowed inside a double-quoted XML attribute value. *)
Definition DoubleQuotedStringCharPunc_re := string_union "!#$%&()*+,-.\/:;=>?@[]^_`{¦}~'".
(** Regex for a single character allowed inside a double-quoted XML attribute value. *)
Definition DoubleQuotedStringChar_re := IterUnion [AZ_re; az_re; digit_re; ws_re; DoubleQuotedStringCharPunc_re].
(** Regex for a complete double-quoted XML attribute string. *)
Definition DoubleQuotedString_re := IterApp [quote_re ; Star DoubleQuotedStringChar_re ; quote_re].

(* No double quotation mark, single quotation mark, or opening angle bracket *)
(** Regex for punctuation characters allowed inside a single-quoted XML attribute value. *)
Definition SingleQuotedStringCharPunc_re := string_union "!#$%&()*+,-.\/:;=>?@[]^_`{¦}~".
(** Regex for a single character allowed inside a single-quoted XML attribute value. *)
Definition SingleQuotedStringChar_re := IterUnion [AZ_re; az_re; digit_re; ws_re; SingleQuotedStringCharPunc_re].
(** Regex for a complete single-quoted XML attribute string. *)
Definition SingleQuotedString_re := IterApp [string_app "\'" ; Star SingleQuotedStringChar_re ; string_app "\'"].

(** Regex for an XML attribute string value (double- or single-quoted). *)
Definition STRING_re := Union DoubleQuotedString_re SingleQuotedString_re.
(** Lexer rule matching an XML attribute string value. *)
Definition STRING_ru := (STRING, STRING_re).

(** Regex for the first character of an XML name (colon, lowercase, or uppercase letter). *)
Definition NameStartChar_re := IterUnion [string_app ":" ; az_re ; AZ_re ].
(** Regex for a subsequent character of an XML name (name-start char, dash, underscore, dot, or digit). *)
Definition NameChar_re := IterUnion [ NameStartChar_re ; string_app "-" ; string_app "_" ; string_app "." ; digit_re ].

(** Regex for a complete XML name. *)
Definition NAME_re := App NameStartChar_re (Star NameChar_re).
(** Lexer rule matching an XML name. *)
Definition NAME_ru := (NAME, NAME_re).

(** Compile rules and extract **)
(** Ordered list of all XML lexer rules. *)
Definition rus : list Rule :=
  [ OPEN_ru ; XMLDeclOpen_ru ; CLOSE_ru ; SPECIAL_CLOSE_ru ; SLASH_CLOSE_ru ; SLASH_ru ; EQUALS_ru ; STRING_ru ; NAME_ru ; SEA_WS_ru ].

(** Converts an XML token label to its string name. *)
Definition show_label (l : Label) : string :=
  match l with
  | OPEN => "OPEN"
  | XMLDeclOpen => "XMLDeclOpen"
  | CLOSE => "CLOSE"
  | SPECIAL_CLOSE => "SPECIAL_CLOSE"
  | SLASH_CLOSE => "SLASH_CLOSE"
  | SLASH => "SLASH"
  | EQUALS => "EQUALS"
  | STRING => "STRING"
  | NAME => "NAME"
  | SEA_WS => "SEA_WS"
  end.

(** Converts a raw XML token (label, character list) to a human-readable string. *)
Definition show_token (t : Token) : string :=
  match t with
  | (l, s) => show_label l ++ " | " ++ string_of_list_ascii s
  end.
