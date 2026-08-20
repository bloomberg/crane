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
(** Token labels for the CSV literal lexer (RFC 4180). *)
Module Export Labels <: Label.

  (** Variant for each CSV token kind. *)
  Inductive Label' : Type :=
  | FIELD    (* an unquoted field: printable chars except comma and quote *)
  | QUOTED   (* a double-quoted field, with "" as an escaped quote *)
  | COMMA    (* the field separator ',' *)
  | NEWLINE. (* a record separator: LF or CRLF *)

  (** Alias for the label type. *)
  Definition Label : Type := Label'.
  (** Default label used as a fallback value. *)
  Definition defLabel : Label := FIELD.
  (** Decidable equality on CSV token labels. *)
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End Labels.

(** Here is where the lexer is compiled **)
(* Alphabet is the Sigma object from AsciiSigma *)
(** Instantiation of the lexer functor for the CSV literal lexer. *)
Module Export LXR := LexerFn Alphabet Labels.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := PrebuiltRegexes R.


(** Record separator: an optional carriage return followed by a line feed
    (so both Unix "\n" and Windows "\r\n" endings are accepted). *)
Definition NEWLINE_re := App (Optional (char_of_nat 13)) (char_of_nat 10).
(** Lexer rule matching a CSV record separator. *)
Definition NEWLINE_ru := (NEWLINE, NEWLINE_re).

(** Field separator ','. *)
Definition COMMA_re := string_app ",".
(** Lexer rule matching a CSV field separator. *)
Definition COMMA_ru := (COMMA, COMMA_re).


(** Unquoted-field content **)
(* Punctuation allowed in an unquoted field: every char in [punc_re] except the
   comma (a separator), plus the backslash (so e.g. Windows paths lex). The
   double quote is deliberately excluded -- a field containing a quote must be
   quoted. *)
Definition FieldPunc_re := string_union "!#$%&()*+-.\/:;<=>?@[]^_`{¦}~'".
(** Regex matching a single character allowed in an unquoted field
    (letters, digits, spaces/tabs, and the punctuation above). *)
Definition FieldChar_re :=
  IterUnion [AZ_re; az_re; digit_re; ascii_union [tab_ascii; space_ascii]; FieldPunc_re].
(** Regex matching a non-empty unquoted field; empty fields are handled by the
    grammar (see [Parser/CSV.v]). *)
Definition FIELD_re := Plus FieldChar_re.
(** Lexer rule matching an unquoted CSV field. *)
Definition FIELD_ru := (FIELD, FIELD_re).


(** Quoted-field content **)
(* Inside a quoted field, everything is allowed except a bare double quote:
   letters, digits, whitespace (incl. CR/LF, so quoted fields may span lines),
   the full punctuation set (comma included), and the backslash. *)
Definition QuotedPunc_re := string_union "!#$%&()*+,-.\/:;<=>?@[]^_`{¦}~'".
(** Regex matching a single ordinary character inside a quoted field. *)
Definition QuotedChar_re :=
  IterUnion [AZ_re; az_re; digit_re; ws_carr_re; QuotedPunc_re].
(** Regex matching an escaped double quote (two consecutive quote chars, which
    RFC 4180 uses to denote a single literal quote inside a quoted field). *)
Definition EscQuote_re := App quote_re quote_re.
(** Regex matching a complete double-quoted CSV field. *)
Definition QUOTED_re := IterApp [quote_re; Star (Union QuotedChar_re EscQuote_re); quote_re].
(** Lexer rule matching a quoted CSV field. *)
Definition QUOTED_ru := (QUOTED, QUOTED_re).


(** Compile rules and extract **)
(* The four rules are first-character disjoint (NEWLINE starts with CR or LF,
   COMMA with a comma, QUOTED with a double quote, FIELD with any other
   printable char), so the maximal-munch rule order below is not load-bearing. *)
(** Ordered list of all CSV lexer rules. *)
Definition rus : list Rule :=
  [ NEWLINE_ru ; COMMA_ru ; QUOTED_ru ; FIELD_ru ].

(** Converts a CSV token label to its string name. *)
Definition show_label (l : Label) : string :=
  match l with
  | FIELD   => "FIELD"
  | QUOTED  => "QUOTED"
  | COMMA   => "COMMA"
  | NEWLINE => "NEWLINE"
  end.

(** Converts a raw CSV token (label, character list) to a human-readable string. *)
Definition show_token (t : Token) : string :=
  match t with
  | (l, s) => show_label l ++ " | " ++ string_of_list_ascii s
  end.
