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
(** Token labels for the Newick format literal lexer. *)
Module Export NewickLabels <: Label.

  (** Variant for each Newick token kind. *)
  Inductive Label' : Type :=
  | NAT
  | COLON
  | COMMA
  | DECIMAL_POINT
  | L_PAREN
  | R_PAREN
  | SEMICOLON
  | WS.

  (** Alias for the label type. *)
  Definition Label : Type := Label'.
  (** Default label used as a fallback value. *)
  Definition defLabel : Label := WS.
  (** Decidable equality on Newick token labels. *)
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End NewickLabels.

(** Here is where the lexer is compiled **)
(* Alphabet is the Sigma object from AsciiSigma *)
(** Instantiation of the lexer functor for the Newick literal lexer. *)
Module Export LXR := LexerFn Alphabet NewickLabels.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := PrebuiltRegexes R.

(** Lexer rule matching a natural number (one or more digits). *)
Definition ru_nat := (NAT, App digit_re (Star digit_re)).
(** Lexer rule matching a colon [':']. *)
Definition ru_colon := (COLON, string_app ":").
(** Lexer rule matching a comma [',']. *)
Definition ru_comma := (COMMA, string_app ",").
(** Lexer rule matching a decimal point ['.']. *)
Definition ru_decimal := (DECIMAL_POINT, string_app ".").
(** Lexer rule matching a left parenthesis ['(']. *)
Definition ru_lparen := (L_PAREN, string_app "(").
(** Lexer rule matching a right parenthesis [')']. *)
Definition ru_rparen := (R_PAREN, string_app ")").
(** Lexer rule matching a semicolon [';']. *)
Definition ru_semi := (SEMICOLON, string_app ";").
(** Lexer rule matching Newick whitespace (space, tab, newline, carriage return). *)
Definition ru_ws : Rule := (WS, ws_carr_re).

(** Compile rules and extract **)
(** Ordered list of all Newick lexer rules. *)
Definition rus : list Rule :=
  [ ru_nat ; ru_colon ; ru_comma ; ru_decimal ; ru_lparen ; ru_rparen ; ru_semi ; ru_ws ].
