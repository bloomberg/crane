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
(** Token labels for the PPM image format literal lexer. *)
Module Export Labels <: Label.

  (** Variant for each PPM token kind: magic number, natural number, or whitespace. *)
  Inductive Label' : Type :=
  | P3
  | NAT
  | WS.

  (** Alias for the label type. *)
  Definition Label : Type := Label'.
  (** Default label used as a fallback value. *)
  Definition defLabel : Label := WS.
  (** Decidable equality on PPM token labels. *)
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End Labels.

(** Here is where the lexer is compiled **)
(* Alphabet is the Sigma object from AsciiSigma *)
(** Instantiation of the lexer functor for the PPM literal lexer. *)
Module Export LXR := LexerFn Alphabet Labels.
(* Loads in regex library from _Utils.Lexer; Object R comes from LXR *)
Module Import PBR := PrebuiltRegexes R.

(** keywords **)
(** Lexer rule matching the PPM magic number ["P3"]. *)
Definition ru_p3 := (P3, string_app "P3").

(** Numbers **)
(** Lexer rule matching a natural number. *)
Definition ru_nat := (NAT, nat_re).

(** White Space **)
(* [ \t\n\r] *)
(* ws_carr_re includes \r; ws_re does not *)
(** Lexer rule matching PPM whitespace (space, tab, newline, carriage return). *)
Definition ru_ws : Rule := (WS, ws_carr_re).

(** Compile rules and extract **)
(** Ordered list of all PPM lexer rules. *)
Definition rus : list Rule :=
  [ru_p3 ; ru_nat; ru_ws].
