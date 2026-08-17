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

(** Token labels for the float sub-lexer used to split float strings into components. *)
Module Export Labels <: Label.

  (** Label variants for integer part, decimal point, decimal digits, and exponent marker. *)
  Inductive Label' : Type :=
  | INT
  | PNT
  | DEC
  | EXP.

  Definition Label := Label'.
  Definition defLabel : Label := INT.
  (** Decidable equality on float sub-lexer labels. *)
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. decide equality. Qed.

End Labels.

(** Instantiation of the lexer functor for the float sub-lexer. *)
Module Export LXR := LexerFn Alphabet Labels.
Module Import PBR := PrebuiltRegexes R.

(** Build Rules **)
(** Lexer rule matching a signed integer. *)
Definition ru_int := (INT, int_re).
(** Lexer rule matching a decimal point. *)
Definition ru_dec_point := (PNT, string_app ".").
(** Lexer rule matching the decimal digits after the point. *)
Definition ru_dec := (DEC, nat_lz_re).
(** Lexer rule matching an exponent marker (e, E, e+, or E+). *)
Definition ru_Ee_delim :=
  (EXP, IterUnion [(string_app "e");(string_app "E");(string_app "e+");(string_app "E+")]).

(** Ordered list of lexer rules for the float sub-lexer. *)
Definition rules : list Rule := [ru_int;ru_dec_point;ru_dec;ru_Ee_delim].

(** Utilities for splitting a float string into integer, decimal, and exponent parts. *)
Module Splitter.

  (** Splits a float string into (integer part, decimal digits, exponent) using the float sub-lexer. *)
  Definition Split_float_str (z : String) : option (String * String * String) :=
    match lex rules z with
    | ([(INT,i)], []) => Some (i, [], [])
    | ([(INT,i);(PNT,_);(DEC,d)], []) => Some (i, d, [])
    | ([(INT,i);(EXP,_);(INT,e)], []) => Some (i, [], e)
    | ([(INT,i);(PNT,_);(DEC,d);(EXP,_);(INT,e)], []) => Some (i, d, e)
    | _ => None
    end.

End Splitter.

