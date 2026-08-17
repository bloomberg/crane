(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import String.
Open Scope string_scope.
From Stdlib Require Import Ascii.

From Stdlib Require Import BinInt BinNat.
From Stdlib Require Import DecimalString.
Import NilEmpty.
(** < Float stuff; doesn't extract **)
(*Require Import PrimFloat.
Require Import Int63.

Require Extraction.
Require ExtrOCamlInt63.
Require ExtrOCamlFloats.

From Verbatim Require FloatLexer.
Import FloatLexer.Splitter.
 *)
(**/> **)

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

(** < Core imports **)
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Abstraction.
From Crane.Libraries.ParseALot.Examples.Newick.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Lexer.Actions Require Import Impl.
From Crane.Libraries.ParseALot.Lexer Require Import RegexBuilders.
(** /> **)

(** This is where the user defines
   1) sem_ty -- which maps labels to types
   2) apply_sem -- which tries to map tokens to semantic tokens
   3) defLiteral -- of type sem_ty defLabel -- which is the "default" value of that type
   4) label_carries -- a proof that apply_sem does not change the label of the token
 **)
(** User-supplied semantic actions for the Newick lexer, mapping tokens to typed values. *)
Module User <: SemUser STT.

  (** Maps each Newick token label to its semantic Rocq type (NAT maps to N, all others to unit). *)
  Definition sem_ty (l : Label) : Type :=
    match l with
    | NAT => N
    | _ => unit
    end.

  (* Need to define a default value for nth *)
  (* defLabel was defined in Literal.v *)
  (** Default semantic value for the default label (WS). *)
  Definition defLiteral : sem_ty defLabel := tt.

  (** Parses a character list as an unsigned natural number N. *)
  Definition N_of_String (s : String) : option N :=
    match uint_of_string (string_of_list_ascii s) with
    | Some ui => Some (N.of_uint ui)
    | None => None
    end.

  (** Applies semantic conversion to a (label, raw string) token pair, producing a typed token. *)
  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (NAT, s) =>
      match N_of_String s with
      | Some n => Some (existT _ NAT n)
      | None => None
      end
    | (l, _) => Some (existT _ l tt)
    end.

  (** Proof that [apply_sem] preserves the label of each token. *)
  Lemma label_carries : forall l l' s t,
      apply_sem (l, s) = Some (existT sem_ty l' t)
      -> l = l'.
  Proof.
    intros. destruct l; destruct l'; auto; sis; repeat dm; repeat inj_all; discriminate.
  Qed.

End User.

(* Here we use the literal lexer and the user parameters to create the semantic lexer *)
(** Instantiation of the semantic lexer functor for Newick. *)
Module Import SemLexer := SemLexerFn STT LitLexer User.
Import SemLexer.Impl.

(* And extract; extract_path returns the default path for extraction *)
