(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import String.
Open Scope string_scope.
From Stdlib Require Import Ascii.

From Stdlib Require Import BinInt.
From Stdlib Require Import DecimalString.
Import NilEmpty.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

(** < Core imports **)
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Abstraction.
From Crane.Libraries.ParseALot.Examples.XML.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Lexer.Actions Require Import Impl.
From Crane.Libraries.ParseALot.Lexer Require Import RegexBuilders.
(** /> **)

(** This is where the user defines
   1) sem_ty -- which maps labels to types
   2) apply_sem -- which tries to map tokens to semantic tokens
   3) defLiteral -- of type sem_ty defLabel -- which is the "default" value of that type
   4) label_carries -- a proof that apply_sem does not change the label of the token
 **)
(** User-supplied semantic actions for the XML lexer, mapping tokens to typed values. *)
Module User <: SemUser STT.

  (** Maps each XML token label to its semantic Rocq type (STRING and NAME map to string, others to unit). *)
  Definition sem_ty (l : Label) : Type :=
    match l with
    | STRING => string
    | NAME => string
    | _ => unit
    end.

  (* Need to define a default value for nth *)
  (* defLabel was defined in Literal.v *)
  (** Default semantic value for the default label (SEA_WS). *)
  Definition defLiteral : sem_ty defLabel := tt.

  (** Applies semantic conversion to a (label, raw string) token pair, producing a typed token. *)
  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (STRING, s) => Some (existT _ STRING (string_of_list_ascii s))
    | (NAME, s)   => Some (existT _ NAME (string_of_list_ascii s))
    | (l, s)      => Some (existT _ l tt)
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
(** Instantiation of the semantic lexer functor for XML. *)
Module Import SemLexer := SemLexerFn STT LitLexer User.
Import SemLexer.Impl.

(* And extract; extract_path returns the default path for extraction *)
