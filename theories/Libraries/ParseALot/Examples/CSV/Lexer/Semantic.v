(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import String.
Open Scope string_scope.
From Stdlib Require Import Ascii.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

(** < Core imports **)
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Abstraction.
From Crane.Libraries.ParseALot.Examples.CSV.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Lexer.Actions Require Import Impl.
From Crane.Libraries.ParseALot.Lexer Require Import RegexBuilders.
(** /> **)

(** This is where the user defines
   1) sem_ty -- which maps labels to types
   2) apply_sem -- which tries to map tokens to semantic tokens
   3) defLiteral -- of type sem_ty defLabel -- which is the "default" value of that type
   4) label_carries -- a proof that apply_sem does not change the label of the token
 **)
(** User-supplied semantic actions for the CSV lexer, mapping tokens to typed values. *)
Module User <: SemUser STT.

  (** Maps each CSV token label to its semantic Rocq type. *)
  Definition sem_ty (l : Label) : Type :=
    match l with
    | FIELD   => string
    | QUOTED  => string
    | COMMA   => unit
    | NEWLINE => unit
    end.

  (* Need to define a default value for nth *)
  (* defLabel was defined in Literal.v (= FIELD) *)
  (** Default semantic value for the default label (FIELD). *)
  Definition defLiteral : sem_ty defLabel := ""%string.

  (** The double-quote character (ASCII 34). *)
  Definition dquote : ascii := ascii_of_nat 34.

  (* Collapse every doubled quote (two adjacent quote chars become one) in the
     already-stripped interior of a quoted field. Written to recurse only on
     strict structural subterms so the guardedness checker accepts it. *)
  (** Collapses each escaped doubled quote into a single quote character. *)
  Fixpoint collapse_dq (cs : list ascii) : list ascii :=
    match cs with
    | [] => []
    | c1 :: l =>
        if Ascii.eqb c1 dquote then
          match l with
          | c2 :: rest =>
              if Ascii.eqb c2 dquote
              then c1 :: collapse_dq rest   (* a "" pair: emit one quote, skip both *)
              else c1 :: collapse_dq l      (* lone quote (malformed): emit and continue *)
          | [] => [c1]
          end
        else c1 :: collapse_dq l
    end.

  (* The raw QUOTED lexeme always has the shape [dquote :: interior ++ [dquote]]
     (guaranteed by [QUOTED_re]); strip the outer quotes, then collapse escapes. *)
  (** Turns a raw quoted lexeme into its logical string value: outer quotes
      removed, each doubled quote collapsed to one. *)
  Definition csv_unquote (z : String) : string :=
    match z with
    | [] => ""
    | _ :: t => string_of_list_ascii (collapse_dq (removelast t))
    end.

  (** Applies semantic conversion to a (label, raw string) token pair, producing a typed token. *)
  Definition apply_sem (pr : Label * String) : option {l : Label & sem_ty l} :=
    match pr with
    | (FIELD, z)  => Some (existT _ FIELD (string_of_list_ascii z))
    | (QUOTED, z) => Some (existT _ QUOTED (csv_unquote z))
    | (L, _)      => Some (existT _ L tt)
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
(** Instantiation of the semantic lexer functor for CSV. *)
Module Import SemLexer := SemLexerFn STT LitLexer User.
Import SemLexer.Impl.

(* And extract; extract_path returns the default path for extraction *)
