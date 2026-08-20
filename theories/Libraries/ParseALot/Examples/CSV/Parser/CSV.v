(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List String.
Import ListNotations.
From Crane.Libraries.ParseALot.Examples.CSV.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Examples.CSV.Lexer Require Import Semantic.
From Crane.Libraries.ParseALot.Parser Require Import Tactics Utils Defs Main.

(** A parsed CSV document: a list of records, each a list of field strings. *)
Definition csv_value := list (list string).

(** Symbol types module for the CSV parser, specifying terminals and nonterminals. *)
Module CSV_Symbol_Types <: SymbolTypes.

  Definition terminal := Label.

  (** Converts a CSV terminal label to its string name. *)
  Definition showT (x : terminal) : string :=
    match x with
    | FIELD   => "FIELD"
    | QUOTED  => "QUOTED"
    | COMMA   => "COMMA"
    | NEWLINE => "NEWLINE"
    end.

  Ltac all_terminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := (eval compute in (String.compare (showT lx) (showT ly)))
        in  exact r
    end.

  (** Comparison function on CSV terminals, computed via their string names. *)
  Definition compareT : forall (x y : terminal), comparison.
    intros x y; destruct x eqn:hx; destruct y eqn:hy; all_terminal_comparisons x y.
  Defined.

  (** Proof that [compareT] returns [Eq] iff its arguments are equal. *)
  Lemma compareT_eq :
    forall x y : terminal,
      compareT x y = Eq <-> x = y.
  Proof.
    intros x y; split; intros heq; destruct x; destruct y; auto; sis; tc.
  Qed.

  (** Proof that [compareT] is transitive in each comparison result. *)
  Lemma compareT_trans :
    forall (c : comparison) (x y z : terminal),
      compareT x y = c -> compareT y z = c -> compareT x z = c.
  Proof.
    intros c x y z h1 h2; destruct x; destruct y; destruct z; auto; sis; tc.
  Qed.

  (** Nonterminal symbols of the CSV grammar. *)
  Inductive nonterminal' :=
  | Csv
  | Rows
  | Row
  | Fields
  | Field.

  (** Alias for the nonterminal type. *)
  Definition nonterminal := nonterminal'.

  (** Converts a CSV nonterminal to its string name. *)
  Definition showNT (x : nonterminal) : string :=
    match x with
    | Csv    => "Csv"
    | Rows   => "Rows"
    | Row    => "Row"
    | Fields => "Fields"
    | Field  => "Field"
    end.

  Ltac all_nonterminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := eval compute in (String.compare (showNT lx) (showNT ly))
        in  exact r
    end.

  (** Comparison function on CSV nonterminals, computed via their string names. *)
  Definition compareNT (x y : nonterminal) : comparison.
    destruct x eqn:hx; destruct y eqn:hy; all_nonterminal_comparisons x y.
  Defined.

  (** Proof that [compareNT] returns [Eq] iff its arguments are equal. *)
  Lemma compareNT_eq :
    forall x y : nonterminal,
      compareNT x y = Eq <-> x = y.
  Proof.
    intros x y; split; intros heq; destruct x; destruct y; auto; sis; tc.
  Qed.

  (** Proof that [compareNT] is transitive in each comparison result. *)
  Lemma compareNT_trans :
    forall (c : comparison) (x y z : nonterminal),
      compareNT x y = c -> compareNT y z = c -> compareNT x z = c.
  Proof.
    intros c x y z h1 h2; destruct x; destruct y; destruct z; auto; sis; tc.
  Qed.

  (** Semantic type family for CSV terminals, delegating to the semantic lexer. *)
  Definition t_semty : terminal -> Type :=
    Crane.Libraries.ParseALot.Examples.CSV.Lexer.Semantic.User.sem_ty.

  (** Semantic type family for CSV nonterminals. *)
  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Csv    => list (list string)
    | Rows   => list (list string)
    | Row    => list string
    | Fields => list string
    | Field  => string
    end.

End CSV_Symbol_Types.

(** Defs module bundling the CSV symbol types for the parser functor. *)
Module D <: Defs.T.
  Module        SymTy := CSV_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

(** Instantiation of the parser functor for CSV. *)
Module Export CSV_Parser := Make D.

(** Grammar productions for CSV (RFC 4180), each paired with a semantic
    predicate and action. Newlines separate records; fields (possibly empty)
    are comma-separated. The grammar is LL(1): the four token classes have
    disjoint FIRST sets, so every nullable choice is decided by one token of
    lookahead. A trailing newline yields one final empty record [[""]]. *)
Definition csvGrammarEntries : list grammar_entry :=
  [
    @existT _ _
            (Csv, [NT Row ; NT Rows])
            (fun _ => true,
             fun tup =>
               match tup with
               | (r, (rs, _)) => r :: rs
               end)

  ; @existT _ _
            (Rows, [T NEWLINE ; NT Row ; NT Rows])
            (fun _ => true,
             fun tup =>
               match tup with
               | (_, (r, (rs, _))) => r :: rs
               end)

  ; @existT _ _
            (Rows, [])
            (fun _ => true,
             fun _ => [])

  ; @existT _ _
            (Row, [NT Field ; NT Fields])
            (fun _ => true,
             fun tup =>
               match tup with
               | (f, (fs, _)) => f :: fs
               end)

  ; @existT _ _
            (Fields, [T COMMA ; NT Field ; NT Fields])
            (fun _ => true,
             fun tup =>
               match tup with
               | (_, (f, (fs, _))) => f :: fs
               end)

  ; @existT _ _
            (Fields, [])
            (fun _ => true,
             fun _ => [])

  ; @existT _ _
            (Field, [T FIELD])
            (fun _ => true,
             fun tup =>
               match tup with
               | (s, _) => s
               end)

  ; @existT _ _
            (Field, [T QUOTED])
            (fun _ => true,
             fun tup =>
               match tup with
               | (s, _) => s
               end)

  ; @existT _ _
            (Field, [])
            (fun _ => true,
             fun _ => ""%string)
  ].

(** Alias for the CSV semantic lex function. *)
Definition lex_sem := Crane.Libraries.ParseALot.Examples.CSV.Lexer.Semantic.SemLexer.Impl.lex_sem.
(** Alias for the CSV literal lexer rules. *)
Definition lex_rus := Crane.Libraries.ParseALot.Examples.CSV.Lexer.Literal.rus.
(** Lexes a CSV input string into typed tokens. There is no whitespace token --
    spaces and tabs are significant field content -- so nothing is filtered. *)
Definition lex_csv (s : String) : option (list token) * String := lex_sem lex_rus s.

(** Parses a token list as a CSV document starting from the [Csv] nonterminal. *)
Definition parse_csv       := parse (grammar_of_entry_list csvGrammarEntries) (grammar_of_entry_list_wf _) Csv.
(** Pretty-prints the result of parsing starting from the [Csv] nonterminal. *)
Definition show_csv_result := show_result Csv.
