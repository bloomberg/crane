(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List Floats String.
From Crane.Libraries.ParseALot.Examples.XML.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Examples.XML.Lexer Require Import Semantic.
From Crane.Libraries.ParseALot.Parser Require Import Tactics Utils Defs Main.
Import ListNotations.

(** Inductive type representing an XML element tree node or leaf. *)
Inductive xml_tree : Type :=
| XmlNode (name : string) (attrs : list (string * string)) (children : list xml_tree)
| XmlLeaf (name : string) (attrs : list (string * string)).

(** Inductive type representing a complete XML document (optional prolog plus root element). *)
Inductive xml_document : Type :=
| XmlDocument (attrs : list (string * string)) (elt : xml_tree).

(** Symbol types module for the XML parser, specifying terminals and nonterminals. *)
Module XML_Symbol_Types <: SymbolTypes.

  Definition terminal := Label.

  (** Converts an XML terminal label to its string name. *)
  Definition showT (x : terminal) : string :=
    match x with
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

  Ltac all_terminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := (eval compute in (String.compare (showT lx) (showT ly)))
        in  exact r
    end.

  (** Comparison function on XML terminals, computed via their string names. *)
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

  (** Nonterminal symbols of the XML grammar. *)
  Inductive nonterminal' :=
  | Document
  | Prolog_opt
  | Prolog
  | Content
  | Element
  | Attrs
  | Attr.

  (** Alias for the nonterminal type. *)
  Definition nonterminal := nonterminal'.

  (** Converts an XML nonterminal to its string name. *)
  Definition showNT (x : nonterminal) : string :=
    match x with
    | Document => "Document"
    | Prolog_opt => "Prolog_opt"
    | Prolog => "Prolog"
    | Content => "Content"
    | Element => "Element"
    | Attrs => "Attrs"
    | Attr => "Attr"
    end.

  Ltac all_nonterminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := eval compute in (String.compare (showNT lx) (showNT ly))
        in  exact r
    end.

  (** Comparison function on XML nonterminals, computed via their string names. *)
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

  (** Semantic type family for XML terminals, delegating to the semantic lexer. *)
  Definition t_semty : terminal -> Type :=
    Crane.Libraries.ParseALot.Examples.XML.Lexer.Semantic.User.sem_ty.

  (** Semantic type family for XML nonterminals. *)
  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Document => xml_document
    | Prolog_opt => list (string * string)
    | Prolog => list (string * string)
    | Content => list xml_tree
    | Element => xml_tree
    | Attrs => list (string * string)
    | Attr => string * string
    end.

End XML_Symbol_Types.

(** Defs module bundling the XML symbol types for the parser functor. *)
Module D <: Defs.T.
  Module        SymTy := XML_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

(** Instantiation of the parser functor for XML. *)
Module Export XML_Parser := Make D.

(** Grammar productions for XML, each paired with a semantic predicate and action. *)
Definition xmlGrammarEntries : list grammar_entry :=
  [

    @existT _ _ (Document, [NT Prolog_opt ; NT Element])
            (fun _ => true, fun tup => match tup with
                                       | (attrs, (elt, _)) => XmlDocument attrs elt
                                       end)

    ; @existT _ _ (Prolog_opt, [NT Prolog])
              (fun _ => true, fun tup => match tup with
                                         | (attrs, _) => attrs
                                         end)

    ; @existT _ _ (Prolog_opt, [])
              (fun _ => true, fun _ => [])

    ; @existT _ _ (Prolog, [T XMLDeclOpen ; NT Attrs ; T SPECIAL_CLOSE])
              (fun _ => true, fun tup => match tup with
                                         | (_, (attrs, (_, _))) => attrs
                                         end)

    ; @existT _ _ (Attrs, [NT Attr ; NT Attrs])
              (fun _ => true, fun tup => match tup with
                                         | (x, (xs, _)) => x :: xs
                                         end)

    ; @existT _ _ (Attrs, [])
              (fun _ => true, fun _ => [])

    ; @existT _ _ (Content, [NT Element ; NT Content])
              (fun _ => true, fun tup => match tup with
                                         | (t, (ts, _)) => t :: ts
                                         end)

    ; @existT _ _ (Content, [])
              (fun _ => true, fun _ => [])

    ; @existT _ _ (Element, [T OPEN ; T NAME ; NT Attrs ; T CLOSE ; NT Content ; T OPEN ; T SLASH ; T NAME ; T CLOSE])
              (fun tup => match tup with
                          | (_, (nm, (attrs, (_, (ts, (_, (_, (nm', (_, _))))))))) => String.eqb nm nm'
                          end,
               fun tup => match tup with
                          | (_, (nm, (attrs, (_, (ts, (_, (_, (nm', (_, _))))))))) => XmlNode nm attrs ts
                          end)

    ; @existT _ _ (Element, [T OPEN ; T NAME ; NT Attrs ; T SLASH_CLOSE])
              (fun _ => true, fun tup => match tup with
                                         | (_, (nm, (attrs, (_, _)))) => XmlLeaf nm attrs
                                         end)

    ; @existT _ _ (Attr, [T NAME ; T EQUALS ; T STRING])
              (fun _ => true, fun tup => match tup with
                                         | (nm, (_, (s, _))) => (nm, s)
                                         end)

  ].

(** Filter predicate that rejects whitespace tokens. *)
Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ SEA_WS _ => false
  | _ => true
  end.

(** Alias for the XML semantic lex function. *)
Definition lex_sem   := Crane.Libraries.ParseALot.Examples.XML.Lexer.Semantic.SemLexer.Impl.lex_sem.
(** Alias for the XML literal lexer rules. *)
Definition lex_rus   := Crane.Libraries.ParseALot.Examples.XML.Lexer.Literal.rus.
(** Semantic lexer partially applied to the XML rules. *)
Definition lex_xml'  := lex_sem lex_rus.
(** Lexes an XML input string, returning typed tokens with whitespace filtered out. *)
Definition lex_xml (s : String) : option (list token) * String :=
  let res' := lex_xml' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

(** Parses a token list as an XML document starting from the [Document] nonterminal. *)
Definition parse_xml       := parse (grammar_of_entry_list xmlGrammarEntries) (grammar_of_entry_list_wf _) Document.
(** Pretty-prints the result of parsing starting from the [Document] nonterminal. *)
Definition show_xml_result := show_result Document.
