(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import BinNat Bool List NArith PeanoNat String.
Import ListNotations.
From Crane.Libraries.ParseALot.Examples.PPM.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Examples.PPM.Lexer Require Import Semantic.
From Crane.Libraries.ParseALot.Parser Require Import Tactics Defs Main.

(** Record type for a single RGB pixel triple. *)
Record rgb_triple : Type :=
  mkRGBTriple { red   : N
              ; green : N
              ; blue  : N
              }.

(** Returns true iff all three channels of the triple are at most [m]. *)
Definition triple_le_max (t : rgb_triple) (m : N) : bool :=
  match t with
  | mkRGBTriple r g b =>
      (r <=? m)%N && (g <=? m)%N && (b <=? m)%N
  end.

(** Returns true iff every triple in the list has all channels at most [m]. *)
Fixpoint triples_le_max (ts : list rgb_triple) (m : N) : bool :=
  match ts with
  | [] => true
  | t :: ts' => triple_le_max t m && triples_le_max ts' m
  end.

(** Returns true iff the list length equals [w * h], used to validate image dimensions. *)
Definition width_x_height_eq_length {A : Type} (w h : N) (l : list A) : bool :=
  (w * h =? N.of_nat (List.length l))%N.

(** Record type representing a complete parsed PPM image. *)
Record ppm_value : Type :=
  mkPPMValue { width   : N
             ; height  : N
             ; max     : N
             ; triples : list rgb_triple
             }.

(** Symbol types module for the PPM parser, specifying terminals and nonterminals. *)
Module PPM_Symbol_Types <: SymbolTypes.

  Definition terminal := Label.

  (** Comparison function on PPM terminals. *)
  Definition compareT (x y : terminal) : comparison :=
    match x, y with
    | NAT, NAT => Eq
    | NAT, _ => Lt
    | P3, NAT => Gt
    | P3, P3 => Eq
    | P3, WS => Lt
    | WS, WS => Eq
    | WS, _ => Gt
    end.

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

  (** Nonterminal symbols of the PPM grammar. *)
  Inductive nonterminal' :=
  | Document
  | Triples.

  (** Alias for the nonterminal type. *)
  Definition nonterminal := nonterminal'.

  (** Comparison function on PPM nonterminals. *)
  Definition compareNT (x y : nonterminal) : comparison :=
    match x, y with
    | Document, Triples => Lt
    | Triples, Document => Gt
    | _, _ => Eq
    end.

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

  (** Converts a PPM terminal label to its string name. *)
  Definition showT (x : terminal) : string :=
    match x with
    | P3 => "P3"
    | NAT => "NAT"
    | WS => "WS"
    end.

  (** Converts a PPM nonterminal to its string name. *)
  Definition showNT (x : nonterminal) : string :=
    match x with
    | Document => "Document"
    | Triples => "Triples"
    end.

  (** Semantic type family for PPM terminals, delegating to the semantic lexer. *)
  Definition t_semty : terminal -> Type :=
    Crane.Libraries.ParseALot.Examples.PPM.Lexer.Semantic.User.sem_ty.

  (** Semantic type family for PPM nonterminals. *)
  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Document => ppm_value
    | Triples  => list rgb_triple
    end.

End PPM_Symbol_Types.

(** Defs module bundling the PPM symbol types for the parser functor. *)
Module D <: Defs.T.
  Module        SymTy := PPM_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

(** Instantiation of the parser functor for PPM. *)
Module Export PPM_Parser := Make D.

(** Grammar productions for PPM, each paired with a semantic predicate and action. *)
Definition ppmGrammarEntries : list grammar_entry :=
  [
    @existT _ _
            (Document, [T P3; T NAT ; T NAT ; T NAT ; NT Triples])
            (fun tup =>
               match tup with
               | (_, (w, (h, (m, (ts, _))))) =>
                   width_x_height_eq_length w h ts && triples_le_max ts m
               end,
             fun tup =>
               match tup with
               | (_, (w, (h, (m, (ts, _))))) =>
                 mkPPMValue w h m ts
               end)

  ; @existT _ _
            (Triples, [])
            (fun _ => true, fun _ => [])

  ; @existT _ _
            (Triples, [T NAT; T NAT; T NAT; NT Triples])
            (fun _ => true,
             fun tup =>
               match tup with
               | (x, (y, (z, (tpls, _)))) =>
                 mkRGBTriple x y z :: tpls
               end)
  ].

(** Filter predicate that rejects whitespace tokens. *)
Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ WS _ => false
  | _ => true
  end.

(** Alias for the PPM semantic lex function. *)
Definition lex_sem  := Crane.Libraries.ParseALot.Examples.PPM.Lexer.Semantic.SemLexer.Impl.lex_sem.
(** Alias for the PPM literal lexer rules. *)
Definition lex_rus  := Crane.Libraries.ParseALot.Examples.PPM.Lexer.Literal.rus.
(** Semantic lexer partially applied to the PPM rules. *)
Definition lex_ppm' := lex_sem lex_rus.
(** Lexes a PPM input string, returning typed tokens with whitespace filtered out. *)
Definition lex_ppm  (s : String) : option (list token) * String :=
  let res' := lex_ppm' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

(** Parses a token list as a PPM document starting from the [Document] nonterminal. *)
Definition parse_ppm       := parse (grammar_of_entry_list ppmGrammarEntries) (grammar_of_entry_list_wf _) Document.
(** Pretty-prints the result of parsing starting from the [Document] nonterminal. *)
Definition show_ppm_result := PPM_Parser.ParserAndProofs.PEF.PS.P.show_result Document.
