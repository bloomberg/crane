(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List QArith String.
From Crane.Libraries.ParseALot.Examples.Newick.Lexer Require Import Literal.
From Crane.Libraries.ParseALot.Examples.Newick.Lexer Require Import Semantic.
From Crane.Libraries.ParseALot.Parser Require Import Tactics Utils Defs Main.
Import ListNotations.

(** Inductive type representing a node in a Newick phylogenetic tree. *)
Inductive newick_node : Type :=
| NkLeaf (label : N) (branch_length : Q)
| NkINode (descendants : list newick_node) (branch_length : Q).

(** Inductive type representing a complete Newick phylogenetic tree. *)
Inductive newick_tree : Type :=
| NkTree : list newick_node -> newick_tree.

(** Symbol types module for the Newick parser, specifying terminals and nonterminals. *)
Module Newick_Symbol_Types <: SymbolTypes.

  Definition terminal := Label.

  (** Converts a Newick terminal label to its string name. *)
  Definition showT (x : terminal) : string :=
    match x with
    | NAT => "NAT"
    | COLON => "COLON"
    | COMMA => "COMMA"
    | DECIMAL_POINT => "DECIMAL_POINT"
    | L_PAREN => "L_PAREN"
    | R_PAREN => "R_PAREN"
    | SEMICOLON => "SEMICOLON"
    | WS => "WS"
    end.

  Ltac all_terminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := (eval compute in (String.compare (showT lx) (showT ly)))
        in  exact r
    end.

  (** Comparison function on Newick terminals, computed via their string names. *)
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

  (** Nonterminal symbols of the Newick grammar. *)
  Inductive nonterminal' :=
  | Trees
  | Tree
  | Subtree
  | Subtrees
  | Subtrees'
  | BranchLength.

  (** Alias for the nonterminal type. *)
  Definition nonterminal := nonterminal'.

  (** Converts a Newick nonterminal to its string name. *)
  Definition showNT (x : nonterminal) : string :=
    match x with
    | Trees => "Trees"
    | Tree => "Tree"
    | Subtree => "Subtree"
    | Subtrees => "Subtrees"
    | Subtrees' => "Subtrees'"
    | BranchLength => "BranchLength"
    end.

  Ltac all_nonterminal_comparisons x y :=
    match goal with
    | Hx : x = ?lx, Hy : y = ?ly |- _ =>
        let r := eval compute in (String.compare (showNT lx) (showNT ly))
        in  exact r
    end.

  (** Comparison function on Newick nonterminals, computed via their string names. *)
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

  (** Semantic type family for Newick terminals, delegating to the semantic lexer. *)
  Definition t_semty : terminal -> Type :=
    Crane.Libraries.ParseALot.Examples.Newick.Lexer.Semantic.User.sem_ty.

  (** Semantic type family for Newick nonterminals. *)
  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Trees => list newick_tree
    | Tree => newick_tree
    | Subtree => newick_node
    | Subtrees => list newick_node
    | Subtrees' => list newick_node
    | BranchLength => Q
    end.

End Newick_Symbol_Types.

(** Defs module bundling the Newick symbol types for the parser functor. *)
Module D <: Defs.T.
  Module        SymTy := Newick_Symbol_Types.
  Module Export Defs  := DefsFn SymTy.
End D.

(** Instantiation of the parser functor for Newick. *)
Module Export Newick_Parser := Make D.

(** Grammar productions for Newick, each paired with a semantic predicate and action. *)
Definition newickGrammarEntries : list grammar_entry :=
  [ @existT _ _
            (Trees, [])
            (fun _ => true, fun _ => [])

  ; @existT _ _
            (Trees, [NT Tree ; NT Trees])
            (fun _ => true, fun tup =>
                              match tup with
                              | (t, (ts, _)) => t :: ts
                              end)
  ; @existT _ _
            (Tree, [NT Subtrees ; T SEMICOLON])
            (fun _ => true, fun tup =>
                              match tup with
                              | (ts, (_, _)) => NkTree ts
                              end)

  ; @existT _ _ (Subtrees, [T L_PAREN ; NT Subtree ; NT Subtrees' ; T R_PAREN])
            (fun _ => true, fun tup =>
                              match tup with
                              | (_, (t, (ts, (_, _)))) => t :: ts
                              end)

  ; @existT _ _ (Subtrees', [T COMMA ; NT Subtree ; NT Subtrees'])
            (fun _ => true, fun tup =>
                              match tup with
                              | (_, (t, (ts, _))) => t :: ts
                              end)

  ; @existT _ _ (Subtrees', [])
            (fun _ => true, fun _ => [])

  ; @existT _ _ (Subtree, [NT Subtrees ; T COLON ; NT BranchLength])
            (fun _ => true, fun tup =>
                              match tup with
                              | (ts, (_, (l, _))) => NkINode ts l
                              end)

  ; @existT _ _ (Subtree, [T NAT ; T COLON ; NT BranchLength])
            (fun _ => true, fun tup =>
                              match tup with
                              | (n, (_, (l, _))) => NkLeaf n l
                              end)

  ; @existT _ _ (BranchLength, [T NAT ; T DECIMAL_POINT ; T NAT])
            (fun _ => true, fun tup =>
                              match tup with
                              | (i, (_, (m, _))) =>
                                  let q1 :=  Z.of_N i # 1            in
                                  let q2 := (Z.of_N m # 1) / 1000000 in
                                  q1 + q2
                              end)
  ].

(** Filter predicate that rejects whitespace tokens. *)
Definition notWS (t : token) : bool :=
  match t with
  | @existT _ _ WS _ => false
  | _ => true
  end.

(** Alias for the Newick semantic lex function. *)
Definition lex_sem   := Crane.Libraries.ParseALot.Examples.Newick.Lexer.Semantic.SemLexer.Impl.lex_sem.
(** Alias for the Newick literal lexer rules. *)
Definition lex_rus   := Crane.Libraries.ParseALot.Examples.Newick.Lexer.Literal.rus.
(** Semantic lexer partially applied to the Newick rules. *)
Definition lex_newick' := lex_sem lex_rus.
(** Lexes a Newick input string, returning typed tokens with whitespace filtered out. *)
Definition lex_newick (s : String) : option (list token) * String :=
  let res' := lex_newick' s in
  match res' with
  | (Some ts, rem) => (Some (List.filter notWS ts), rem)
  | (None, _) => res'
  end.

(** Parses a token list as a Newick forest starting from the [Trees] nonterminal. *)
Definition parse_newick       := parse (grammar_of_entry_list newickGrammarEntries) (grammar_of_entry_list_wf _) Trees.
(** Pretty-prints the result of parsing starting from the [Trees] nonterminal. *)
Definition show_newick_result := show_result Trees.
