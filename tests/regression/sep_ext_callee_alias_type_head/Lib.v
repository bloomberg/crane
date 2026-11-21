From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module Type L.
  Parameter Label : Type.
End L.

Module DefsFn (X : L).
  Definition Token : Type := X.Label * nat.
End DefsFn.

Module Type Lexer (X : L).
  Module D := DefsFn X.
  Parameter lex : list X.Label -> list nat -> list D.Token * list nat.
End Lexer.

Module LexFn (X : L) <: Lexer X.
  Module D := DefsFn X.
  Definition lex (rus : list X.Label) (code : list nat) : list D.Token * list nat :=
    (map (fun r => (r, length code)) rus, code).
End LexFn.

Module SemFn (X : L) (LX : Lexer X).
  Definition lex_with (lx : list nat -> list LX.D.Token * list nat) (code : list nat) : nat :=
    length (fst (lx code)).
End SemFn.
