(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test tries to trigger the Impossible exception at mlutil.ml:1278
   in the iota_red function when handling pattern matching cases that
   aren't currently supported (not Prel 1 with single id, not Pwild with
   empty ids, etc.)
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module PatternImpossible.

Inductive three : Type :=
| One : three
| Two : three
| Three : three.

Inductive nested : Type :=
| Leaf : nat -> nested
| Node : nested -> nested -> nested.

(* Complex pattern matching that might trigger edge cases in iota reduction *)
Definition complex_match (x : three) : nat :=
  match x with
  | One => 1
  | Two => 2
  | Three => 3
  end.

(* Nested pattern matching *)
Definition nested_match (n : nested) : nat :=
  match n with
  | Leaf x => x
  | Node (Leaf a) (Leaf b) => a + b
  | Node _ _ => 0
  end.

(* Match inside match - might trigger iota reduction edge cases *)
Definition double_match (x y : three) : nat :=
  match x with
  | One => match y with
           | One => 1
           | Two => 2
           | Three => 3
           end
  | Two => 10
  | Three => 20
  end.

(* Pattern with constructor having multiple arguments *)
Definition multi_arg_pattern (n : nested) : nat :=
  match n with
  | Node (Leaf x) (Node (Leaf y) (Leaf z)) => x + y + z
  | _ => 0
  end.

Definition test1 := complex_match One.
Definition test2 := nested_match (Node (Leaf 5) (Leaf 10)).
Definition test3 := double_match One Two.

End PatternImpossible.

Crane Extraction "pattern_impossible" PatternImpossible.
