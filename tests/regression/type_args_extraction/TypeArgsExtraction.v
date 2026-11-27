(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: an operation mapping can name the type arguments of a use
    ([TypeParameter] in a structured body).  [Monads.ITree] maps [rec] and
    [call] to [crane::rec<A, B>] and [crane::rec_call<A, B>], naming the
    recursion's argument and result types, which is what types the lambda
    passed to the loop combinator. *)

From ITree Require Import
  ITree
  ITreeFacts
.

From Crane Require Import Monads.ITree.   



Definition double_n_body (n : nat) : itree ((callE nat nat) +' void1) nat :=
  match n with
  | O => Ret 0
  | Datatypes.S x =>
      x' <- call x;;
      Ret (2 + x') 
  end.


Definition double_n (n : nat) : itree void1 nat
  := Eval unfold double_n_body in (rec double_n_body n).


Require Import Crane.Mapping.NatInt.


Crane Extraction "type_args_extraction" double_n.
