From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Loopify, a match on the loop variable nested inside a projection of
    a match ([py (match t with Leaf => fold_left ... | ...)]) reads the loop
    pointer as [_loop_t.v()] instead of [_loop_t->v()]: "member reference
    type 'const tree *' is a pointer".  Fine without Loopify, and fine when
    the [fold_left] is replaced by a plain record. *)
Module LoopifyRereadLoopPointer.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Record pt : Type := mkpt { px : nat; py : bool }.

Fixpoint g (t : tree) : bool :=
  match t with
  | Leaf => py (match t with
                | Leaf => fold_left (fun (acc : pt) (_ : bool) => acc) [] (mkpt 0 true)
                | Node _ _ _ => mkpt 0 false
                end)
  | Node l _ _ => g l
  end.

End LoopifyRereadLoopPointer.

Crane Extraction "loopify_reread_loop_pointer" LoopifyRereadLoopPointer.
