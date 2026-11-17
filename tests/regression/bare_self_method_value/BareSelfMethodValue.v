(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A method of a module's eponymous type, used as a function value by a
    definition of that same module.  The value is a function of the receiver,
    so it is written as a forwarding lambda; [this->size()] would apply the
    method instead of naming it, inside a static member function that has no
    [this].  The second inductive keeps the module from being promoted to the
    type itself, so [sizes] is defined out of line in the implementation. *)

From Stdlib Require Import List.
Import ListNotations.

Module BareSelfMethodValue.
  Inductive bareSelfMethodValue : Type :=
  | Leaf : bareSelfMethodValue
  | Node : bareSelfMethodValue -> nat -> bareSelfMethodValue -> bareSelfMethodValue.

  Inductive colour : Type := Red | Black.

  Fixpoint size (t : bareSelfMethodValue) : nat :=
    match t with
    | Leaf => 0
    | Node l _ r => S (size l + size r)
    end.

  Definition sizes (ts : list bareSelfMethodValue) : list nat := map size ts.

  Definition total (ts : list bareSelfMethodValue) : nat :=
    fold_left Nat.add (sizes ts) 0.

  Definition example : nat :=
    total [Leaf; Node Leaf 1 Leaf; Node (Node Leaf 2 Leaf) 3 Leaf].
End BareSelfMethodValue.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Extraction "bare_self_method_value" BareSelfMethodValue.
