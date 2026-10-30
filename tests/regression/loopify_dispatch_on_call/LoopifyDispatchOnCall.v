(** A recursive call whose result decides a branch: the condition of an
    [if] in [parity], the scrutinee of a match in [graft].  Normalize binds
    the call before the dispatch, and the machine resumes after it there. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Set Crane Loopify.

Module LoopifyDispatchOnCall.

Inductive tree := Leaf | Node (l : tree) (r : tree).

Fixpoint parity (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node l r => if parity l then negb (parity r) else parity r
  end.

Fixpoint graft (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l r =>
    match graft l with
    | Leaf => Node (graft r) Leaf
    | Node a b => Node (graft r) (Node b a)
    end
  end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 1 | Node l r => size l + size r end.

Fixpoint comb (n : nat) : tree :=
  match n with
  | O => Leaf
  | S O => Node Leaf Leaf
  | S (S m as k) => Node (comb k) (Node Leaf (comb m))
  end.

End LoopifyDispatchOnCall.

Crane Extraction "loopify_dispatch_on_call" LoopifyDispatchOnCall.
