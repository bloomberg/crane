(** A recursive call that ends a branch of a match standing as an operand.

    Normalize binds such a match to a temporary, and translation runs a
    bound match that is neither custom nor a record's in a lambda invoked
    in place, or as a conditional expression: the calls its branches end in
    are ordinary calls there, which no loop takes as turns.  ControlIR took
    them for points the machine resumes at, so [depthish] was entered by no
    call and [mirror] left calls its ControlIR said it took; both were
    declined, which [CRANE_CHECK_IR] reports of a loop the plan commits to. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Set Crane Loopify.

Module LoopifyOperandMatchCall.

Inductive tree := Leaf | Node (l : tree) (r : tree).

Fixpoint depthish (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l r => S (match l with Leaf => depthish r | Node _ _ => depthish l + depthish r end)
  end.

Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l r => Node (match r with Leaf => mirror l | Node _ _ => mirror r end) (mirror l)
  end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 1 | Node l r => size l + size r end.

Fixpoint comb (n : nat) : tree :=
  match n with
  | O => Leaf
  | S O => Node Leaf Leaf
  | S (S m as k) => Node (comb k) (Node Leaf (comb m))
  end.

End LoopifyOperandMatchCall.

Crane Extraction "loopify_operand_match_call" LoopifyOperandMatchCall.
