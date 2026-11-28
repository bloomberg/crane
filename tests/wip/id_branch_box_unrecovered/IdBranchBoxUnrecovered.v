(** Crane bug, found by Ephyra round 31: [id f x] (with [id] declared at
    [crane::obj]) as one branch of a match whose value is passed to a
    template function.  The branch is lowered in an immediately invoked
    lambda that states no result type, so nothing says what to recover the
    box at and the lambda returns a [crane::obj]: "no matching function for
    call to 'psize'" (under CRANE_CHECK_IR, "argument, unbox").  Expected:
    [e = 0].  Present at 081553f85. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module IdBranchBoxUnrecovered.

Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.
Fixpoint psize {A : Type} (t : ptree A) : nat :=
  match t with PLeaf => 0 | PNode l _ r => S (psize l + psize r) end.
Definition e : nat :=
  psize (match 9 with O => @PLeaf nat | S m => (id (fun _ : nat => @PLeaf nat)) m end).

End IdBranchBoxUnrecovered.

Crane Extraction "id_branch_box_unrecovered" IdBranchBoxUnrecovered.
