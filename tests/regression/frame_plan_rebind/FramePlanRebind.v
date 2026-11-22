(** Found by Ephyra (round 22, first in the BDE flavour; the std flavour
    failed the same way). A tree recursion whose [Node] case runs a local
    fixpoint over a list of two primitive strings, passing the recursive
    call [g2 l] both as the initial accumulator and in its step, with a
    second (unused) inductive [ptree] in the module. Expected: extracts;
    [result = true].

    Fixed: under [CRANE_CHECK_IR] the frame plan check reported "a
    continuation binds again a local the recursion plan neither keeps nor
    finds recomputable" for the closure [go]. The recursion plan lists [go]
    as recomputable from [l], which the frame keeps, and the continuation
    rebinds it after restoring [l]; the check only accepted recomputation
    from parameters no turn changes. It now accepts what the frame keeps. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.
Module FramePlanRebind.
Inductive tree : Type := Leaf | Node (l : tree) (x : nat) (r : tree).
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Fixpoint g2 (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node l v r =>
    let fix go (m : list PrimString.string) (acc : bool) {struct m} : bool :=
      match m with [] => true | _ :: rest => go rest (g2 l) end in
    go ["a"%pstring; "b"%pstring] (g2 l)
  end.
Definition result : bool := g2 (Node (Node Leaf 1 Leaf) 2 Leaf).
End FramePlanRebind.
Crane Extraction "frame_plan_rebind" FramePlanRebind.
