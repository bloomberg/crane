From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module ListSelfDeepCopy.

(** Recursive occurrence hidden under stdlib [list].  The list spine has its
    own iterative clone, so the generated C++ compiles.  However, each list
    element copy re-enters [chain::clone] recursively; copying a deep
    single-child chain with [dup_chain] therefore overflows the C++ stack. *)

Inductive chain : Type :=
| Stop : chain
| Link : list chain -> chain.

Definition dup_chain (c : chain) : chain * chain := (c, c).

End ListSelfDeepCopy.

Crane Extraction "list_self_deep_copy" ListSelfDeepCopy.
