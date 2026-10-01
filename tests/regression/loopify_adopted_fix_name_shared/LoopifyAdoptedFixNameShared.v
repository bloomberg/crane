From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

(** Crane bug (compile error): under [Set Crane Loopify], a function whose
    body let-binds two local fixpoints of the same name -- both [loop], the
    first inside a lambda -- adopts one as a second machine entry, and
    installing the adoption reroutes calls by name.  The names are shared
    ([loop_impl], [loop], [_self_loop]), so the other fixpoint's calls were
    rerouted too, to an entry that never handles them:
      error: use of undeclared identifier '_adopted_loop'

    Reduced from Vellvm, [Semantics/MemoryBytes.v:112]
    ([dvalue_extract_byte]: [dvalue_extract_struct_bytes] under its [pad]
    lambda, and [dvalue_extract_array_bytes]). *)

Module LoopifyAdoptedFixNameShared.
  Inductive tree : Type := Leaf (n : nat) | Node (ts : list tree) | Arr (ts : list tree).

  Fixpoint f (t : tree) (i : nat) {struct t} : option nat :=
    let struct_bytes (pad : option nat) : list tree -> nat -> option nat :=
      fix loop ts k {struct ts} :=
        match ts with
        | [] => match pad with Some p => Some (p + k) | None => None end
        | t' :: ts' => if Nat.ltb k 3 then f t' k else loop ts' (k - 3)
        end in
    let array_bytes :=
      fix loop (ts : list tree) (k : nat) {struct ts} :=
        match ts with
        | [] => None
        | t' :: ts' => if Nat.ltb k 2 then f t' k else loop ts' (k - 2)
        end in
    match t with
    | Leaf n => Some (n + i)
    | Node ts => struct_bytes (Some 1) ts i
    | Arr ts => array_bytes ts i
    end.

  (** The struct loop skips [Leaf 1] (4 >= 3), enters the array at 1, and
      the array loop reaches [Leaf 7] at 1. *)
  Definition r1 : option nat := f (Node [Leaf 1; Arr [Leaf 7; Leaf 5]]) 4.
End LoopifyAdoptedFixNameShared.

Set Crane Loopify.
Crane Extraction "loopify_adopted_fix_name_shared" LoopifyAdoptedFixNameShared.
