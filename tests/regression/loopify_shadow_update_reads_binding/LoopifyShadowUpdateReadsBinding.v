From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

(** A tail loop whose new arguments read a field of the list it walks.

    One call passes a fresh list, so [fs] is kept by value in [_loop_fs],
    and the match binds [f] and [rest] by reference into that value.  The
    updates were staged in a temporary only where one names another's
    variable, and [f v] names [f], not [_loop_fs]: [_loop_fs] was assigned
    [rest] first, and [f] then read the same storage, now the next cell's
    function. *)

Module LoopifyShadowUpdateReadsBinding.

Fixpoint apply_n (n v : nat) (fs : list (nat -> nat)) : nat :=
  match n with
  | O => v
  | S m =>
    match fs with
    | [] => apply_n m v []
    | f :: rest => apply_n m (f v) rest
    end
  end.

Definition result : nat := apply_n 4 2 [fun x => x + 1; fun x => x * 10; fun x => x + 3].

End LoopifyShadowUpdateReadsBinding.

Crane Extraction "loopify_shadow_update_reads_binding" LoopifyShadowUpdateReadsBinding.
