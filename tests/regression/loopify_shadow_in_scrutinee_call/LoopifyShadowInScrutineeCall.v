From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

(** A tail loop matching on a call that takes its parameters.

    The loop walks [n] and [xs] by pointer ([const Nat *_loop_n]), and reads
    them through the pointer.  A scrutinee that mentions a pointer was taken
    for the pointer itself, so [firstn n xs] was passed the pointers, which
    did not compile. *)

Module LoopifyShadowInScrutineeCall.

Fixpoint walk (n : nat) (xs : list nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S m =>
    match firstn n xs with
    | [] => walk m xs acc
    | y :: _ => walk m xs (acc + y)
    end
  end.

Definition total : nat := walk 3 [5; 7; 9] 0.

End LoopifyShadowInScrutineeCall.

Crane Extraction "loopify_shadow_in_scrutinee_call" LoopifyShadowInScrutineeCall.
