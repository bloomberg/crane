From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

(** A member of a mutual group recurses by the calls of itself it makes once
    Loopify has inlined its partners into it, not by every call between the
    group's members.

    [ja] calls its partner [jb] only through a partial application, a
    closure, so nothing is inlined into it and its body calls nothing it
    could loop on.  In the three-way cycle [f1 -> f2 -> f3 -> f1] each call is
    an operand of [+], so a partner's body runs in a lambda invoked in place
    of its call, where the next partner is not inlined: [f1]'s body never
    calls [f1].  The recursion plan used to give every member its group's
    kind, here "not only tail calls", which the finished bodies contradicted
    under [CRANE_CHECK_IR]. *)

Module LoopifyMemberOwnCalls.

Fixpoint ja (n : nat) : nat :=
  match n with O => 0 | S m => fold_left Nat.add (map (jb m) [m; m]) 0 end
with jb (n : nat) (x : nat) : nat :=
  match n with O => x | S m => x + ja m end.

Fixpoint f1 (n : nat) : nat :=
  match n with O => 0 | S n' => 1 + f2 n' end
with f2 (n : nat) : nat :=
  match n with O => 0 | S n' => 2 + f3 n' end
with f3 (n : nat) : nat :=
  match n with O => 0 | S n' => 3 + f1 n' end.

End LoopifyMemberOwnCalls.

Crane Extraction "loopify_member_own_calls" LoopifyMemberOwnCalls.
