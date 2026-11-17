From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

(** Mutual recursion between functions returning nothing.

    A tail call of [odd_void] is generated as its statement and a return,
    [odd_void(m); return;], which Loopify did not continue in: it ran the
    partner's body in a lambda, declared a machine with a [void _result]
    and called an adopted entry it never defined, and the C++ did not
    compile.  The call now continues in the partner's body, every path of
    which ends in a return, and the group is a tail loop. *)

Module LoopifyMutualVoid.

Fixpoint even_void (n : nat) : unit :=
  match n with
  | O => tt
  | S m => odd_void m
  end
with odd_void (n : nat) : unit :=
  match n with
  | O => tt
  | S m => even_void m
  end.

End LoopifyMutualVoid.

Crane Extraction "loopify_mutual_void" LoopifyMutualVoid.
