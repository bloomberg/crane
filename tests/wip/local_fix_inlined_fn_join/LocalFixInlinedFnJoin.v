(** Found by Ephyra round 28. Variant of round 24's [local_fix_fn_result_join]
    (fixed). A local fixpoint returning [nat -> nat], applied to [[]] and
    passed to a lambda, is lowered to an immediately invoked C++ lambda with
    no declared return type: its [nil] branch returns the accumulator
    ([std::move(acc)], a [crane::fn<uint64_t(uint64_t)>]) while its [cons]
    branch returns a fresh lambda partially applying an inner local
    fixpoint, so the two returns deduce different types. Without the inner
    fixpoint (the [cons] branch a plain lambda) it compiles. Expected:
    compiles, [result = 2]. Actual: "return type '(lambda ...)' must match
    previous return type 'crane::fn<unsigned long long (unsigned long long)>'
    when lambda expression has unspecified explicit return type". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module LocalFixInlinedFnJoin.

Definition result : nat :=
  (fun w : nat -> nat => w 0 + w 1)
    (let fix go (l : list bool) (acc : nat -> nat) {struct l} : nat -> nat :=
       match l with
       | [] => acc
       | _ :: r =>
           let fix go2 (l2 : list bool) (acc2 : nat -> nat) {struct l2} : nat -> nat :=
             match l2 with [] => fun _ : nat => 0 | _ :: r2 => go2 r2 acc end in
           go2 r (fun _ : nat => 0)
       end in
     go [] (fun _ : nat => 1)).

End LocalFixInlinedFnJoin.

Crane Extraction "local_fix_inlined_fn_join" LocalFixInlinedFnJoin.
