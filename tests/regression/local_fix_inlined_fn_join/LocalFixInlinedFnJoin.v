(** Found by Ephyra round 28. Variant of round 24's [local_fix_fn_result_join].
    A local fixpoint returning [nat -> nat], applied to [[]] and passed to a
    lambda, was lowered to an immediately invoked C++ lambda with no
    declared return type: its [nil] branch returns the accumulator
    ([std::move(acc)], a [crane::fn<uint64_t(uint64_t)>]) while its [cons]
    branch returns a fresh lambda partially applying an inner local
    fixpoint, so the two returns deduced different types ("return type
    '(lambda ...)' must match previous return type 'crane::fn<...>'").

    Fixed: the join reads the type each [return] was lowered at, recorded
    by node identity.  The [cons] branch's closure captures the pattern
    field [a1], which the branch then reads through its local [a1_value];
    that substitution rebuilt the closure, which was no longer found and
    counted as unannotated.  A value the substitution rebuilds is now
    recorded at its original's type ([Lifting.local_var_subst_stmts],
    [Lowering_state.carry_returns]).

    Expected: compiles, [result = 2]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
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
