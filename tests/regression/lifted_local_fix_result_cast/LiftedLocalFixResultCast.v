From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** A local fixpoint with a type binder of its own is lifted to a template
    returning its variable, [T1 f_crane_go(List<T1>, T1)].  Called at a
    record under a projection, its result is cast to the enclosing
    function's return type, [crane::any_cast<bool>(f_crane_go(..)).py],
    where it is the record: it does not compile.  The body calls [go] as a
    local whose type binder makes it higher-rank, so lowering read its
    result back from a box, at the only type it had, the function's; the
    template it is lifted to returns its result unboxed, and the call
    standing for it is now the call alone. *)
Module LiftedLocalFixResultCast.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition f (n : nat) : bool :=
  let fix go {B : Type} (l : list B) (d : B) {struct l} : B :=
    match l with [] => d | x :: r => go r x end in
  py (go [mkpt 1 true] (mkpt 0 false)).

Definition t : bool := f 0.

End LiftedLocalFixResultCast.

Crane Extraction "lifted_local_fix_result_cast" LiftedLocalFixResultCast.
