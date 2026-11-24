(** Found by Ephyra round 24 (under [CRANE_LOOPIFY_CENSUS]; no flag is
    needed). A list recursion [go] returning [nat -> nat] whose [cons] case
    binds the recursive result [rv] and returns a call of a local [go2],
    itself returning, in its [cons] case, a call of a local [go3] (a tail
    loop) whose [nil] case may return [rv]; the result is let-bound and
    applied twice.  The lambda [go2] lowers to returns [acc] (a
    [crane::fn]) on one path and the closure [[](uint64_t) { return 0; }]
    on another, so its deduced return type disagrees.  Related to round
    1's [local_fix_returns_function] and round 19's
    [branch_callables_fix_accumulator] (both fixed); this shape still fails.

    Expected: compiles; [result = 6].
    Actual: "return type '(lambda ...)' must match previous return type
    'crane::fn<unsigned long long (unsigned long long)>' when lambda
    expression has unspecified explicit return type". *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module LocalFixFnResultJoin.

Definition result : nat :=
  let f :=
    let fix go (l : list nat) (acc : nat -> nat) {struct l} : nat -> nat :=
      match l with
      | [] => acc
      | _ :: rest =>
        let rv := go rest acc in
        let fix go2 (k : list (bool * nat)) (acc2 : nat -> nat) {struct k} : nat -> nat :=
          match k with
          | [] => (fun _ : nat => 0)
          | _ :: _ =>
            let fix go3 (m : list nat) (acc3 : nat -> nat) {struct m} : nat -> nat :=
              match m with
              | [] => match 11 with O => rv | S _ => (fun _ : nat => 10) end
              | _ :: m2 => let rv3 := go3 m2 acc3 in acc3
              end in go3 [3; 12] acc
          end in
        go2 (match rest with [] => [] | [_] => [(false, 12)] | _ => [(false, 1); (true, 14)] end) acc
      end in go [1; 2; 3] (fun _ : nat => 3)
  in f 1 + f 2.

End LocalFixFnResultJoin.

Crane Extraction "local_fix_fn_result_join" LocalFixFnResultJoin.
