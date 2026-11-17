From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A match (or [if]) whose scrutinee is another match: after case-of-case the
    immediately invoked lambda is annotated with the inner match's result type
    instead of the outer one.

    - [t]: inner [list nat], outer [nat]: [-> List<uint64_t>] does not compile.
    - [g]: inner [bool], outer [nat] under [Nat.leb]: [-> bool] compiles and
      turns [12] into [true] (1); [g 3 4] is [true] in Rocq, [false] in C++.
    - [u]: same at a top-level constant: Rocq [12], C++ [1].
    - [v]: a projection of a match on a [fold_left] pair: [-> pt] on a lambda
      returning [px]; does not compile.
    - [w]: a match whose branches are all lambdas, applied to [k]: the
      lambdas move out of the match and the branches kept their arrow type,
      [-> crane::fn<uint64_t(uint64_t)>]; does not compile.

    The wrong values have no diagnostic (with a literal left operand clang
    flags [g] via -Wtautological-constant-out-of-range-compare). *)
Module CaseOfCaseResultType.

Definition h (n : nat) : nat := n + 7.

Definition t : nat :=
  match (match (let fix go (m : list bool) (acc : nat) {struct m} : nat :=
                  match m with [] => 0 | _ :: _ => acc end in go [] 0)
         with 0 => [0; 1] | S _ => [] end)
  with [] => 0 | _ :: _ => h 1 end.

Definition g (k n : nat) : bool :=
  Nat.leb k (if (match n with 0 => true | S _ => false end) then 0 else 12).

Definition u : nat :=
  match (match h 0 with 0 => true | S _ => true end) with true => h 5 | false => 0 end.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition v : nat :=
  px (match fold_left (fun (acc : option nat * pt) (e : list bool) => (@None nat, mkpt 0 true))
              (@nil (list bool)) (@None nat, mkpt 0 true)
      with (p, q) => mkpt 3 true end).

(** A match applied to an argument: the argument is pushed into the
    branches, which then return what their functions did. *)
Definition w (k n : nat) : bool :=
  Nat.leb 3 ((match n with 0 => fun x : nat => x | S _ => fun x => x + 9 end) k).

End CaseOfCaseResultType.

Crane Extraction "case_of_case_result_type" CaseOfCaseResultType.
