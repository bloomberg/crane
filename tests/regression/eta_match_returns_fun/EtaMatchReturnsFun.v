(** A function whose result type is itself a function, defined by a match whose
    branches already return function values.  Crane eta-expands the result but
    then returns the branch's function object instead of applying it:

    {v
      no viable conversion from returned value of type
      'const std::function<unsigned long long (unsigned long long)>'
      to function return type 'uint64_t'
    v} *)

From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List Arith.

Module EtaMatchReturnsFun.

Definition tbl : list (nat * (nat -> nat)) := cons (0, fun x => x) (cons (1, S) nil).

Fixpoint lookup (l : list (nat * (nat -> nat))) (k : nat) : nat -> nat :=
  match l with
  | nil => fun x => x
  | cons p r => if Nat.eqb (fst p) k then snd p else lookup r k
  end.

Definition test := lookup tbl 1 5.

End EtaMatchReturnsFun.

Crane Extraction "eta_match_returns_fun" EtaMatchReturnsFun.
