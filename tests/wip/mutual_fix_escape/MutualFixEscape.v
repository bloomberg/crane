From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module MutualFixEscape.

(** Mutual fixpoints escaped through a pair. Each fixpoint calls the
    other, so in C++ both std::functions cross-reference each other
    via [&] capture. After the defining scope, both std::functions
    and all captured variables are destroyed.

    This is different from single fixpoints: the generated C++ must
    create TWO std::function variables that reference each other.
    The [&] capture creates a cycle of dangling references. *)

(** Mutual fixpoint using fix...with...for syntax, then return
    both functions through a pair. *)
Definition make_even_odd (base : nat)
  : (nat -> bool) * (nat -> bool) :=
  let eo :=
    fix even (n : nat) : bool :=
      match n with
      | O => true
      | S n' => odd n'
      end
    with odd (n : nat) : bool :=
      match n with
      | O => false
      | S n' => even n'
      end
    for even
  in
  let od :=
    fix even (n : nat) : bool :=
      match n with
      | O => true
      | S n' => odd n'
      end
    with odd (n : nat) : bool :=
      match n with
      | O => false
      | S n' => even n'
      end
    for odd
  in (eo, od).

(** test1: even(4) = true, odd(3) = true. 1+1=2. *)
Definition test1 : nat :=
  let '(ev, od) := make_even_odd 0 in
  (if ev 4 then 1 else 0) + (if od 3 then 1 else 0).

(** test2: even(5) = false, odd(6) = false. 0+0=0. *)
Definition test2 : nat :=
  let '(ev, od) := make_even_odd 0 in
  (if ev 5 then 1 else 0) + (if od 6 then 1 else 0).

(** A mutual fixpoint that captures a parameter [base]. *)
Definition make_count_pair (base : nat)
  : (nat -> nat) * (nat -> nat) :=
  let ce :=
    fix count_even (n : nat) : nat :=
      match n with
      | O => base
      | S n' => 1 + count_odd n'
      end
    with count_odd (n : nat) : nat :=
      match n with
      | O => base * 2
      | S n' => 1 + count_even n'
      end
    for count_even
  in
  let co :=
    fix count_even (n : nat) : nat :=
      match n with
      | O => base
      | S n' => 1 + count_odd n'
      end
    with count_odd (n : nat) : nat :=
      match n with
      | O => base * 2
      | S n' => 1 + count_even n'
      end
    for count_odd
  in (ce, co).

(** test3: count_even(0) = base = 10. count_odd(0) = 20.
    count_even(3) = 1+count_odd(2) = 1+(1+count_even(1))
                   = 1+(1+(1+count_odd(0))) = 1+1+1+20 = 23.
    Total = 10 + 23 = 33. *)
Definition test3 : nat :=
  let '(ce, co) := make_count_pair 10 in
  ce 0 + ce 3.

(** test4: with noise. count_odd(1) = 1+count_even(0) = 1+5 = 6. *)
Definition test4 : nat :=
  let p := make_count_pair 5 in
  let noise := 1 + 2 + 3 + 4 + 5 in
  snd p 1.

End MutualFixEscape.

Crane Extraction "mutual_fix_escape" MutualFixEscape.
