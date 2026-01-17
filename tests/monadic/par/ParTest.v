(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.Par.

Import ParNotations.

Module partest.

  Definition ack (p : nat * nat) : nat :=
    let fix f (m n : nat) : nat :=
      (fix ack_m (n : nat) : nat :=
        match m with
          | 0 => S n
          | S pm =>
            match n with
              | 0 => f pm Nat.one
              | S pn => f pm (ack_m pn)
            end
        end) n in
    f (fst p) (snd p).

  Definition fast (m n : nat) : nat * nat :=
    let f _ :=
    let p := (m, n) in
    t1 <- mk_thread ack p ;;
    t2 <- mk_thread ack p ;;
    r1 <- get_thread t1 ;;
    r2 <- get_thread t2 ;;
    Pret (r1, r2) in
    runPar f.

  Definition slow (m n : nat) : nat * nat :=
    let p := (m, n) in
    let r1 := ack p in
    let r2 := ack p in
    (r1, r2).

End partest.

Crane Extraction TestCompile "par" partest.
