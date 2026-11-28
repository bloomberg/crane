(** Found by Ephyra round 31.  A polymorphic helper instantiated at a
    function type and handed to [id], whose argument is a box: the lambda
    argument of the helper is a closure whose result its body does not
    write ([auto]).  The C++ was right, but under [CRANE_CHECK_IR] the
    typed fit check found [closure (nat)->auto] unrelated to the slot
    [fn(nat)->nat] and stopped extraction.

    Fixed: [auto], a type C++ deduces, is undecided in [Coerce.unrelated],
    as a box is. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module FitClosureAutoResult.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition pick {A : Type} (b : bool) (x y : A) : A := if b then x else y.
Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition nth_or {A : Type} (l : list A) (n : nat) (d : A) : A := nth n l d.

Definition via_hd_or : nat := (id (hd_or (fun _ : nat => 3) (@nil (nat -> nat)))) 0.
Definition via_twice : nat :=
  (id (twice (fun _ : nat -> nat => fun _ : nat => 4) (fun _ : nat => 0))) 0.
Definition via_nth_or : nat :=
  px ((id (nth_or (@nil (nat -> pt)) 0 (fun _ : nat => mkpt 5 true))) 0).
Definition via_pick : bool :=
  (id (pick true (fun _ : nat => true) (fun _ : nat => false))) 0.

End FitClosureAutoResult.

Crane Extraction "fit_closure_auto_result" FitClosureAutoResult.
