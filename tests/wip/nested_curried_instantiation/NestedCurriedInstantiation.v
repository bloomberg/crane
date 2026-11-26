(** Found by Ephyra round 28. A list literal of lambdas whose element type is
    a function transformer, [(nat -> nat) -> nat -> nat], passed to a
    polymorphic function ([hd_or]) whose result is the step of [twice]. The
    list's element type is spelled curried,
    [List<crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<...>)>>], but each
    element lambda is written flat, taking [(crane::fn<uint64_t(uint64_t)>,
    uint64_t)], and does not convert to the one-argument [crane::fn]. The
    typed-fit check finds nothing. Without [twice] (the same [hd_or] call
    applied to its two arguments directly) it compiles. [result2] shows the
    same with a plain two-argument element type under [map]; [result3] a
    [fold_left] step at the transformer type (no matching member function
    for call to 'fold_left'). Kin of round 25's
    [pick_curried_fn_overapply] and [fn_list_state_alias_fit] (both fixed).
    Expected: compiles, [result = 8], [result2 = 44], [result3 = 7]. Actual: "no viable conversion from
    '(lambda ...)' to 'crane::fn<crane::fn<unsigned long long (unsigned long
    long)> (crane::fn<unsigned long long (unsigned long long)>)>'". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module NestedCurriedInstantiation.

Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (hd_or (fun (g : nat -> nat) (n : nat) => n) [fun (g : nat -> nat) (n : nat) => g n + 1])
    (fun n : nat => n * 2) 3.

(** No transformer needed: a two-argument element, [bool -> nat -> nat], at an
    instantiation [map] reads as [bool -> (nat -> nat)]. *)
Definition result2 : nat :=
  fold_left (fun a f => a + f 4)
    (map (hd_or (fun (_ : bool) (n : nat) => n) [fun (b : bool) (n : nat) => if b then n * 10 else n])
       [true; false]) 0.

(** The same under a fold: [fold_left]'s step, at the transformer type, takes
    its accumulator as the flat [crane::fn<uint64_t(crane::fn<...>,
    uint64_t)>] and returns a flat two-argument lambda, while the member
    [fold_left]'s template argument is the curried type. *)
Definition result3 : nat :=
  twice (fold_left (fun (acc : (nat -> nat) -> nat -> nat) (e : nat) (g : nat -> nat) (n : nat) => g n + e)
           [1; 2] (fun (g : nat -> nat) (n : nat) => g n + 1))
    (fun n : nat => n) 3.

End NestedCurriedInstantiation.

Crane Extraction "nested_curried_instantiation" NestedCurriedInstantiation.
