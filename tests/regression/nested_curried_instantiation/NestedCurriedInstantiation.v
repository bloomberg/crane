(** Found by Ephyra round 28. A list literal of lambdas whose element type is
    a function transformer, [(nat -> nat) -> nat -> nat], passed to a
    polymorphic function ([hd_or]) whose result is the step of [twice]. The
    call wrote its type argument the way the step's slot groups it,
    [List<crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<...>)>>], but
    each element lambda was written flat, taking [(crane::fn<uint64_t
    (uint64_t)>, uint64_t)], and did not convert ("no viable conversion").
    [result2] showed the same with a plain two-argument element type under
    [map]; [result3] a [fold_left] step at the transformer type, built flat
    while the member [fold_left]'s template argument was curried ("no
    matching member function for call to 'fold_left'").

    Fixed: a call's instantiation is read once, each variable at its
    instantiation with a function type grouped as the call's expected
    result writes it ([Calls.grouped_instantiation]), and every argument is
    built at its parameter at that grouping where the two are one type
    grouped otherwise ([Calls.grouped_parameter], in
    [Calls.argument_position]), a methodified callee's receiver variables
    included; a constructor field at a variable is built at the
    constructor's written type argument ([Constructors.regular_field]). *)
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
