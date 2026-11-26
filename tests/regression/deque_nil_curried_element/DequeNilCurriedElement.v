(** Found by Ephyra round 28. Under [Mapping.DequeList], a list literal
    (here [nil]; a non-empty literal of lambdas failed the same way) whose
    element type is a function transformer, [(nat -> nat) -> nat -> nat],
    passed to a polymorphic function ([hd_or]) whose result is the step of
    [twice]. The template argument was spelled curried,
    [hd_or<crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<...>)>>], but
    the mapped list's element type flat,
    [std::deque<crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>,
    uint64_t)>>], so deduction failed ("no matching function for call to
    'hd_or'"); the typed-fit check reported it (argument, unrelated).

    Fixed: an argument the parameter states nothing more of is built at the
    parameter at the call's grouping ([Calls.argument_position]); a custom
    constructor takes a function type its destination groups otherwise at
    the destination's grouping, in its type arguments, its fields and the
    closure it names ([Construction.gen_expr_custom_cons],
    [Constructors.custom], [Constructors.custom_field]), and a nullary one
    is typed at the instantiation it was built at. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

Module DequeNilCurriedElement.

Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (hd_or (fun (g : nat -> nat) (n : nat) => g n + 7) (@nil ((nat -> nat) -> nat -> nat)))
    (fun n : nat => n * 2) 3.

End DequeNilCurriedElement.

Crane Extraction "deque_nil_curried_element" DequeNilCurriedElement.
