(** Found by Ephyra round 25. A list of functions whose result type is a
    function-type alias ([st A := nat -> A * nat]), passed to a polymorphic
    function at [A := nat -> st nat]. The template argument keeps the alias,
    [hd_or<crane::fn<st<uint64_t>(uint64_t)>>], but the list literal spells its
    element type flat through the alias, [List<crane::fn<std::pair<uint64_t,
    uint64_t>(uint64_t, uint64_t)>>], and the one-argument lambda does not
    convert to the two-argument [crane::fn]. Under CRANE_CHECK_IR the typed-fit
    check reports the same disagreement (argument, convert, list <- list).
    Expected: compiles, [result = 705]. Actual: "no viable conversion from
    '(lambda ...)' to 'crane::fn<std::pair<unsigned long long, unsigned long
    long> (unsigned long long, unsigned long long)>'". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module FnListStateAliasFit.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).
Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition h (k : nat) : st nat := hd_or (fun _ : nat => sret 0) [fun j : nat => sret (j + k)] 4.
Definition result : nat := let (a, s) := h 3 5 in a * 100 + s.

End FnListStateAliasFit.

Crane Extraction "fn_list_state_alias_fit" FnListStateAliasFit.
