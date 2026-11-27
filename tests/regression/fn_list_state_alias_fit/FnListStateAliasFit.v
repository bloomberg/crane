(** Found by Ephyra round 25. A list of functions whose result type is a
    function-type alias ([st A := nat -> A * nat]), passed to a polymorphic
    function at [A := nat -> st nat]. The template argument kept the alias,
    [hd_or<crane::fn<st<uint64_t>(uint64_t)>>], but the list literal was
    built at its own annotation, which Rocq wrote with the alias unfolded
    ([list (nat -> nat -> nat * nat)]), as [List<crane::fn<std::pair<uint64_t,
    uint64_t>(uint64_t, uint64_t)>>]; the one-argument lambda did not convert
    to the two-argument [crane::fn] ("no viable conversion"), and the
    typed-fit check refused the list (argument, convert).

    Fixed: a constructed argument whose annotation is the parameter's type
    grouped otherwise once function aliases are unfolded is built at the
    parameter's type ([Calls.argument_position],
    [Types.regrouped_through_aliases]).  An over-applied call no longer
    reads its callee's variables off its position's type either, which
    states its result applied to the excess arguments
    ([Calls.plan_call]'s [result_tvar_map]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
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
