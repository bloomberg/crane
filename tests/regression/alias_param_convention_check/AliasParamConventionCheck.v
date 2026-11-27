(** Found by Ephyra (round 23; there: module types' [t := nat * bool]).
    A parameter whose type is a type alias of a pair, [op1 (u : t1)] with
    [t1 := nat * bool], under [CRANE_CHECK_IR=1].

    Expected: extracts, [result = 4].

    Fixed: "Crane IR check (parameter convention): the Core type of a
    parameter says it is copied, its C++ type the other" (a typed-mappings
    regression).  The Core reading unfolded the alias to the typed-mapped
    pair and read it by value, as its read style says; the C++ reading
    unfolded it to the inductive [prod], a value inductive, lent by const
    reference.  Both now read an alias of a typed-mapped type by its
    mapping, and so does the access-driven parameter form. *)
From Crane Require Import Mapping.NatInt.
From Crane Require Import Extraction.

Module AliasParamConventionCheck.

Definition t1 : Type := (nat * bool).

Definition op1 (u : t1) : nat := fst u.

Definition result : nat := op1 (4, true).

End AliasParamConventionCheck.

Crane Extraction "alias_param_convention_check" AliasParamConventionCheck.
