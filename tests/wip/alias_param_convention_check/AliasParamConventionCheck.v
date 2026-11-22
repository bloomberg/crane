(** Found by Ephyra round 23 (there: module types' [t := nat * bool]).
    A parameter whose type is a type alias of a pair, [op1 (u : t1)] with
    [t1 := nat * bool]. The tests run with [CRANE_CHECK_IR=1], and the
    parameter-convention check rejects the declaration. The emitted C++,
    [uint64_t P::op1(P::t1 x0_)], takes it by value, which is what the Core
    type says; the check apparently reads the alias [t1] as a lent type.
    Expected: extracts, [result = 4].
    Actual: "Crane IR check (parameter convention): the Core type of a
    parameter says it is copied, its C++ type the other". Typed-mappings
    regression: main, with [CRANE_CHECK_IR=1], extracts it. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.

Module AliasParamConventionCheck.

Definition t1 : Type := (nat * bool).

Definition op1 (u : t1) : nat := fst u.

Definition result : nat := op1 (4, true).

End AliasParamConventionCheck.

Crane Extraction "alias_param_convention_check" AliasParamConventionCheck.
