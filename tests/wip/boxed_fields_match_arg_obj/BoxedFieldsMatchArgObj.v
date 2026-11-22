(** Found by Ephyra round 23. Under [Set Crane BoxedFields], a match on a
    nat passed as the [list (option nat)] argument of a local fixpoint that
    walks a [list PrimString.string] is lowered to an immediately invoked
    lambda declared [-> List<std::optional<crane::obj>>] whose branches
    return [List<std::optional<uint64_t>>]; [go] itself takes
    [List<std::optional<uint64_t>>].
    Expected: [count 0 = 0], [count 3 = 1].
    Actual: C++ compile error in obj.h ("substitution into constraint
    expression resulted in a non-constant expression") converting the
    branch value to [List<std::optional<crane::obj>>]. Without BoxedFields,
    or with a [list nat] walked instead of strings, it compiles. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.
Set Crane BoxedFields.

Module BoxedFieldsMatchArgObj.

Definition count (n : nat) : nat :=
  List.length (let fix go (l : list PrimString.string) (acc : list (option nat))
                   {struct l} : list (option nat) :=
    match l with [] => acc | _ :: r => go r acc end
  in go ["a"%pstring] (match n with O => [] | S _ => [None] end)).

End BoxedFieldsMatchArgObj.

Crane Extraction "boxed_fields_match_arg_obj" BoxedFieldsMatchArgObj.
