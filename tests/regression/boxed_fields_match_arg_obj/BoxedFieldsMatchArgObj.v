(** Found by Ephyra round 23. Under [Set Crane BoxedFields], a match on a
    nat passed as the [list (option nat)] argument of a local fixpoint that
    walks a [list PrimString.string].
    Expected: [count 0 = 0], [count 3 = 1].
    Fixed: C++ compile error in obj.h ("substitution into constraint
    expression resulted in a non-constant expression"). The match was an
    immediately invoked lambda declared [-> List<std::optional<crane::obj>>]
    from the match's annotation, which erased the option's payload, while
    its branches built [List<std::optional<uint64_t>>] at the parameter's
    type. The lambda's return type is now the annotation refined by the
    slot, as the branches' values are. *)
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
