(** Found by Ephyra (round 21). A variant of round 20's
    [fix_acc_empty_erased] that its fix does not cover: the local
    fixpoint's initial accumulator is a [match] whose branches build
    [(None, k)], and the result is used (not discarded).

    Expected: compiles; [result = 2]: over the one-string list both calls
    return [(None, 1)].

    Fixed: compile error "no matching function for call to object of type
    'crane::fn<std::pair<std::optional<std::string>, uint64_t>
    (List<std::string>, std::pair<std::optional<std::string>, uint64_t>)>'":
    the match became a conditional expression whose [None]s were built as
    [std::optional<crane::obj>()], so the pair did not convert.  Only an
    argument that was itself a constructor took the callee parameter's Core
    type as its slot; now every argument does, and the forms that hand
    their slot on (match branches, let bodies, constructor fields) carry it
    to the value built inside. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.
Module FixAccMatchNoneErased.
Definition run (n : list nat) : option PrimString.string * nat :=
  let fix go (l : list PrimString.string) (acc : option PrimString.string * nat) {struct l}
        : option PrimString.string * nat :=
    match l with [] => acc | _ :: _ => (None, 1) end in
  go [""%pstring] (match n with [] => (None, 2) | _ :: _ => (None, 3) end).
Definition result : nat := snd (run []) + snd (run [5]).
End FixAccMatchNoneErased.
Crane Extraction "fix_acc_match_none_erased" FixAccMatchNoneErased.
