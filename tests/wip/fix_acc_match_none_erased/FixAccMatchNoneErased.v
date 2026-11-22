(** Found by Ephyra (round 21). A variant of round 20's
    [fix_acc_empty_erased] that its fix does not cover: the local
    fixpoint's initial accumulator is a [match] whose branches build
    [(None, k)], and the result is used (not discarded).

    Expected: compiles; [result = 2]: over the one-string list both calls
    return [(None, 1)].

    Actual: compile error "no matching function for call to object of type
    'crane::fn<std::pair<std::optional<std::string>, uint64_t>
    (List<std::string>, std::pair<std::optional<std::string>, uint64_t>)>'":
    the match becomes a conditional expression whose [None]s are built as
    [std::optional<crane::obj>()], so the pair does not convert. Also on
    main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
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
