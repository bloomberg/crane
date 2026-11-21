(** Found by Ephyra (round 20). A local fixpoint over a list of primitive
    strings whose accumulator holds an [option] or a list, called with a
    literal [(None, 0)] or [(0, [])], in a position whose result is
    discarded ([let (p, q) := ... in nil]).

    Expected: compiles; [t_opt = 0] and [t_deque = 0].

    Actual: compile error "no matching function for call to object of type
    'crane::fn<std::pair<std::optional<uint64_t>, uint64_t>
    (List<std::string>, std::pair<std::optional<uint64_t>, uint64_t>)>'":
    the initial accumulator's [None] is printed [std::optional<crane::obj>]
    (under [Mapping.DequeList] the empty list likewise as
    [std::deque<crane::obj>{}]), its payload type erased, so the pair does not
    convert to the fixpoint's parameter. Over a list of [nat] or [bool] it
    compiles. Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std Mapping.DequeList.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.

Module FixAccEmptyErased.

Definition t_opt : nat :=
  List.length
    (let (p, q) :=
       (let fix go (l : list PrimString.string) (acc : option nat * nat) {struct l}
              : option nat * nat :=
          match l with [] => acc | _ :: _ => (None, 0) end in
        go [""%pstring] (None, 0)) in
     @nil bool).

Definition t_deque : nat :=
  List.length
    (let (p, q) :=
       (let fix go (l : list PrimString.string) (acc : nat * list nat) {struct l}
              : nat * list nat :=
          match l with [] => acc | _ :: _ => (0, []) end in
        go [""%pstring] (0, [])) in
     @nil bool).

End FixAccEmptyErased.

Crane Extraction "fix_acc_empty_erased" FixAccEmptyErased.
