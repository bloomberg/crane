(** Found by Ephyra (round 20). Under [Mapping.DequeList] (list as
    [std::deque]), a local fixpoint over a list of primitive strings with a
    [nat * list nat] accumulator, called with the literal [(0, [])], in a
    position whose result is discarded ([let (p, q) := ... in nil]).

    Expected: compiles; [t_1 = 0].

    Actual: compile error "no matching function for call to object of type
    'crane::fn<std::pair<uint64_t, std::deque<uint64_t>>
    (std::deque<std::string>, std::pair<uint64_t, std::deque<uint64_t>>)>'":
    the initial accumulator's empty list is printed
    [std::deque<crane::obj>{}], its element type erased, so the pair does
    not convert. With a list of [bool] instead of strings it compiles. Also
    on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std Mapping.DequeList.
From Crane Require Extraction.
From Stdlib Require Import List Ascii.
From Corelib Require Import PrimString.
Import ListNotations.
Module DequeNilErased.
Definition t_1 : nat :=
  List.length
    (let (p, q) :=
       (let fix go (l : list PrimString.string) (acc : nat * list nat) {struct l} : nat * list nat :=
          match l with [] => acc | _ :: _ => (0, []) end in
        go [""%pstring] (0, [])) in
     @nil ascii).
End DequeNilErased.
Crane Extraction "deque_nil_erased" DequeNilErased.
