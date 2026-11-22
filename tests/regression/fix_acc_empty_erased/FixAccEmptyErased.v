(** Found by Ephyra (round 20). A local fixpoint over a list of primitive
    strings whose accumulator holds an [option] or a list, called with a
    literal [(None, 0)] or [(0, [])], in a position whose result is
    discarded ([let (p, q) := ... in nil]).

    Expected: compiles; [t_opt = 0] and [t_deque = 0].

    Fixed: compile error "no matching function for call to object of type
    'crane::fn<...>'": the initial accumulator's [None] was printed
    [std::optional<crane::obj>] (under [Mapping.DequeList] the empty list
    likewise as [std::deque<crane::obj>{}]): extraction leaves its type
    argument erased, and an argument of a local function's call was
    generated with no slot, so nothing refined it. A constructed argument is
    now generated against the callee's parameter, its Core type read from
    the binder's recorded type for a local function. *)
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
