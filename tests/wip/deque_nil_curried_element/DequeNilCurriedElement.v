(** Found by Ephyra round 28. Under [Mapping.DequeList], a list literal
    (here [nil]; a non-empty literal of lambdas fails the same way) whose
    element type is a function transformer, [(nat -> nat) -> nat -> nat],
    passed to a polymorphic function ([hd_or]) whose result is the step of
    [twice]. The template argument is spelled curried,
    [hd_or<crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<...>)>>], but the
    mapped list's element type is spelled flat,
    [std::deque<crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>>],
    so deduction fails. Without the deque mapping the generic [List] literal
    is spelled curried and the program compiles. Under CRANE_CHECK_IR the
    typed-fit check reports the same disagreement (argument, unrelated,
    list <- list). Variant of [nested_curried_instantiation] (there the generic
    list type is curried and its element lambdas flat; here the mapped list's
    type itself is flat), of round 25's [fn_list_state_alias_fit] and of
    round 24's [mapped_op_curried_element]. Expected: compiles, [result = 20]. Actual:
    "no matching function for call to 'hd_or'". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

Module DequeNilCurriedElement.

Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (hd_or (fun (g : nat -> nat) (n : nat) => g n + 7) (@nil ((nat -> nat) -> nat -> nat)))
    (fun n : nat => n * 2) 3.

End DequeNilCurriedElement.

Crane Extraction "deque_nil_curried_element" DequeNilCurriedElement.
