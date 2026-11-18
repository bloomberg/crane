From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint returning a function, called with literal arguments so
    the call is inlined (the beta-redex form in local_fix_returns_function is
    fixed).
    - [t]: under an applied observer, "no matching function for call to object
      of type 'const (lambda ...)'".
    - [u]: a branch returning a lambda next to one returning the accumulator:
      "return type '(lambda ...)' must match previous return type
      'crane::fn<bool (uint64_t)>'". *)
Module LocalFixFunctionResultInlined.

Definition t : nat :=
  (fun w : list nat -> bool => if w [] then 1 else 2)
  (let fix go (l : list nat) (acc : list nat -> bool) {struct l} : list nat -> bool :=
     match l with [] => (fun _ => true) | _ :: r => go r acc end in go [] (fun _ => false)).

Definition u : bool :=
  fst (let fix go (l : list nat) (acc : nat -> bool) {struct l} : nat -> bool :=
     match l with [] => acc | _ :: _ => (fun _ => true) end in go [] (fun _ => false), true) 0.

End LocalFixFunctionResultInlined.

Crane Extraction "local_fix_function_result_inlined" LocalFixFunctionResultInlined.
