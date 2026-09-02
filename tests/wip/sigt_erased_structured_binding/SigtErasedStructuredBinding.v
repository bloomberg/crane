From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module SigtErasedStructuredBinding.

(** Destructuring the pair payload of a [sigT] emits a C++ structured binding
    applied directly to the [std::any] that [projT2()] returns:

      auto [x, f] = i.projT2();

    error: cannot bind private member '__h_' of 'std::any'
    error: type 'std::any::_Storage' does not provide a call operator
           (crane_fn.h:148)

    The payload has to be [any_cast] to [std::pair<std::any, std::any>] first. *)

Definition item := { T : Type & (T * (T -> nat))%type }.

Definition mkitem {T} (x : T) (f : T -> nat) : item := existT _ T (x, f).

Definition score (i : item) : nat := let (x, f) := projT2 i in f x.

Definition total (l : list item) : nat := fold_left (fun a i => a + score i) l 0.

Definition ex : list item := cons (mkitem 3 (fun n : nat => n)) nil.

Definition run : nat := total ex.

End SigtErasedStructuredBinding.

Crane Extraction "sigt_erased_structured_binding" SigtErasedStructuredBinding.run.
