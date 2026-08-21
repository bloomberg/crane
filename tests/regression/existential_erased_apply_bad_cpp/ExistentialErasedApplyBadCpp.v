From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module ExistentialErasedApplyBadCpp.

(** [dyn] packages a value with a consumer for it, hiding the value's type.
    The quantified [A] has no C++ counterpart, so both the value field and
    the consumer's argument erase to [std::any].

    The consumer is emitted with the erased signature it actually has --
    [const std::any &] in, [uint64_t] out. For the identity [fun k => k] the
    erased [std::any] used to be returned directly, with no [any_cast] back
    to the concrete return type:

      [](const std::any &k) -> uint64_t { return k; }

    which does not compile. The other two consumers were already fine: they
    use their argument at a site with a known expected type ([.first], a
    method call), which is where the cast was being inserted. A bare [return]
    has no such site, so the lambda's declared return type is now threaded
    through as the expected type there. *)
Inductive dyn : Type := Dyn : forall (A : Type), A -> (A -> nat) -> dyn.

Definition force (d : dyn) : nat :=
  match d with Dyn _ x f => f x end.

Definition mk (n : nat) : list dyn :=
  [ Dyn nat n (fun k => k)
  ; Dyn (nat * nat) (n, S n) (fun p => fst p + snd p)
  ; Dyn (list nat) [n; n; n] (fun l => length l) ].

Fixpoint total (l : list dyn) : nat :=
  match l with [] => 0 | d :: r => force d + total r end.

Definition run (n : nat) : nat := total (mk n).

End ExistentialErasedApplyBadCpp.

Crane Extraction "existential_erased_apply_bad_cpp" ExistentialErasedApplyBadCpp.
