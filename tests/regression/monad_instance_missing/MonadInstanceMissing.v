(** Crane bug: a top-level typeclass instance is qualified with the extraction
    module's name at its use sites.

    [EOU_monad] is defined at top level and emitted there, correctly:

      struct EOU_monad { ... };
      static_assert(Monad<EOU_monad>);

    but every use inside the extracted module names it as a member of that
    module:

      Monad::template bind<MonadInstanceMissing::EOU_monad, Nat, Nat>(...)

    Expected: [Monad::template bind<EOU_monad, Nat, Nat>(...)].
    Actual:   error: no member named 'EOU_monad' in 'MonadInstanceMissing' (x2)

    Seen in Vellvm as "use of undeclared identifier 'EOU_monad'", 26 times.

    The [Crane Extraction Blacklist Monad] line is needed to keep this test
    down to one bug; without it the module/concept name collision in
    [monad_name_collision] fires first. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.

Crane Extraction Blacklist Monad.

Import MonadNotation.
Open Scope monad.

Variant EOU {X : Type} : Type :=
  | raise_error (s : nat) : EOU
  | raise_ret (x : X) : EOU.
Arguments EOU : clear implicits.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := @raise_ret ;
     bind _ _ c k :=
       match c with
       | raise_error s => raise_error s
       | raise_ret x => k x
       end
  |}.

Definition double (n : nat) : EOU nat := ret (n + n).

Module MonadInstanceMissing.

  Definition use (n : nat) : EOU nat :=
    x <- double n ;; ret (S x).

End MonadInstanceMissing.

Crane Extraction "monad_instance_missing" MonadInstanceMissing.
