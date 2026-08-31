(** An existential whose witness type is erased to [std::any], instantiated at
    an enum-like inductive.  The callback body switches directly on the erased
    scrutinee instead of casting it first:

    {v
      statement requires expression of integer type ('const std::any' invalid)
      value of type 'Bool0' is not implicitly convertible to 'int'
    v} *)

Require Crane.Extraction.

Module ErasedEnumSwitch.

Inductive dep : Type := D : forall A : Type, A -> (A -> nat) -> dep.

Definition run (d : dep) : nat := match d with D _ x f => f x end.

Definition test : nat :=
  run (D nat 5 (fun n => n)) + run (D bool true (fun b => if b then 1 else 0)).

End ErasedEnumSwitch.

Crane Extraction "erased_enum_switch" ErasedEnumSwitch.
