(** A [let]-bound local [fix] that is partially applied.

    Crane eta-expands the remaining parameter but types the wrapper's parameter
    from the wrong position of the fix's signature, so the wrapper cannot call
    the function it wraps:

    {v
      no matching function for call to object of type '(lambda ...)'
    v} *)

Require Crane.Extraction.

Module PartialLocalFix.

Definition run : bool -> nat :=
  let loop :=
    fix loop (n : nat) (b : bool) : nat :=
      match n with
      | 0 => 0
      | S k => if b then S (loop k b) else loop k b
      end
  in loop 8.

Definition test : nat := run true.

End PartialLocalFix.

Crane Extraction "partial_local_fix" PartialLocalFix.
