(** A user inductive named [Nat] shadows Crane's runtime [Nat], so every
    reference to the built-in one resolves to the user's type:

    {v
      return type of out-of-line definition ... differs from that in the declaration
      no member named 'o' in 'ShadowRuntimeNat::Nat'; did you mean '::Nat::o'?
    v} *)

Require Crane.Extraction.

Module ShadowRuntimeNat.

Inductive Nat := O2 : Nat | S2 : Nat -> Nat.

Definition two : Nat := S2 (S2 O2).

Fixpoint toNat (n : Nat) : nat := match n with O2 => 0 | S2 k => S (toNat k) end.

Definition test : nat := toNat two.

End ShadowRuntimeNat.

Crane Extraction "shadow_runtime_nat" ShadowRuntimeNat.
