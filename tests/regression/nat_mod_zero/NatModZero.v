From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NatModZero.
  (** In Rocq, [Nat.modulo n 0 = n] — perfectly defined.
      But NatIntStd maps [Nat.modulo] to [(%a0 % %a1)] with
      no zero guard — unlike [Nat.div] which has one.
      So [my_mod n 0] produces [n % 0u] in C++ — UB (SIGFPE). *)

  Definition my_mod (a b : nat) : nat := Nat.modulo a b.

  (** A "safe" divmod that a Rocq programmer would reasonably write,
      relying on the totality of [Nat.div] and [Nat.modulo].
      In Rocq, [divmod n 0 = (0, n)].
      In C++, the second component triggers UB. *)
  Definition divmod (a b : nat) : nat * nat :=
    (Nat.div a b, Nat.modulo a b).
End NatModZero.

Crane Extraction "nat_mod_zero" NatModZero.
