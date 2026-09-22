From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import template_merge_outlined_member.A.

Module Tally.
  (** The back edge, inside the very module the method body names: a by-value
      [box nat] field, so this struct needs [box] complete and cannot be moved
      in front of it. *)
  Record boxed : Set := Mk {unbox : box nat}.

  (** No [box] argument, so it stays in this struct rather than being promoted
      onto the datatype. *)
  Definition bump (n : nat) : nat := S n.
End Tally.

Definition roundtrip (x : box nat) : box nat := Tally.unbox (Tally.Mk x).
