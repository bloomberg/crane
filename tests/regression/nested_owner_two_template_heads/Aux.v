From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import nested_owner_two_template_heads.A.

Module Tally.
  (** The back edge: a by-value [bag nat] field, so this struct needs [bag]
      complete and cannot be moved in front of it. *)
  Record held : Set := Hold {unhold : bag nat}.

  (** No [bag] argument, so it stays here rather than being promoted onto the
      datatype, and a method body naming it names a struct still to come. *)
  Definition bump (n : nat) : nat := S n.
End Tally.

Definition roundtrip (b : bag nat) : bag nat := Tally.unhold (Tally.Hold b).
