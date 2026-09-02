From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module SubmoduleNamedNat.

(** A submodule named [Nat] becomes a nested struct that shadows the runtime
    [Nat] for every unqualified lookup inside its parent, so the runtime type
    must be spelled [::Nat]:

      ::Nat SubmoduleNamedNat::Nat::succ(::Nat n)

    Unlike [shadow_runtime_nat], the shadowing name here is a *module*, which
    carries no [GlobRef.t] of its own. *)

Module Nat.
  Definition succ (n : nat) : nat := S n.
End Nat.

Definition run (n : nat) : nat := Nat.succ n.

End SubmoduleNamedNat.

Crane Extraction "submodule_named_nat" SubmoduleNamedNat.
