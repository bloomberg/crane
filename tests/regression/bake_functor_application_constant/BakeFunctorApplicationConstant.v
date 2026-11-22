(** Found by Ephyra round 23 (a probe extending the generator to modules
    and [Crane Bake]). [Crane Bake] of [FN.vals], a constant of a functor
    application [Module FN := F N], and of [GN.vals] through an alias of
    one.
    Expected: either [vals] is baked or [Crane Bake] refuses it with a
    [Crane Bake: ...] diagnostic, as docs/Crane-Bake.md does for a
    constant inside a functor; [total = 18] either way.
    Fixed: the check accepted it (it is not syntactically inside a
    functor), but the extraction prints [FN] as [using FN = F<N>;] and
    [vals] as a member of the template [F] that the bake driver never
    instantiates, so no root was registered: "Crane Bake: the bake driver
    failed (exit code 2): crane::bake: usage: <out> <symbol> <prefix>, with
    a root". An image cannot initialise one instantiation's member, so the
    check now refuses a constant declared in a functor application
    (following aliases), and [total] is computed at startup. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module BakeFunctorApplicationConstant.

Module Type T.
  Parameter t : Type.
  Parameter mk : nat -> t.
  Parameter obs : t -> nat.
End T.

Module N <: T.
  Definition t := list nat.
  Definition mk (n : nat) : t := repeat n 3.
  Definition obs (x : t) : nat := fold_left Nat.add x 0.
End N.

Module F (X : T).
  Definition vals : list X.t := map X.mk [1; 2; 3].
  Definition total : nat := fold_left (fun a v => a + X.obs v) vals 0.
End F.

Module FN := F N.
Module GN := FN.

Definition total : nat := FN.total.

End BakeFunctorApplicationConstant.

Fail Crane Bake BakeFunctorApplicationConstant.FN.vals.
Fail Crane Bake BakeFunctorApplicationConstant.GN.vals.
Crane Extraction "bake_functor_application_constant" BakeFunctorApplicationConstant.
