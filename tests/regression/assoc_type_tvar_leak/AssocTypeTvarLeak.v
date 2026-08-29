From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AssocTypeTvarLeak.
  (** An associated [Type] used as a list element type.  The instance body's
      embedded types must be resolved to the instance's concrete choice, or
      they would render as the class's template parameter [T1], which is not
      in scope inside the instance struct. *)
  Class Elt :=
    { E : Type ; e0 : E ; elist : list E ; ecount : list E -> nat }.

  Instance EN : Elt :=
    { E := nat
    ; e0 := 0
    ; elist := [1; 2; 3]
    ; ecount := fun l => fold_left Nat.add l 0 }.

  Definition go `{Elt} : nat := ecount (e0 :: elist).

  Definition run (k : nat) : nat := go + k.
End AssocTypeTvarLeak.

Crane Extraction "assoc_type_tvar_leak" AssocTypeTvarLeak.
