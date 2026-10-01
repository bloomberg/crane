(** Crane bug: an instance over a chain of class instances
    ([overlaps_ptoi {P : Provenance} {A : @Pointer P} {Pi : @PI P A}])
    is constrained with the class's *type field* unresolved, so the
    constraint fails at any concrete instance.

    Observed (post-unapplied_subevent_handler install):
      template <Provenance _tcI0, Pointer _tcI1, typename _tcI2>
        requires PI<_tcI2, ptr>          // [ptr] = file-scope std::any fallback
      struct overlaps_ptoi { ... };
    The constraint should read [PI<_tcI2, typename _tcI1::ptr>].
    Diagnostic at the use:
      error: constraints not satisfied for class template 'overlaps_ptoi'
             [with _tcI0 = provNat, _tcI1 = ptrNat, _tcI2 = piNat]
      (Vellvm: "because 'I::ptr_to_int(std::declval<ptr>())' would be
       invalid: no viable conversion from 'std::any' to 'typename
       PointerV<IPZ>::ptr'")

    Reduced from Vellvm, [Semantics/Interfaces/Pointer.v:84]
    ([Instance overlaps_ptoi {P : Provenance} {A : @Pointer P} {PI : @PI P A}
    : @Overlaps P A]), used by [Memory1::memcpy]'s [no_overlap]
    ([requires Pointer<_tcI1, prov> && PI<_tcI2, ptr, prov>]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module InstanceChainConstraint.
  (* Vellvm's Interfaces/Provenance.v and Interfaces/Pointer.v: a chain of
     classes, each over the previous one's instance, with type fields. *)
  Class Provenance : Type := { prov : Type ; wildcard : prov }.
  Class Pointer {P : Provenance} : Type := { ptr : Type ; null : ptr }.
  Class PI {P : Provenance} {A : @Pointer P} : Type := { ptr_to_int : ptr -> nat }.
  Class Overlaps {P : Provenance} {A : @Pointer P} : Type :=
    { overlaps : ptr -> nat -> ptr -> nat -> bool }.

  (* Interfaces/Pointer.v:84 *)
  #[global] Instance overlaps_ptoi {P : Provenance} {A : @Pointer P} {Pi : @PI P A} : @Overlaps P A :=
    {| overlaps a1 sz1 a2 sz2 :=
         let s1 := ptr_to_int a1 in let s2 := ptr_to_int a2 in
         andb (Nat.leb s1 (s2 + sz2 - 1)) (Nat.leb s2 (s1 + sz1 - 1)) |}.

  #[global] Instance provNat : Provenance := { prov := nat ; wildcard := 0 }.
  #[global] Instance ptrNat : @Pointer provNat := { ptr := nat ; null := 0 }.
  #[global] Instance piNat : @PI provNat ptrNat := { ptr_to_int := fun p => p }.

  (* Memory.v's [memcpy]: [no_overlap] through the Overlaps instance. *)
  Definition no_overlap (a1 : nat) (sz1 : nat) (a2 : nat) (sz2 : nat) : bool :=
    negb (@overlaps provNat ptrNat _ a1 sz1 a2 sz2).

  Definition is_ok : bool := andb (no_overlap 0 4 8 4) (negb (no_overlap 0 4 2 4)).
End InstanceChainConstraint.

Crane Extraction "instance_chain_constraint" InstanceChainConstraint.
