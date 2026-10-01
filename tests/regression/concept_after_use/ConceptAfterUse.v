From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import ZArith NArith.

(** A class and a function generic over it, in one module.  Crane emits the
    class as a C++ concept [Size], and [walk] as a member template
    [template <Size _tcI0>] of the module's struct -- but the concept is
    printed after that struct, so the template names a concept that is not
    declared yet: "unknown type name 'Size'", and every call to [walk] fails
    with it.  Moving [Size] into a module of its own, as Vellvm's classes are,
    orders the output correctly.

    Found while reducing [borrowed_field_moved_into_method]. *)

Module ConceptAfterUse.

  Inductive ty := TB (n : positive) | TA (sz : N) (t : ty).

  Class Size : Type := { size_of : ty -> N }.

  Section Walk.
    Context {S : Size}.

    Definition walk (t : ty) : N :=
      match t with
      | TA _ ta => size_of ta
      | TB _ => 0%N
      end.
  End Walk.

  Fixpoint sz (t : ty) : N :=
    match t with
    | TB n => N.div (Npos n) 8
    | TA n t => n * sz t
    end%N.

  #[export] Instance SizeI : Size := { size_of := sz }.

  Definition check (_ : unit) : bool := N.eqb (walk (TA 4 (TB 64))) 8.

End ConceptAfterUse.

Crane Extraction "concept_after_use" ConceptAfterUse.
