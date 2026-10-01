(** A class demoted to a struct, {e constructed} rather than only mentioned.

    [tests/regression/class_field_type_via_section_inductive] established that
    a class is parameterised by the promoted variables it mentions but does
    not declare, and threaded those arguments onto every use the {e type}
    printer writes: the concept constraint, the instance's [static_assert],
    the alias, the declaration's return type.

    A class used as data is demoted from a concept to a struct
    (see the [record-value-typeclass-demotion] note), and a struct is also
    {e built}.  A constructor call is a type mention that does not go through
    the type printer, so the threading cannot have seen it: the declaration
    says [ToDvalueBase<ptr, iptr, I>] and the [return ToDvalueBase<Nat>{...}]
    beside it says one argument.

    Reduced from the Vellvm-side session's install #14, which reported exactly
    this split within one function --- return type arity 3, return statement
    arity 1. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params := { ptr : Type ; iptr : Type ; nullp : ptr ; zeroi : iptr }.

Section DValue.
  Context {Pa : Params}.

  Variant dvalue_base : Type :=
    | DVALUE_Pointer : ptr -> dvalue_base
    | DVALUE_Iptr : iptr -> dvalue_base.

  Class ToDvalueBase (I : Type) : Type := { tdb : I -> dvalue_base }.

End DValue.

#[global] Instance natParams : Params :=
  {| ptr := nat ; iptr := nat ; nullp := 0 ; zeroi := 0 |}.

(** Built and returned, so the class is data here and the struct is
    constructed in an expression position. *)
Definition mk_to_base {Pa : Params} {I : Type} (f : I -> dvalue_base)
  : ToDvalueBase I := {| tdb := f |}.

Definition apply_to_base {Pa : Params} {I : Type} (d : ToDvalueBase I) (x : I)
  : dvalue_base := @tdb Pa I d x.

Module ClassValueCtorDropsPromoted.
  Definition run : dvalue_base :=
    apply_to_base (mk_to_base (fun n : nat => DVALUE_Iptr n)) 7.
End ClassValueCtorDropsPromoted.
Crane Extraction "class_value_ctor_drops_promoted" ClassValueCtorDropsPromoted.
