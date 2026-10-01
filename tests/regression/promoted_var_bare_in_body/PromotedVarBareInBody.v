(** A promoted variable resolved in a signature but left bare in the body.

    Inside a function whose only template parameter is the [Params] instance,
    the signature spells [typename _tcI0::iptr] -- resolved against the
    instance -- while the body spells the same variable as the bare [iptr],
    which at namespace scope is the file-scope [using iptr = std::any;].
    So the lambda's binder and the value it builds are at [std::any], and
    neither converts to the type the signature promised.

    Reported by the Vellvm-side session at install #16, in
    [DynamicValues::ToDvalue_Int] / [ToDvalue_iptr]: the return type is
    [ToDvalueBase<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr, ...>]
    and the body returns [Dvalue_base<ptr, iptr>::dvalue_i(sz, x)]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params := { ptr : Type ; iptr : Type ; nullp : ptr ; zeroi : iptr }.

Section DValue.
  Context {Pa : Params}.

  Variant dvalue_base : Type :=
    | DVALUE_Pointer : ptr -> dvalue_base
    | DVALUE_Iptr : iptr -> dvalue_base.

  Class ToDvalueBase (I : Type) : Type := { tdb : I -> dvalue_base }.

  (** Takes an argument, so it is a function returning the class as a value
      rather than an instance; its body builds a [dvalue_base] and binds an
      [iptr]. *)
  Definition to_iptr (fallback : iptr) : ToDvalueBase iptr :=
    {| tdb := fun x => DVALUE_Iptr x |}.

End DValue.

#[global] Instance natParams : Params :=
  {| ptr := nat ; iptr := nat ; nullp := 0 ; zeroi := 0 |}.

Module PromotedVarBareInBody.
  Definition run : dvalue_base := @tdb natParams nat (@to_iptr natParams 0) 7.
End PromotedVarBareInBody.
Crane Extraction "promoted_var_bare_in_body" PromotedVarBareInBody.
