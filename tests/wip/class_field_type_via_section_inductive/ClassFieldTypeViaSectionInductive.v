(** A class whose dependence on another class is carried by a {e third} type.

    [ToDvalueBase] in Vellvm takes one parameter, [I], and declares one field
    whose type is [dvalue_base].  [dvalue_base] is a [Variant] declared in the
    same [Section] as a [Context {Pa : Params}], so discharge turns it into
    [Dvalue_base<ptr, iptr>] --- and those two names are fields of [Params],
    which [ToDvalueBase] never mentions.  The dependence is real, it is present
    in the discharged C++ type, and it appears nowhere in the class's own
    signature.

    {b Why [Gen_decls.promoted_resolutions] loses it, stated before the fix.}
    That function has two sources.  [class_promoted_vars class_ref] gives the
    class's own promoted variables, and [ToDvalueBase] has none --- [I] is an
    ordinary parameter.  The nested branch fires only on a field whose type is
    [Tglob (r, _, _)] with [Table.is_typeclass r], and [dvalue_base] is an
    inductive.  So both sources come up empty, every name in the field's type
    is unresolved, and [ptr] and [iptr] fall through to the file-scope
    [using ptr = std::any;].

    That is a {e third} way to lose a resolution, and neither docstring at the
    site records it.  The two that are recorded are "promotion was required
    here and the class contributed none" ([promoted_resolutions]) and "the
    owner was given concretely, so the path is gone while the name survives"
    ([class_arg_type]).  This one is "the dependence is carried by a non-class
    type in the field, where nothing looks".

    Contrast [tests/wip/hk_class_field_result_cast_to_concept], which put the
    dependence in an explicit [Context] on a definition and did {e not}
    reproduce this: there every position resolved correctly.  Paraphrasing a
    dependence is not reproducing it; the [Variant] in the section is the
    load-bearing part.

    Reduced from the Vellvm-side session's [ToDvalueBase] source (h:12843). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params := { ptr : Type ; iptr : Type ; nullp : ptr ; zeroi : iptr }.

Section DValue.
  Context {Pa : Params}.

  (** Declared in the section, so discharge parameterises it by [ptr] and
      [iptr].  This is what carries [Params] into the class below. *)
  Variant dvalue_base : Type :=
    | DVALUE_Pointer : ptr -> dvalue_base
    | DVALUE_Iptr : iptr -> dvalue_base.

  (** Takes only [I].  Its field's type is the section inductive, so its
      dependence on [Params] is never written down. *)
  Class ToDvalueBase (I : Type) : Type := { tdb : I -> dvalue_base }.

End DValue.

Definition to_base {Pa : Params} {I : Type} `{ToDvalueBase I} (x : I)
  : dvalue_base := tdb x.

#[global] Instance natParams : Params :=
  {| ptr := nat ; iptr := nat ; nullp := 0 ; zeroi := 0 |}.

#[global] Instance natToBase : ToDvalueBase nat :=
  {| tdb := fun n => DVALUE_Iptr n |}.

Module ClassFieldTypeViaSectionInductive.
  Definition run : dvalue_base := to_base 7.
End ClassFieldTypeViaSectionInductive.
Crane Extraction "class_field_type_via_section_inductive" ClassFieldTypeViaSectionInductive.
