(** Crane bug: a class-typed argument is lifted to a template parameter for a
    free function, but not when the function is emitted as a *member function*
    of its first argument's inductive.

    [show_memory_bit] takes an inductive first and a [Params] second, so Crane
    makes it a member of [Memory_bit].  The call site is already right --

      x0_.template show_memory_bit<_tcI0>()

    -- but the declaration still spells the class as a value parameter, and
    [Params] is a concept:

      Nat show_memory_bit(const Params &pa) const { ... pa.width ... }

    Expected: [template <Params _tcI0> Nat show_memory_bit() const].
    Actual:   error: expected 'auto' or 'decltype(auto)' after concept name
              error: 'pa' is not a class, namespace, or enumeration
              error: unused parameter 'pa' [-Werror,-Wunused-parameter]

    This is what is left of [class_as_value_arg] after d77449c8: that test
    covered a class *method*, and passes now.  Seen in Vellvm 15 times, on the
    members of [memory_bit] and [dvalue_base] under [Context {Pa : Params}] --
    [show_memory_bit], [memory_bit_eq_dec], [dtyp_of_dvalue_base],
    [dvalue_base_eq_dec], [is_DVALUE_IX], [dvalue_base_int_unsigned]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params : Type := { width : nat }.

Inductive memory_bit : Set := Byte (b : nat) | Ptr (p : nat).

Definition show_memory_bit (b : memory_bit) (pa : Params) : nat :=
  match b with Byte n => n + width | Ptr n => n end.

Module ClassArgInMethod.

  Definition use (b : memory_bit) (pa : Params) : nat := show_memory_bit b pa.

End ClassArgInMethod.

Crane Extraction "class_arg_in_method" ClassArgInMethod.
