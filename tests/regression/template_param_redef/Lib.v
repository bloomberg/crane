From Crane Require Extraction.

(** A polymorphic function over a mapped type, in one file, used from
    another: [f] is declared in [struct Lib] with [template <typename T1 =
    void>] and defined out of line after it.  The out-of-line definition
    used to repeat the default argument, which C++ rejects as a redefinition
    of it.

    The mapping says where [ex]'s parameter goes: a mapped name that does
    not ({!Cpp_ir.Foreign_template.custom_template_with_args}) takes it as a
    template argument, and [std::monostate<A>] is no type. *)
Variant ex (A : Type) : Type := mk_box.

Crane Extract Inductive ex => "std::conditional_t<true, std::monostate, %t0>"
  [ "std::monostate{}" ]
From "variant" "type_traits".

Definition f {A : Type} (b : ex A) : unit := tt.
