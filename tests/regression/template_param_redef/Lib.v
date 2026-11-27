From Crane Require Extraction.

(** A polymorphic function over a mapped type, in one file, used from
    another: [f] is declared in [struct Lib] with [template <typename T1 =
    void>] and defined out of line after it.  The out-of-line definition
    used to repeat the default argument, which C++ rejects as a redefinition
    of it.

    The mapping says where [ex]'s parameter goes ([SourceType A]), so the
    type is no [std::monostate<A>]. *)
Variant ex (A : Type) : Type := mk_box.

From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Import PrimString.PStringNotations List.ListNotations.
Local Open Scope pstring_scope.

#[global] Instance ex_mapping (A : Type) : TypeMapping (ex A) :=
  {| type_headers := ["variant"; "type_traits"];
     type_cpp :=
       Crane.Cpp.Apply "std::conditional_t"
         [Crane.Cpp.ValueArg "true"; Crane.Cpp.TypeArg (Crane.Cpp.Name "std::monostate");
          Crane.Cpp.TypeArg (Crane.Cpp.SourceType A)];
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews (ex A);
     type_interface := AlgebraicInterface [event (Ref (@mk_box A)) "std::monostate{}"];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

Definition f {A : Type} (b : ex A) : unit := tt.
