(** A lifted helper constrained by a type class, whose forward declaration is
    written ahead of the concept that constrains it.

    {v
      template <Params _tcI0, typename T1> auto _walk_mk(const T1 _x);
      ...
      template <typename I> concept Params = requires { ... };
    v}

    {v
      ./lifted_spec_before_class_concept.h:16:11: error: unknown type name 'Params'
    v}

    Two facts meet.  A lifted helper's spec is emitted ahead of {e every}
    section, deliberately and unconditionally: its definition goes after the
    struct it came out of, and its callers are that struct's members, so there
    is no position for the definition that is also before the calls.  And a
    type class declared at file scope became a concept in the ordinary
    declaration stream, in source order, which here is after the helper's
    spec.

    A struct in that position is repaired by its forward declaration, which is
    why the same ordering is already safe for [struct natParams].  A concept
    has no forward declaration --- C++ does not admit one --- so the only
    repair is to move the concept, and the only place it can move to that is
    ahead of an unconditional prologue is the top of the file.  Which is where
    a {e nested} module's type-class concepts already went, for the unrelated
    reason that a concept cannot be declared inside a struct; this adds the
    file-scope case to the same destination.

    Only at file scope.  Inside a struct, {!Cpp.pp_structure_elements} has
    already decided between hoisting the concept and holding it back behind
    the struct whose types its [requires] clause names, and it can tell those
    apart where the declaration stream cannot.

    {b The test would not have existed without a wrong guess.}  It was written
    to reproduce an undeducible return-only template parameter and does not:
    [T1] turns out deducible from the value argument.  What it does reproduce
    is this, found by reading the diagnostic it actually produced rather than
    the one it was written for. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params := { addr : Type ; zero : addr ; bump : addr -> addr }.

(** [A] is phantom: it is in [tagged A]'s type and in no field, so a lambda
    returning one has a type variable no argument mentions. *)
Inductive tagged (A : Type) : Type :=
| Tag : nat -> tagged A.

Arguments Tag {A}.

Inductive box (P : Params) : Type :=
| Box : addr -> box P.

Arguments Box {P}.

Definition walk {P : Params} (n : nat) (a : addr) : tagged (box P) :=
  let mk := fun (A : Type) (x : addr) => @Tag A 1 in
  match n with
  | O => mk (box P) a
  | S _ => mk (box P) (bump a)
  end.

#[global] Instance natParams : Params :=
  {| addr := nat ; zero := 0 ; bump := S |}.

Module LiftedSpecBeforeClassConcept.
  Definition run : tagged (box natParams) := @walk natParams 1 0.
End LiftedSpecBeforeClassConcept.
Crane Extraction "lifted_spec_before_class_concept" LiftedSpecBeforeClassConcept.

