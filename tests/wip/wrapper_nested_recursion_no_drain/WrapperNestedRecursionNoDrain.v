From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module WrapperNestedRecursionNoDrain.

(** A user-defined wrapper. Nothing special about it: one type parameter,
    one constructor, one field. *)
Inductive box (A : Type) : Type := Box : A -> box A.
Arguments Box {A} _.

(** [rose]'s recursive occurrence sits inside [box], so it is neither a direct
    self-reference nor a self-reference through a list. The drain classifier
    (["classify_ml_self_ref"] in "src/gen_decls.ml") recognises only those two
    shapes, so it reports no self-recursion here and Crane emits no iterative
    destructor for [rose] at all. The same program written with [list rose]
    instead of [box rose] does get one, and survives this test.

    Destruction therefore falls back to the default member-wise
    [~shared_ptr] chain, which recurses once per level of the value. A deep
    [rose] overflows the C++ call stack when it goes out of scope (CWE-674). *)
Inductive rose : Type :=
| RLeaf : nat -> rose
| RNode : box rose -> rose.

Fixpoint deep (n : nat) : rose :=
  match n with
  | O => RLeaf 42
  | S m => RNode (Box (deep m))
  end.

Definition test_deep (n : nat) : nat :=
  match deep n with
  | RLeaf x => x
  | RNode _ => 0
  end.

End WrapperNestedRecursionNoDrain.

(** [Set Crane Loopify] makes [deep] build the value with an explicit frame
    stack rather than by C++ recursion. Without it a crash here would be
    ambiguous between construction and destruction; with it, construction
    costs no call-stack depth and any overflow is the destructor's. *)
Set Crane Loopify.
Crane Extraction "wrapper_nested_recursion_no_drain" WrapperNestedRecursionNoDrain.
