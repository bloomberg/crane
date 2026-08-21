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
    (["classify_ml_self_ref"] in "src/gen_decls.ml") used to recognise only
    those two shapes, reported no self-recursion here, and emitted no
    iterative destructor for [rose] at all. Destruction then fell back to the
    default member-wise [~shared_ptr] chain, recursing once per level and
    overflowing the C++ call stack on a deep value (CWE-674).

    It now classifies recursion through a flat single-constructor wrapper too,
    and the generated [~rose] reaches through a uniquely-owned [box] cell to
    move the nested [rose] onto its worklist. *)
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
