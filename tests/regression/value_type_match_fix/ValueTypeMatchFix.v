From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ValueTypeMatchFix.

(** A non-recursive inductive (will be a value type). *)
Inductive triple :=
  | MkTriple : nat -> nat -> nat -> triple.

(** A fixpoint that captures a field from a value-type match.

    BUG HYPOTHESIS: [triple] is a value type (stack-allocated, non-recursive).
    When pattern matching on a value type, the fields are bound as
    references into the stack-allocated object. If a fixpoint captures
    these references by [&] and then escapes, the references dangle
    when the function returns and the value type is destroyed.

    This is different from pointer-based (shared_ptr) types where the
    field data lives on the heap and persists as long as the shared_ptr. *)

Definition make_adder_from_triple (t : triple) : option (nat -> nat) :=
  match t with
  | MkTriple a b c =>
    let base := a + b + c in
    let fix go (x : nat) : nat :=
      match x with
      | O => base
      | S x' => S (go x')
      end
    in Some go
  end.

(** test1: MkTriple 10 20 30 -> base=60, go(5) = 60+5 = 65. *)
Definition test1 : nat :=
  match make_adder_from_triple (MkTriple 10 20 30) with
  | Some f => f 5
  | None => 999
  end.

(** test2: With noise between creation and use. *)
Definition test2 : nat :=
  let o := make_adder_from_triple (MkTriple 100 200 300) in
  let noise := 42 + 13 in
  match o with
  | Some f => f 0 + noise
  | None => 999
  end.

(** Direct capture of pattern fields (no intermediate let binding). *)
Definition make_field_adder (t : triple) : option (nat -> nat) :=
  match t with
  | MkTriple a _ _ =>
    let fix go (x : nat) : nat :=
      match x with
      | O => a
      | S x' => S (go x')
      end
    in Some go
  end.

(** test3: MkTriple 42 0 0 -> a=42, go(3) = 42+3 = 45. *)
Definition test3 : nat :=
  match make_field_adder (MkTriple 42 0 0) with
  | Some f => f 3
  | None => 999
  end.

End ValueTypeMatchFix.

Crane Extraction "value_type_match_fix" ValueTypeMatchFix.
