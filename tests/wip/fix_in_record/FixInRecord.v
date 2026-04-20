From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixInRecord.

(** A local fixpoint stored in a Rocq record field.

    BUG HYPOTHESIS: Records are translated to C++ structs with named
    fields. A field of type [nat -> nat] becomes
    [std::function<unsigned int(unsigned int)>]. When a local fixpoint
    (which uses [&] capture) is stored in a record field, the
    [std::function] wraps the [&] closure. After the creating function
    returns, the captured references dangle.

    This is a different escape mechanism from option/pair/list:
    the closure escapes through a RECORD FIELD. *)

Record fn_box := MkFnBox {
  label : nat;
  fn : nat -> nat
}.

Definition make_box (n : nat) : fn_box :=
  let base := n * 3 in
  let fix add (x : nat) : nat :=
    match x with
    | O => base
    | S x' => S (add x')
    end
  in MkFnBox base add.

(** test1: n=10, base=30, fn = add where add(x) = 30+x.
    fn(make_box 10)(7) = 30 + 7 = 37.
    Bug: [base] captured by [&] in [add], dangles after [make_box] returns. *)
Definition test1 : nat :=
  fn (make_box 10) 7.

(** test2: With intervening work.
    n=20, base=60, fn(5) = 60+5 = 65. *)
Definition test2 : nat :=
  let bx := make_box 20 in
  let noise := 1 + 2 + 3 + 4 + 5 in
  fn bx noise.

(** test3: Use label too (to ensure struct is alive).
    n=5, base=15, label=15, fn(0) = 15. label + fn(0) = 30. *)
Definition test3 : nat :=
  let bx := make_box 5 in
  label bx + fn bx 0.

End FixInRecord.

Crane Extraction "fix_in_record" FixInRecord.
