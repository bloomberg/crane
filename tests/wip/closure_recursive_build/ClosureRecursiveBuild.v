From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureRecursiveBuild.

(** A list of closures, each one of which captures a different value. *)
Inductive fn_list :=
  | FNil : fn_list
  | FCons : (nat -> nat) -> fn_list -> fn_list.

(** Recursively build a list of fixpoint closures. Each recursive call
    creates a local fixpoint [adder] that captures the current [n].

    BUG HYPOTHESIS: Each [adder] captures [n] from its stack frame
    by [&]. The closures are stored in [FCons] constructors. After
    [build_adders] returns, all intermediate stack frames are gone,
    and every closure holds a dangling reference. *)

Fixpoint build_adders (n : nat) : fn_list :=
  match n with
  | O => FNil
  | S n' =>
    let fix adder (x : nat) : nat :=
      match x with
      | O => n
      | S x' => S (adder x')
      end
    in FCons adder (build_adders n')
  end.

Fixpoint apply_first (fl : fn_list) (x : nat) : nat :=
  match fl with
  | FNil => 0
  | FCons f _ => f x
  end.

Fixpoint apply_all_sum (fl : fn_list) (x : nat) : nat :=
  match fl with
  | FNil => 0
  | FCons f rest => f x + apply_all_sum rest x
  end.

(** test1: build_adders(3) = [adder_3, adder_2, adder_1].
    apply_first returns adder_3(10) = 3 + 10 = 13. *)
Definition test1 : nat :=
  apply_first (build_adders 3) 10.

(** test2: apply_all_sum sums all adders applied to 0.
    adder_3(0) + adder_2(0) + adder_1(0) = 3 + 2 + 1 = 6. *)
Definition test2 : nat :=
  apply_all_sum (build_adders 3) 0.

(** test3: with noise between build and use.
    build_adders(5), noise, then apply_first(fns, 0) = 5. *)
Definition test3 : nat :=
  let fns := build_adders 5 in
  let noise := 99 + 88 + 77 in
  apply_first fns 0 + noise.

End ClosureRecursiveBuild.

Crane Extraction "closure_recursive_build" ClosureRecursiveBuild.
