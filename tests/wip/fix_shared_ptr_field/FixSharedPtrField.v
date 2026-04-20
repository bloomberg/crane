From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixSharedPtrField.

(** A value-type inductive with recursive self-reference (shared_ptr).
    Pattern matching creates structured bindings to fields including
    the shared_ptr tail. A local fixpoint captures these bindings
    by [&], then escapes through [option].

    BUG: The structured bindings [h] and [t] from the match are
    references into the variant's data. The shared_ptr [t] is a
    reference to the shared_ptr field of the variant. When the
    fixpoint escapes, the references dangle. The shared_ptr [t]
    may be destroyed, freeing the tail list. Calling the closure
    then dereferences freed heap memory.

    This differs from closure_map_escape: the captured shared_ptr
    [t] is used to traverse heap-allocated data (mylist_sum t),
    not just read a POD value. Freeing the shared_ptr causes
    a use-after-free on HEAP memory (not just stack). *)

Inductive mylist : Type :=
  | mynil : mylist
  | mycons : nat -> mylist -> mylist.

Fixpoint mylist_sum (l : mylist) : nat :=
  match l with
  | mynil => 0
  | mycons h t => h + mylist_sum t
  end.

Fixpoint mylist_length (l : mylist) : nat :=
  match l with
  | mynil => 0
  | mycons _ t => 1 + mylist_length t
  end.

(** A second inductive to prevent methodification of make_list_fn. *)
Inductive wrapper : Type :=
  | Wrap : mylist -> wrapper.

(** Local fixpoint captures [h : nat] (POD) and [t : shared_ptr<mylist>]
    from the match on value-type [mylist]. Both are captured by [&]. *)
Definition make_list_fn (l : mylist) : option (nat -> nat) :=
  match l with
  | mynil => None
  | mycons h t =>
    let fix compute (x : nat) : nat :=
      match x with
      | O => h + mylist_sum t
      | S x' => 1 + compute x'
      end
    in Some compute
  end.

(** test1: l = [10, 20, 30], h=10, t=[20,30], mylist_sum(t)=50.
    compute(5) = (10+50) + 5 = 65.
    Bug: h and t captured by [&], dangle after match scope ends. *)
Definition test1 : nat :=
  match make_list_fn (mycons 10 (mycons 20 (mycons 30 mynil))) with
  | Some f => f 5
  | None => 999
  end.

(** test2: With intervening allocation to increase stack pressure.
    l = [100, 200], h=100, t=[200], mylist_sum(t)=200.
    compute(0) = 100+200 = 300. *)
Definition test2 : nat :=
  let opt := make_list_fn (mycons 100 (mycons 200 mynil)) in
  let noise := mylist_sum (mycons 1 (mycons 2 (mycons 3 mynil))) in
  match opt with
  | Some f => f 0
  | None => noise
  end.

(** test3: Longer list, use mylist_length on captured tail.
    l = [5, 10, 15, 20, 25], h=5, t=[10,15,20,25],
    mylist_sum(t) = 70, compute(10) = (5+70)+10 = 85. *)
Definition test3 : nat :=
  match make_list_fn (mycons 5 (mycons 10 (mycons 15 (mycons 20 (mycons 25 mynil))))) with
  | Some f => f 10
  | None => 999
  end.

(** Dummy use of wrapper to keep it alive for extraction. *)
Definition wrap_list (l : mylist) : wrapper := Wrap l.

End FixSharedPtrField.

Crane Extraction "fix_shared_ptr_field" FixSharedPtrField.
