From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseFnInBody.

(** [mycons] first so reuse picks it (variant index 0). *)
Inductive mylist :=
| mycons : nat -> mylist -> mylist
| mynil : mylist.

Arguments mycons _ _.
Arguments mynil.

Fixpoint length (l : mylist) : nat :=
  match l with
  | mycons _ t => 1 + length t
  | mynil => 0
  end.

Fixpoint sum (l : mylist) : nat :=
  match l with
  | mycons h t => h + sum t
  | mynil => 0
  end.

(** BUG: reuse fires on the [mycons] branch. The body constructs
    [mycons (sum l + h) t] where [l] is the scrutinee.

    The reuse path does:
      auto h  = std::move(_rf.d_a0);
      auto xs = std::move(_rf.d_a1);   // _rf.d_a1 = nullptr
      _rf.d_a0 = sum(l) + h;           // sum(l) accesses l.d_a1 = nullptr!
      _rf.d_a1 = xs;
      return l;

    [sum(l)] traverses [l], hitting the null [d_a1] field.
    Dereferencing null shared_ptr → CRASH.

    This is similar to [reuse_use_after_move] but the scrutinee
    is used through a DIFFERENT function ([sum] instead of [length])
    AND combined with a pattern variable in an arithmetic expression. *)
Definition prefix_sum (l : mylist) (b : bool) : mylist :=
  if b then
    match l with
    | mycons h t => mycons (sum l + h) t
    | mynil => mynil
    end
  else l.

Definition test1 : nat :=
  sum (prefix_sum (mycons 1 (mycons 2 (mycons 3 mynil))) true).
(** Original list: [1, 2, 3]. sum = 6.
    prefix_sum: head becomes sum([1,2,3]) + 1 = 6 + 1 = 7, tail = [2, 3].
    Result: [7, 2, 3]. sum = 12.
    BUG: sum(l) crashes because l's fields are moved. *)

Definition test2 : nat :=
  sum (prefix_sum (mycons 10 mynil) true).
(** Original: [10]. sum = 10.
    prefix_sum: head = 10 + 10 = 20, tail = [].
    Result: [20]. sum = 20.
    BUG: same crash pattern. *)

End ReuseFnInBody.

Crane Extraction "reuse_fn_in_body" ReuseFnInBody.
