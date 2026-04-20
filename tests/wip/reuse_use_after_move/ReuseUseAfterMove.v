From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseUseAfterMove.

(** Define mycons FIRST so it gets variant index 0.
    This is critical: the reuse optimization picks [List.hd reuse_candidates],
    i.e. the first constructor branch with a matching tail constructor.
    By putting mycons at index 0, the reuse optimization fires on the
    mycons branch instead of skipping to the no-op mynil branch. *)

Inductive mylist : Type :=
  | mycons : nat -> mylist -> mylist
  | mynil : mylist.

Arguments mycons _ _.
Arguments mynil.

Fixpoint length (l : mylist) : nat :=
  match l with
  | mycons _ xs => 1 + length xs
  | mynil => 0
  end.

Fixpoint sum (l : mylist) : nat :=
  match l with
  | mycons x xs => x + sum xs
  | mynil => 0
  end.

(** BUG: The reuse optimization fires because:
    1. [l] escapes in the [else] branch (returned in tail position)
       -> [infer_owned_params] marks [l] as owned (pass by value)
    2. The mycons branch has tail constructor [mycons] with arity 2 = 2
       -> [find_reuse_candidates] finds it as a candidate
    3. mycons is at index 0 -> [List.hd] picks it
    4. At runtime, [use_count() == 1] holds for fresh values

    The reuse branch does:
      auto x  = std::move(_rf.d_a0);   // unsigned int, trivial
      auto xs = std::move(_rf.d_a1);   // shared_ptr -> NULL
      _rf.d_a0 = length(l);            // length accesses l.d_a1 which is NULL!
      _rf.d_a1 = xs;                   // restore xs
      return l;

    [length(l)] traverses [l], hitting the null [d_a1] field.
    Dereferencing null shared_ptr -> CRASH. *)

Definition rewrite_head (l : mylist) (b : bool) : mylist :=
  if b then
    match l with
    | mycons x xs => mycons (length l) xs
    | mynil => mynil
    end
  else l.

(** test1: rewrite_head on [1, 2, 3] with true.
    Expected: length [1,2,3] = 3, so result = [3, 2, 3].
    Bug: null dereference inside length. *)
Definition test1 : nat :=
  match rewrite_head (mycons 1 (mycons 2 (mycons 3 mynil))) true with
  | mycons x _ => x
  | mynil => 999
  end.

(** test2: Use sum instead of length — same bug pattern. *)
Definition rewrite_head_sum (l : mylist) (b : bool) : mylist :=
  if b then
    match l with
    | mycons x xs => mycons (sum l) xs
    | mynil => mynil
    end
  else l.

Definition test2 : nat :=
  match rewrite_head_sum (mycons 10 (mycons 20 (mycons 30 mynil))) true with
  | mycons x _ => x
  | mynil => 999
  end.

End ReuseUseAfterMove.

Crane Extraction "reuse_use_after_move" ReuseUseAfterMove.
