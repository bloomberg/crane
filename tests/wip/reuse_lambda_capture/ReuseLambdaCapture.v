From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseLambdaCapture.

(** A variant of the reuse-use-after-move bug where the scrutinee
    is used not directly but through a LAMBDA that captures it.

    The reuse optimization fires because:
    1. [l] escapes in the [else] branch (returned directly) so the
       parameter is owned (passed by value).
    2. The [mycons] branch constructs a [mycons] with matching arity
       so [find_reuse_candidates] accepts it.
    3. At runtime [use_count() == 1] holds for fresh values.

    The reuse path does:
      auto x  = std::move(_rf.d_a0);
      auto xs = std::move(_rf.d_a1);   // _rf.d_a1 is now null
      _rf.d_a0 = x + 1;
      _rf.d_a1 = map(lambda, xs);      // lambda calls length(l)
                                        // l is the same object as _rf
                                        // l.d_a1 is null -> crash
      return _rf;

    The key difference from [reuse_use_after_move]: the scrutinee
    is accessed THROUGH A CLOSURE passed to [map], not by a direct
    call.  This tests whether the reuse analysis considers indirect
    uses via captured variables. *)

(** Define [mycons] FIRST so it gets variant index 0.
    The reuse optimization picks [List.hd reuse_candidates], i.e. the
    first constructor branch with a matching tail constructor.
    By putting [mycons] at index 0, reuse fires on the [mycons] branch. *)

Inductive mylist : Type :=
| mycons : nat -> mylist -> mylist
| mynil : mylist.

Arguments mycons _ _.
Arguments mynil.

Fixpoint length (l : mylist) : nat :=
  match l with
  | mycons _ t => 1 + length t
  | mynil => 0
  end.

Fixpoint map (f : nat -> nat) (l : mylist) : mylist :=
  match l with
  | mycons h t => mycons (f h) (map f t)
  | mynil => mynil
  end.

(** BUG: reuse fires, then [length l] inside the lambda accesses
    moved-from fields of [l].

    The reuse path does:
      auto x  = std::move(_rf.d_a0);
      auto xs = std::move(_rf.d_a1);   // _rf.d_a1 is now null
      _rf.d_a0 = x + 1;
      _rf.d_a1 = map(lambda, xs);      // lambda calls length(l)
                                        // l is the same object as _rf
                                        // l.d_a1 is null -> crash
      return _rf; *)

Definition add_length_to_each (l : mylist) (b : bool) : mylist :=
  if b then
    match l with
    | mycons h t => mycons (h + 1) (map (fun x => x + length l) t)
    | mynil => mynil
    end
  else l.

Definition test1 : nat :=
  length (add_length_to_each (mycons 10 (mycons 20 (mycons 30 mynil))) true).

(** Expected: map adds length(original list)=3 to each tail element.
    Original: [10, 20, 30]
    Result:   [11, 23, 33]  (h+1=11, 20+3=23, 30+3=33)
    Length = 3 *)

Definition test2 : nat :=
  match add_length_to_each (mycons 5 (mycons 6 mynil)) true with
  | mycons h _ => h
  | _ => 999
  end.
(** Expected: 5 + 1 = 6 *)

End ReuseLambdaCapture.

Crane Extraction "reuse_lambda_capture" ReuseLambdaCapture.
