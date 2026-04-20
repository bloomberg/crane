From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module MatchRefAfterMove.

(** This test exercises patterns where a value is destructured
    and then the original is also used, testing move/reference
    interactions in the generated C++. *)

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

Inductive mypair (A B : Type) : Type :=
| mkpair : A -> B -> mypair A B.

Arguments mkpair {A B}.

(** Pattern 1: Match on a list, return head AND apply a function
    to the tail that also takes the head as argument.
    The generated code must ensure [h] survives until both uses. *)
Fixpoint mylist_length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ t => 1 + mylist_length t
  end.

Definition head_and_tail_length (l : mylist nat) : mypair nat nat :=
  match l with
  | mynil => mkpair 0 0
  | mycons h t => mkpair h (mylist_length t)
  end.

(** Pattern 2: Nested match where inner match is on a field of outer.
    After inner match, outer pattern variables are still used.

    BUG HYPOTHESIS: Outer match creates structured bindings into the
    outer value. Inner match on the tail might consume/move the tail.
    If the outer head [h] is a reference into the outer value, and
    the outer value is freed because the inner match consumes the
    tail (sole remaining reference), [h] dangles. *)
Definition nested_match_probe (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons h t =>
    match t with
    | mynil => h
    | mycons h2 t2 => h + h2 + mylist_length t2
    end
  end.

(** Pattern 3: Build a pair where one element is from a match
    and the other is a function of the matched value.
    Tests evaluation order in pair construction. *)
Definition match_into_pair (l : mylist nat) : mypair nat (mylist nat) :=
  match l with
  | mynil => mkpair 0 mynil
  | mycons h t => mkpair h (mycons (h + 1) t)
  end.

(** Pattern 4: Double match on same value.
    First match extracts head, second match extracts tail.
    Between matches, the value might be moved. *)
Definition double_match (l : mylist nat) : mypair nat (mylist nat) :=
  let h := match l with
           | mynil => 0
           | mycons h _ => h
           end in
  let t := match l with
           | mynil => mynil
           | mycons _ t => t
           end in
  mkpair h t.

Fixpoint mylist_sum (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons h t => h + mylist_sum t
  end.

(** test1: head_and_tail_length [10,20,30] = (10, 2) *)
Definition test1 : nat :=
  match head_and_tail_length (mycons 10 (mycons 20 (mycons 30 mynil))) with
  | mkpair h len => h + len
  end.

(** test2: nested_match_probe [10,20,30] = 10+20+1 = 31 *)
Definition test2 : nat :=
  nested_match_probe (mycons 10 (mycons 20 (mycons 30 mynil))).

(** test3: match_into_pair [5,10] = (5, [6,10]) *)
Definition test3 : nat :=
  match match_into_pair (mycons 5 (mycons 10 mynil)) with
  | mkpair h l => h + mylist_sum l
  end.

(** test4: double_match [7,8,9] = (7, [8,9]) *)
Definition test4 : nat :=
  match double_match (mycons 7 (mycons 8 (mycons 9 mynil))) with
  | mkpair h t => h + mylist_sum t
  end.

(** Pattern 5: CPS with explicit continuation that captures from match.
    The continuation is a SIMPLE lambda, not a fixpoint. *)
Definition match_with_cont (l : mylist nat) (k : nat -> nat -> nat) : nat :=
  match l with
  | mynil => k 0 0
  | mycons h t => k h (mylist_length t)
  end.

(** test5: match_with_cont [100, 200, 300] (+) = 100 + 2 = 102 *)
Definition test5 : nat :=
  match_with_cont (mycons 100 (mycons 200 (mycons 300 mynil)))
    (fun h len => h + len).

(** Pattern 6: Deep nesting of matches with multiple constructors. *)
Inductive either (A B : Type) : Type :=
| Left : A -> either A B
| Right : B -> either A B.

Arguments Left {A B}.
Arguments Right {A B}.

Definition complex_match (e : either (mylist nat) (mylist nat)) : nat :=
  match e with
  | Left l =>
    match l with
    | mynil => 0
    | mycons h _ => h
    end
  | Right l =>
    match l with
    | mynil => 999
    | mycons h t => h + mylist_length t
    end
  end.

(** test6: complex_match (Right [50, 60]) = 50 + 1 = 51 *)
Definition test6 : nat :=
  complex_match (Right (mycons 50 (mycons 60 mynil))).

End MatchRefAfterMove.

Crane Extraction "match_ref_after_move" MatchRefAfterMove.
