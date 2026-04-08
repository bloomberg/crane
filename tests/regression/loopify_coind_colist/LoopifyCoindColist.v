From Stdlib Require Import Nat List.
Import ListNotations.
From Crane Require Mapping.Std Mapping.NatIntStd.
Require Crane.Extraction.

Set Crane Loopify.

Module LoopifyCoindColist.

CoInductive colist (A : Type) : Type :=
| conil : colist A
| cocons : A -> colist A -> colist A.
Arguments conil {A}.
Arguments cocons {A}.

CoFixpoint comap {A B} (f : A -> B) (l : colist A) : colist B :=
  match l with
  | conil => conil
  | cocons x xs => cocons (f x) (comap f xs)
  end.

CoFixpoint cotake {A} (n : nat) (l : colist A) : colist A :=
  match n with
  | 0 => conil
  | S n' => match l with
            | conil => conil
            | cocons x xs => cocons x (cotake n' xs)
            end
  end.

CoFixpoint from_list {A} (l : list A) : colist A :=
  match l with
  | nil => conil
  | cons x xs => cocons x (from_list xs)
  end.

Fixpoint to_list {A} (fuel : nat) (l : colist A) : list A :=
  match fuel with
  | 0 => nil
  | S f => match l with
           | conil => nil
           | cocons x xs => cons x (to_list f xs)
           end
  end.

Definition test_comap :=
  to_list 5 (comap (fun n => n * 2) (from_list (1 :: 2 :: 3 :: nil))).

Definition test_cotake :=
  to_list 10 (cotake 2 (from_list (10 :: 20 :: 30 :: nil))).

End LoopifyCoindColist.

Crane Extraction "loopify_coind_colist" LoopifyCoindColist.
