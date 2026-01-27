(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Copied from https://github.com/bloomberg/game-trees/blob/main/theories/Cotrees.v *)
(* The original source has the Apache license. *)

From Stdlib Require Import List.
Import ListNotations.

Module Colist.

CoInductive colist (A : Type) : Type :=
| conil : colist A
| cocons : A -> colist A -> colist A.

Arguments conil {A}.
Arguments cocons {A} x xs.

Fixpoint list_of_colist {A : Type} (fuel : nat) (l : colist A) {struct fuel} : list A :=
  match fuel with
  | O => nil
  | S fuel' =>
    match l with
    | conil => nil
    | cocons x xs => cons x (list_of_colist fuel' xs)
    end
  end.

CoFixpoint nats (n : nat) : colist nat :=
  cocons n (nats (S n)).

Definition comap {A B : Type} (f : A -> B) : colist A -> colist B :=
  cofix comap (l : colist A) : colist B :=
    match l with
    | conil => conil
    | cocons x xs => cocons (f x) (comap xs)
    end.

Definition first_three : list nat :=
  list_of_colist 3 (nats O).

End Colist.

Require Crane.Extraction.
Crane Extraction "colist" Colist.
