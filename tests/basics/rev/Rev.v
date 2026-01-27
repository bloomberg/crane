(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Crane.Extraction.

Definition better_rev {A : Type} (l : list A) : list A :=
  let fix go (l : list A) (acc : list A) : list A :=
      match l with
      | [] => acc
      | x :: xs => go xs (x :: acc)
      end
  in go l [].

Crane Extraction "rev" better_rev.
