(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Crane.Extraction.

Definition better_zip {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
  let fix go (la : list A) (lb : list B) (acc : list (A * B)) : list (A * B) :=
      match la, lb with
      | x :: xs, y :: ys => go xs ys ((x, y) :: acc)
      | _, _ => rev acc
      end
  in go la lb [].

Crane Extraction "zip" better_zip.
