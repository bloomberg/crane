(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Crane.Extraction.

Definition better_map {A B : Type} (f : A -> B) (l : list A) : list B :=
  let fix go (l : list A) (acc : list B) : list B :=
      match l with
      | [] => rev acc
      | x :: xs => go xs (f x :: acc)
      end
  in go l [].

Crane Extraction TestCompile "map" better_map.
