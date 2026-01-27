(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module List.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

Definition tl {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x ls => ls
  end.

Definition hd {A : Type} (x : A) (l : list A) : A :=
  match l with
  | nil => x
  | cons y ls => y
  end.

Fixpoint last {A : Type} (x : A) (l : list A) : A :=
  match l with
  | nil => x
  | cons y ls => last y ls
  end.

Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x l1 => cons x (app l1 l2)
  end.

Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x l' => cons (f x) (map f l')
  end.

Definition mytest := app (cons three (cons one (cons two nil))) (cons eight (cons three (cons seven (cons nine nil)))).

(* Definition test2 := map (fun x => x + three) mytest. *)

(*
Fixpoint find {A} (f : A -> bool) (l:list A) : option A :=
  match l with
  | nil => None
  | cons x tl => if f x then Some x else find f tl
  end.

Definition test2 := match find (fun x => Nat.eqb x 3) test with
                    | Some x => x
                    | None => O
                    end.
*)
End List.

Crane Extraction "list" List.
