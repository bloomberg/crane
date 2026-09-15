From Stdlib Require Import List.
Import ListNotations.

(* A top-level inductive, a type alias over it, and a function taking the
   inductive whose type names the alias and whose body calls another
   function of this file. *)

Inductive rv := RU | RS (n : nat).

Definition rfile := list rv.

Fixpoint replace_nth {A : Type} (l : list A) (i : nat) (x : A)
  : option (list A) :=
  match l, i with
  | [], _ => None
  | _ :: t, O => Some (x :: t)
  | y :: t, S i' =>
      match replace_nth t i' x with
      | Some t' => Some (y :: t')
      | None => None
      end
  end.

Definition write_r (rf : rfile) (r : nat) (v : rv) : option rfile :=
  replace_nth rf r v.
