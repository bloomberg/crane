From Stdlib Require Import List.
Import ListNotations.

(* As in decl_order_method_alias, but without a type alias: a top-level
   inductive and a function taking it whose body calls another function of
   this file. *)

Inductive rv := RU | RS (n : nat).

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

Definition write_r (rf : list rv) (r : nat) (v : rv) : option (list rv) :=
  replace_nth rf r v.
