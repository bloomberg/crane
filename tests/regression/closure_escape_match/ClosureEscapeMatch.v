From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module ClosureEscapeMatch.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => S (length xs)
  end.

Fixpoint app {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (app xs l2)
  end.

(** Return a closure wrapped in option — prevents uncurrying.
    The closure captures a pattern variable [hd] (a shared_ptr),
    which is an inlined _args.d_a0 inside the std::visit callback. *)
Definition make_prepender_opt (l : mylist (mylist nat))
  : option (mylist nat -> mylist nat) :=
  match l with
  | mynil => None
  | mycons hd _ => Some (fun x => app hd x)
  end.

(** Return a closure in a pair — prevents uncurrying.
    Captures pattern variables [x] and [xs]. *)
Definition make_pair_fn_opt (l : mylist nat)
  : option (unit -> nat * nat) :=
  match l with
  | mynil => None
  | mycons x xs => Some (fun _ => (x, length xs))
  end.

(** Nested matches with closures returned in option. *)
Definition nested_closure_opt (a b : mylist nat)
  : option (nat -> nat) :=
  match a with
  | mynil =>
    match b with
    | mynil => None
    | mycons y _ => Some (fun n => y + n)
    end
  | mycons x _ =>
    match b with
    | mynil => Some (fun n => x + n)
    | mycons y _ => Some (fun n => x + y + n)
    end
  end.

(** Closure stored in a product, capturing shared_ptr pattern variable. *)
Definition closure_in_pair (l : mylist (mylist nat))
  : nat * (mylist nat -> mylist nat) :=
  match l with
  | mynil => (0, fun x => x)
  | mycons hd tl => (length hd, fun x => app hd x)
  end.

End ClosureEscapeMatch.

Crane Extraction "closure_escape_match" ClosureEscapeMatch.
