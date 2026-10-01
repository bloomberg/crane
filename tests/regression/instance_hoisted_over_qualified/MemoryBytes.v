From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.
From Stdlib Require Import List.
Import MonadNotation.
Open Scope monad_scope.

Fixpoint map_monad {m : Type -> Type} `{Monad m} {A B : Type}
  (f : A -> m B) (l : list A) : m (list B) :=
  match l with
  | nil => ret nil
  | cons x xs => y <- f x ;; ys <- map_monad f xs ;; ret (cons y ys)
  end.

Definition helper (n : nat) : nat := n.

Definition EOUP (A : Type) := (nat + A)%type.

#[local] Instance EOUP_Monad : Monad EOUP :=
  {| ret := fun _ a => inr a
   ; bind := fun _ _ m k => match m with inl e => inl e | inr a => k a end |}.

(* Passes [EOUP_Monad] to [map_monad] as an explicit type argument, in
   expression position.  This is the call that comes out over-qualified. *)
Definition bump_all (bs : list nat) : EOUP (list nat) :=
  map_monad (fun b => ret (helper b + 1)) bs.
