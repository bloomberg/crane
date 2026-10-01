From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

(** A monad the recursion below is generic in, so that the recursive function
    is passed as a {i value} rather than applied. *)
Class Monad (m : Type -> Type) := {
  ret : forall {A}, A -> m A ;
  bind : forall {A B}, m A -> (A -> m B) -> m B }.

#[global] Instance option_monad : Monad option := {
  ret A x := Some x ;
  bind A B o f := match o with None => None | Some x => f x end }.

(** The class the section is parameterised by.  Rocq prepends the section's
    [Context] to every definition in it, so a use of [freeze] inside the
    section is already applied to one argument. *)
Class Params := { base : Set ; base_default : base }.

(** Four more parameters that extraction erases.  They are what make the
    fixpoint's ML signature longer than the arguments it is applied to, which
    is the condition [general_optimize_fix] fires on. *)
Class C1 (X : Type) := { c1 : X -> X }.
Class C2 (X : Type) := { c2 : X -> X }.
Class C3 (X : Type) := { c3 : X -> X }.
Class C4 (X : Type) := { c4 : X -> X }.

Fixpoint map_monad {m : Type -> Type} `{Monad m} {A B : Type}
    (f : A -> m B) (l : list A) : m (list B) :=
  match l with
  | [] => ret []
  | x :: xs =>
    bind (f x) (fun y => bind (map_monad f xs) (fun ys => ret (y :: ys)))
  end.

Section Denote.
  Context {Pa : Params}.

  Inductive tree : Set :=
  | Leaf (b : base)
  | Node (kids : list tree).

  (** [freeze] refers to itself {i point-free}: [map_monad freeze kids] passes
      it as a value, so there is no redex for [normalize] to reduce.  The
      lambdas [general_optimize_fix] wraps around the recursive occurrence
      therefore survive into the C++ backend, and need real types -- they used
      to be written [Taxiom], which prints as the undeclared type [axiom]. *)
  Fixpoint freeze {X : Type} `{C1 X} `{C2 X} `{C3 X} `{C4 X}
      (t : tree) : option tree :=
    match t with
    | Leaf b => ret (Leaf b)
    | Node kids => bind (map_monad freeze kids) (fun ks => ret (Node ks))
    end.

End Denote.
