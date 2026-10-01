From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

(* ExtLib's shape: a Monad class whose carrier [m] is a class member, a generic
   [liftM] written against it, and a Functor instance that forwards to it. *)
Class Mon (m : Type -> Type) : Type := {
  mret : forall A, A -> m A ;
  mbind : forall A B, m A -> (A -> m B) -> m B
}.
Arguments mret {m _ A}. Arguments mbind {m _ A B}.

Definition liftM {m} `{Mon m} {A B} (f : A -> B) : m A -> m B :=
  fun x => mbind x (fun a => mret (f a)).

Class Fun (F : Type -> Type) : Type := {
  ffmap : forall A B, (A -> B) -> F A -> F B ;
  fconst : forall A B, A -> F B -> F A
}.
Arguments ffmap {F _ A B}. Arguments fconst {F _ A B}.

#[global] Instance Mon_option : Mon option | 50 := {
  mret A a := Some a ;
  mbind A B o k := match o with Some a => k a | None => None end
}.

(* The forwarding instance: [liftM]'s A and B sit only in [m A] / [m B], which
   are dependent qualified names and so non-deduced in C++. *)
#[global] Instance Fun_Mon (m : Type -> Type) `{Mon m} : Fun m | 60 :=
{
  ffmap := @liftM m _ ;
  fconst A B a x := liftM (fun _ => a) x
}.

Definition run (o : option nat) : option (list nat) :=
  ffmap (fun x => [x]) o.

Crane Extraction "eta_partial_app_drops_targs" run.
