From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module ExistentialCtorErasedFn.

(** The same erased-function-parameter failure reached through a user
    inductive with an existential constructor rather than through [sigT]. *)
Inductive dynamic : Type :=
| Dyn : forall A : Type, A -> (A -> nat) -> dynamic.

Definition read (d : dynamic) : nat := match d with Dyn _ x f => f x end.

Definition items : list dynamic :=
  [ Dyn nat 7 (fun n => n)
  ; Dyn bool true (fun b => if b then 1 else 0)
  ; Dyn (list nat) [1;2;3] (@length nat) ].

Definition total : nat := fold_left (fun acc d => acc + read d) items 0.

End ExistentialCtorErasedFn.
Crane Extraction "existential_ctor_erased_fn" ExistentialCtorErasedFn.
