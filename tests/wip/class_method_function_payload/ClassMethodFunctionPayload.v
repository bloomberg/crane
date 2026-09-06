From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [twiceM] instantiates [bind]'s second type argument at a *function* type,
    [M (nat -> nat)].  The instance bodies do not recover that: [MOpt]'s [bind]
    types its payload as [uint64_t], so the returned [std::function] does not
    convert, and the caller then tries to call a [uint64_t]. *)

Module ClassMethodFunctionPayload.

  Class Monad (M : Type -> Type) := {
    ret : forall A, A -> M A ;
    bind : forall A B, M A -> (A -> M B) -> M B }.

  #[export] Instance MOpt : Monad option :=
    { ret A x := Some x ;
      bind A B m f := match m with None => None | Some x => f x end }.

  #[export] Instance MList : Monad list :=
    { ret A x := [x] ; bind A B m f := List.flat_map f m }.

  Definition adders {M} `{Monad M} (x : M nat) : M (nat -> nat) :=
    bind nat (nat -> nat) x (fun n => ret (nat -> nat) (fun k => k + n)).

  Definition run : nat :=
    (match adders (Some 3) with Some f => f 1 | None => 0 end)
    + List.fold_left (fun a f => a + f 1) (adders [1;2]) 0.

End ClassMethodFunctionPayload.

Crane Extraction "class_method_function_payload" ClassMethodFunctionPayload.
