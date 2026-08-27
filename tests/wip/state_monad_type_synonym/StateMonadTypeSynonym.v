From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A state-monad type synonym (`st A := nat -> (A * nat)`) used through `bind`
    produces a call with the wrong arity on the `std::function` synonym. *)

Module StateMonadTypeSynonym.
Definition st (A : Type) := nat -> (A * nat)%type.
Definition ret {A} (a : A) : st A := fun s => (a, s).
Definition bind {A B} (m : st A) (f : A -> st B) : st B :=
  fun s => let p := m s in f (fst p) (snd p).
Definition tick : st nat := fun s => (s, S s).
Definition prog : st nat := bind tick (fun a => bind tick (fun b => ret (a + b))).
Definition go : nat := fst (prog 1).
End StateMonadTypeSynonym.
Crane Extraction "state_monad_type_synonym" StateMonadTypeSynonym.
