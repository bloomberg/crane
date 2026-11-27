From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.

Module Type T.
  Parameter t : Type.
End T.

Module PredFn (Import D : T).
  Definition cache : Type := list (list t).
  (** A nullary constant inside a functor: a Meyers accessor in C++. *)
  Definition empty_cache : cache := nil.
  Definition size (c : cache) : nat := length c.
End PredFn.
