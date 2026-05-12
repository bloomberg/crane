From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import Strings.String.

(* A module type that uses the Rocq `string` type in a function signature.
   In separate extraction, cross-file merged inductives like `string` must be
   qualified as String::String (not bare String) since String is the namespace. *)
Module Type HasShow.
  Parameter t : Type.
  Parameter show : t -> string.
End HasShow.

Module ShowNat <: HasShow.
  Definition t := nat.
  Fixpoint show (n : nat) : string :=
    match n with
    | O => "0"
    | S n' => String.append (show n') "+"
    end.
End ShowNat.

Crane Separate Extraction ShowNat.
