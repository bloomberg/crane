From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
(** A `sigT` payload whose type is value-dependent (`list nat` in the `false`
    branch) is erased to `std::any`.  The producer must store it in the
    canonical element-erased shape the consumer reads back. *)

Module SigtListPayloadAnyCast.
Definition pack : sigT (fun b : bool => if b then nat else list nat) :=
  existT _ false [1;2;3].
Definition go : nat :=
  match pack with
  | existT _ true n => n
  | existT _ false l => length l
  end.
End SigtListPayloadAnyCast.
Crane Extraction "sigt_list_payload_any_cast" SigtListPayloadAnyCast.
