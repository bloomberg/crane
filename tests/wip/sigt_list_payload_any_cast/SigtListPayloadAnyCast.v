From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
(** WIP: A `sigT` payload holding a `list nat` is stored as `List<uint64_t>` by the
    producer but read back through a doubled `any_cast<List<std::any>>` at the
    consumer, which throws `std::bad_any_cast` at run time. *)

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
