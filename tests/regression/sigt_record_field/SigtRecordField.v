From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** The field [payload] is declared at the erased shape [SigT<std::any,
    std::any>], but each producer builds the [existT] at its concrete
    instantiation -- [SigT<std::any, List<std::any>>] for [b2] -- so the
    aggregate initialiser does not match the field it initialises. *)

Module SigtRecordField.

  Record boxed := MkBoxed { payload : { A : Type & A } ; size : nat }.

  Definition b1 : boxed := MkBoxed (existT (fun A : Type => A) nat 5) 1.
  Definition b2 : boxed := MkBoxed (existT (fun A : Type => A) (list nat) [1;2]) 2.

  Definition peek (b : boxed) : nat := size b.

  Definition run : nat := peek b1 + peek b2.

End SigtRecordField.

Crane Extraction "sigt_record_field" SigtRecordField.
