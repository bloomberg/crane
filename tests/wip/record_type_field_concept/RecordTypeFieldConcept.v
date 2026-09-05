From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module RecordTypeFieldConcept.

(** A record with a [Type]-valued field is emitted as a C++ concept, yet it
    is also used as a value type and as a list element. *)
Record dyn := mkDyn { dty : Type ; dval : dty ; dshow : dty -> nat }.

Definition read (d : dyn) : nat := dshow d (dval d).

Definition ds : list dyn :=
  [ mkDyn nat 7 (fun n => n)
  ; mkDyn (list nat) [1;2;3] (@length nat)
  ; mkDyn (nat * nat) (3, 4) (fun p => fst p * snd p) ].

Definition total : nat := fold_left (fun acc d => acc + read d) ds 0.

End RecordTypeFieldConcept.
Crane Extraction "record_type_field_concept" RecordTypeFieldConcept.
