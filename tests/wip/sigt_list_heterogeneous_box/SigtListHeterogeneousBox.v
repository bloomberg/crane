From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module SigtListHeterogeneousBox.

(** A list literal of [{ T : Type & T }] values built at different concrete
    types.  The list element type erases to [SigT<..., std::any>], but each
    element is emitted at its concrete type with no boxing at the producer:

      error: no viable conversion from 'SigT<[...], bool>'
             to 'SigT<[...], std::any>'

    This is a producer-side boxing gap: no accessor is involved, unlike
    [sigt_type_witness_container] and [sigt_erased_structured_binding]. *)

Definition anyv := sigT (fun T : Type => T).

Definition items : list anyv :=
  cons (existT (fun T : Type => T) nat 1)
       (cons (existT (fun T : Type => T) bool true) nil).

Definition count (l : list anyv) : nat := List.length l.

Definition run : nat := count items.

End SigtListHeterogeneousBox.

Crane Extraction "sigt_list_heterogeneous_box" SigtListHeterogeneousBox.run SigtListHeterogeneousBox.items.
