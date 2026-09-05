From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module SigtErasedFnParam.

(** A value packed into a [sigT] together with a function that consumes it.
    The pair is stored in erased ([std::any]) slots, but the stored function's
    {e parameter} is not erased, so [crane_erase_fn] instantiates the closure
    body on [std::any] and the body's member access does not type-check. *)
Definition packed := sigT (fun A : Type => (A * (A -> nat))%type).

Definition pack {A : Type} (x : A) (f : A -> nat) : packed :=
  existT _ A (x, f).

Definition unpack (p : packed) : nat :=
  match p with
  | existT _ _ (x, f) => f x
  end.

Definition items : list packed :=
  [ pack 5 (fun n : nat => n)
  ; pack true (fun b : bool => if b then 1 else 0)
  ; pack [1;2;3] (fun l : list nat => length l) ].

Definition total : nat := fold_left (fun acc p => acc + unpack p) items 0.

End SigtErasedFnParam.
Crane Extraction "sigt_erased_fn_param" SigtErasedFnParam.
