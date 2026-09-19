(** A record field of a module obtained by *functor application* is projected
    as a module-scoped static call instead of a member access.

    [IM.this m] should be [m.this_] -- and is, everywhere inside the generated
    [IM] struct itself ([Raw::is_empty<T1>(m.this_)] and friends). But a
    definition *outside* that struct gets

      return raw_size<T1>(IM::template this_<T1>(m));

    giving

      error: no member named 'this_' in 'Make<Z_as_OT>'

    [this_] is a data member of [IM::bst<T1>], not a static member of [IM].

    A record declared in an ordinary [Module ... End] does *not* reproduce:
    there the projection comes out correctly as [m.this_]. The functor
    application is what is needed, presumably because the field arrives
    through the functor's signature rather than from a local record
    declaration.

    Seen in Vellvm at [vellvm_bench.h:8808], from
    [src/rocq/Utils/IntMaps.v:193]:

      Definition IM_greatest_key {A} (m : IM.t A) : option Z
        := IM_raw_greatest_key (IM.this m).

    with [IM] declared at [IntMaps.v:32] as
    [Module IM := FMapAVL.Make(Stdlib.Structures.OrderedTypeEx.Z_as_OT).] *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import FSets.FMapAVL Structures.OrderedTypeEx ZArith.

(* A module obtained by *functor application*, as Vellvm's [IM]. *)
Module IM := FMapAVL.Make(Stdlib.Structures.OrderedTypeEx.Z_as_OT).

(* [IM.this] projects the [bst] record field. *)
Definition raw_size {A} (m : IM.Raw.tree A) : nat := IM.Raw.cardinal m.
Definition im_size {A} (m : IM.t A) : nat := raw_size (IM.this m).

Module Qp.
  Definition use (m : IM.t nat) : nat := im_size m.
End Qp.
Crane Extraction "functor_record_proj_as_static" Qp.
