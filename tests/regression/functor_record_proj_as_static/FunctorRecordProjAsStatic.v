(** A record field of a module obtained by *functor application*, projected
    from outside that module's struct.

    [IM.this m] is [m.this_].  It used to come out as a module-scoped static
    call instead,

      return raw_size<T1>(IM::template this_<T1>(m));

    giving [error: no member named 'this_' in 'Make<Z_as_OT>'] -- a call to
    something that was never going to exist, since a projection that is never
    used higher-order is not emitted as a function at all.  The rewrite that
    turns a projection into a member access was guarded on the projection
    having no type arguments, and this one is applied at [A].  A record in an
    ordinary [Module ... End] did not reproduce it: there the projection is
    monomorphic by the time it is called.

    The field is named [this], so the test also pins that the member access is
    spelled with the escaped field name [this_] rather than the raw Rocq
    label.

    Only one of the two printer sites is covered here.  The fix relaxed the
    same guard at both the call site and the higher-order site -- the one that
    prints a projection used as a function value as
    [[](const auto &_x) { return _x.field; }] -- and nothing in this suite, or
    in Vellvm, uses a projection higher-order with type arguments or with a
    keyword field name.  That half is carried by the argument that two sites
    answering one question should not disagree, and by nothing measured.

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
