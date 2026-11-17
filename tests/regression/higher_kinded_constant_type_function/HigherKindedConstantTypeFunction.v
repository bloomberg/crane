(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a higher-kinded parameter [B : Type -> Type] instantiated at a
    constant type function, [fun T => list nat], does not compile.  [appT]
    becomes [template <template <typename> class T1> T1<uint64_t> appT(T1<crane::obj> f)],
    and nothing at the call says what [T1] is -- a lambda over types is not
    a C++ template, and no carrier is synthesised for it: "could not match
    'crane::obj' against 'unsigned long long'".  The same shape over a proof
    binder ([B : 1 = 1 -> Type]) works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module HigherKindedConstantTypeFunction.

Definition appT (B : Type -> Type) (f : forall T : Type, B T) : B nat := f nat.

Definition z : list nat := appT (fun T => list nat) (fun _ => [1; 2]).

Definition result : nat := List.length z.

End HigherKindedConstantTypeFunction.

Crane Extraction "higher_kinded_constant_type_function" HigherKindedConstantTypeFunction.
