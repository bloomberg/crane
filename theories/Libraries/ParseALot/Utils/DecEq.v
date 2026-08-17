(* SPDX-License-Identifier: BSD-3-Clause *)
(** A minimal decidable-equality typeclass, used by [NativeMapBaseline] to
    implement a generic association-list map. Kept separate from
    [NativeMapBaseline.v] (rather than defined there) so it can be imported
    unconditionally by consumers like [Lexer/Memo/ConcreteMemo.v], regardless
    of which realization of [NativeMap] is toggled in. *)
Class Dec (K : Type) := dec_eq : forall x y : K, {x = y} + {x <> y}.
