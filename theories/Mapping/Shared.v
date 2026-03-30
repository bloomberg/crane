(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.

Crane Extract Inductive bool =>
  "bool"
  [ "true" "false" ]
  "if (%scrut) { %br0 } else { %br1 }".

Crane Extract Inductive sumbool =>
  "bool"
  [ "true" "false" ]
  "if (%scrut) { %br0 } else { %br1 }".

Crane Extract Inlined Constant negb => "!(%a0)".
Crane Extract Inlined Constant andb => "(%a0 && %a1)".
Crane Extract Inlined Constant orb => "(%a0 || %a1)".

Axiom void : Type.
Axiom ghost : void.
Crane Extract Void void [ ghost ].

Crane Extract Inductive unit =>
  "std::monostate"
  [ "std::monostate{}" ]
  "{ %br0 }"
  From "variant".

(* PrimArray - persistent copy-on-write array (persistent_array<T>). *)
From Corelib Require PrimArray.
Crane Extract Inlined Constant PrimArray.array => "persistent_array<%t0>" From "persistent_array.h".
Crane Extract Inlined Constant PrimArray.make => "persistent_array<%t0>(%a0, %a1)" From "persistent_array.h".
Crane Extract Inlined Constant PrimArray.get => "%a0.get(%a1)" From "persistent_array.h".
Crane Extract Inlined Constant PrimArray.set => "%a0.set(%a1, %a2)" From "persistent_array.h".
Crane Extract Inlined Constant PrimArray.length => "%a0.length()" From "persistent_array.h".
Crane Extract Inlined Constant PrimArray.copy => "%a0.copy()" From "persistent_array.h".
