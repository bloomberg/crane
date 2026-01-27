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
