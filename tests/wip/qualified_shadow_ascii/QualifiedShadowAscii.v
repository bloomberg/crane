(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 5: qualified type names must be rendered in absolute form under shadowing. *)

Module QualifiedShadowAscii.

Module Shadow.
  Inductive shadow : Type :=
  | Mk.
End Shadow.

Definition id_shadow (x : Shadow.shadow) : Shadow.shadow := x.
Definition t : Shadow.shadow := id_shadow Shadow.Mk.

End QualifiedShadowAscii.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extraction "qualified_shadow_ascii" QualifiedShadowAscii.
