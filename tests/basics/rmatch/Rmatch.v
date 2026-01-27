(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Bool.
From Crane Require Mapping.Std Mapping.NatIntStd.


Module RMatch.

Record MyRec : Type :=
 { f1 : nat;
   f2 : nat;
   f3 : nat
 }.

Definition sum (r : MyRec) : nat :=
  match r with
  | {| f1 := n1; f2 := n2; f3 := n3 |} => n1 + n2 + n3
  end.

End RMatch.

Require Crane.Extraction.

Crane Extraction "rmatch" RMatch.
