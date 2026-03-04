(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: RAM accessor naming keeps namespaces distinct *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module RamAccessorNamespaceSafe.
Inductive port : Type := ReadPort | WritePort.
Definition read (x : port) : nat := match x with | ReadPort => 3 | WritePort => 4 end.
Definition t : nat := read ReadPort + read WritePort.
End RamAccessorNamespaceSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_accessor_namespace_safe" RamAccessorNamespaceSafe.