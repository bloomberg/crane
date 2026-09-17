(* A lowercase record named like its file: [catalog] in Catalog.v. *)

Record catalog := { size : nat }.

Definition grow (c : catalog) : catalog := {| size := S (size c) |}.
