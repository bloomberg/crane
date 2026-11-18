From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List Strings.String.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Without the Std mapping, Rocq's [string] used only inside a function type
    ([list string -> pt], the domain of a beta-redex) is spelled [String] in
    C++ but never declared: "unknown type name 'String'". *)
Module RocqStringTypeUndeclared.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition t : nat :=
  (fun w : list String.string -> pt => px (w [])) (fun _ : list String.string => mkpt 7 true).

End RocqStringTypeUndeclared.

Crane Extraction "rocq_string_type_undeclared" RocqStringTypeUndeclared.
