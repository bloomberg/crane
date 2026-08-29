From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module DepReturnAnyCast.
  (** A definition with a dependent return type erases to [std::any].  The
      producer stores a [List<uint64_t>] but the consumer [any_cast]s to
      [List<std::any>], so the program compiles and then dies at run time with
      an uncaught [std::bad_any_cast]. *)
  Definition dep (b : bool) : (if b then nat else list nat) :=
    match b with true => 7 | false => [1; 2; 3] end.

  Definition run (k : nat) : nat :=
    (dep true) + length (dep false) + k.
End DepReturnAnyCast.

Crane Extraction "dep_return_any_cast" DepReturnAnyCast.
