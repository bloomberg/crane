From Crane Require Extraction.

Module SigTProbe.

(** A dependent pair whose first component is a type and whose second
    component has that concrete type.  Regression test for the bug where
    Crane would generate [SigT<std::any, Bool0>] for the constructor call
    but declare the type as [SigT<std::any, std::any>], producing
    incompatible [shared_ptr] template instantiations. *)
Definition packed : { A : Type & A } :=
  existT (fun A => A) bool true.

Definition sample : nat :=
  match packed with
  | existT _ _ _ => 0
  end.

End SigTProbe.

Crane Extraction "sigt_probe" SigTProbe.
