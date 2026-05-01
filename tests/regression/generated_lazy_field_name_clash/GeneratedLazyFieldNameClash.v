From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module GeneratedLazyFieldNameClash.

(** Generated coinductive classes store their forced value in a lazy field named
    [d_lazyV_].  If the Rocq coinductive itself is named [d_lazyV_], Crane
    generates a C++ class [d_lazyV_] with a data member also named [d_lazyV_].
    This hides the class name inside its own scope and breaks constructors and
    method signatures, so the generated C++ does not compile. *)

CoInductive d_lazyV_ : Type :=
| Cons : bool -> d_lazyV_ -> d_lazyV_.

CoFixpoint true_stream : d_lazyV_ :=
  Cons true true_stream.

Definition head (s : d_lazyV_) : bool :=
  match s with
  | Cons b _ => b
  end.

Definition sample : bool := head true_stream.

End GeneratedLazyFieldNameClash.

Crane Extraction "generated_lazy_field_name_clash" GeneratedLazyFieldNameClash.
