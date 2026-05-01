From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module GeneratedStorageFieldNameClash.

(** Generated ADT classes store their backing variant in a private field named
    [d_v_].  If the Rocq inductive itself is named [d_v_], Crane generates a
    C++ class [d_v_] with a data member also named [d_v_].  C++ rejects a
    non-static data member with the same name as its class, so the generated
    code does not compile. *)

Inductive d_v_ : Type :=
| Empty : d_v_
| Flag : bool -> d_v_.

Definition is_flag (x : d_v_) : bool :=
  match x with
  | Empty => false
  | Flag b => b
  end.

Definition sample : bool := is_flag (Flag true).

End GeneratedStorageFieldNameClash.

Crane Extraction "generated_storage_field_name_clash" GeneratedStorageFieldNameClash.
