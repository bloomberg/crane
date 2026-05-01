From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module GeneratedVariantAliasNameClash.

(** Generated ADT classes contain an internal alias named [variant_t] for the
    backing [std::variant].  If the Rocq inductive itself is named [variant_t],
    Crane generates a C++ class [variant_t] that also declares
    [using variant_t = ...] inside the class.  C++ rejects this because the
    nested type alias has the same name as the enclosing class. *)

Inductive variant_t : Type :=
| Empty : variant_t
| Flag : bool -> variant_t.

Definition is_flag (x : variant_t) : bool :=
  match x with
  | Empty => false
  | Flag b => b
  end.

Definition sample : bool := is_flag (Flag true).

End GeneratedVariantAliasNameClash.

Crane Extraction "generated_variant_alias_name_clash" GeneratedVariantAliasNameClash.
