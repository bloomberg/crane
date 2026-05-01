From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module GeneratedVariantFactoryNameClash.

(** Constructors become static factory methods on the generated C++ class.  A
    constructor named [Variant_t] lowers to a factory named [variant_t], which
    collides with Crane's internal [using variant_t = ...] alias for the backing
    [std::variant].  The generated C++ does not compile because a member type
    alias and a static member function cannot share this name cleanly. *)

Inductive token : Type :=
| Variant_t : token
| Other : bool -> token.

Definition is_variant (t : token) : bool :=
  match t with
  | Variant_t => true
  | Other b => b
  end.

Definition sample : bool := is_variant Variant_t.

End GeneratedVariantFactoryNameClash.

Crane Extraction "generated_variant_factory_name_clash" GeneratedVariantFactoryNameClash.
