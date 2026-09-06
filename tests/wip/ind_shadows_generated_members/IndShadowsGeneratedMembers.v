From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** Every generated inductive carries a [variant_t] alias and [v] / [v_mut]
    accessors.  An inductive that is itself named [variant_t], with
    constructors named [v_mut] and [v_], redeclares them, and the pattern match
    then calls [std::get_if] against the constructor rather than the alias. *)

Module IndShadowsGeneratedMembers.

  Inductive variant_t := v_mut : nat -> variant_t | v_ : variant_t -> variant_t.

  Fixpoint depth (x : variant_t) : nat :=
    match x with
    | v_mut n => n
    | v_ y => S (depth y)
    end.

  Definition run : nat := depth (v_ (v_ (v_mut 2))).

End IndShadowsGeneratedMembers.

Crane Extraction "ind_shadows_generated_members" IndShadowsGeneratedMembers.
