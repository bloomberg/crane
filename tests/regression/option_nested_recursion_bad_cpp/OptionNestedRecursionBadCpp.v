From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module OptionNestedRecursionBadCpp.

(** [chain]'s recursive occurrence is nested under [option], which
    "Mapping/Std.v" maps to [std::optional] with the custom match template

      [if (%scrut.has_value()) { const %t0& %b0a0 = *%scrut; ... }]

    Because the recursion makes the field indirect, its C++ type is
    [std::shared_ptr<std::optional<chain>>] and the scrutinee prints as the
    dereference [*a1]. [%scrut] is spliced in as text, so the template's
    member access used to bind to [a1] rather than to the pointee:

      if ( *a1.has_value() )  // error: no member named 'has_value' in
                              // 'std::shared_ptr<std::optional<...::chain>>'

    Prefix-operator scrutinees are now parenthesized at the splice point, so
    this comes out as [( *a1 ).has_value()]. Nothing here is specific to
    [option] beyond its being a mapped type with a match template. *)
Inductive chain : Type := Link : nat -> option chain -> chain.

Fixpoint build (n : nat) : chain :=
  match n with
  | O => Link 0 None
  | S m => Link n (Some (build m))
  end.

Fixpoint depth (c : chain) : nat :=
  match c with
  | Link _ o => match o with
                | None => 1
                | Some c' => S (depth c')
                end
  end.

Definition run (n : nat) : nat := depth (build n).

End OptionNestedRecursionBadCpp.

Crane Extraction "option_nested_recursion_bad_cpp" OptionNestedRecursionBadCpp.
