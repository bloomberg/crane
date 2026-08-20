From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module OptionNestedRecursionBadCpp.

(** [chain]'s recursive occurrence is nested under [option], which
    "Mapping/Std.v" maps to [std::optional]. The field is stored behind a
    [shared_ptr], so its C++ type is
    [std::shared_ptr<std::optional<chain>>], but the generated match on the
    [option] forgets to dereference the pointer before probing the optional:
    it emits [o.has_value()] against the [shared_ptr] rather than
    dereferencing it first. The result does not compile:

      error: no member named 'has_value' in
             'std::shared_ptr<std::optional<...::chain>>'

    A one-constructor wrapper is enough; nothing here depends on [option]
    specifically beyond its being a mapped type. *)
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
