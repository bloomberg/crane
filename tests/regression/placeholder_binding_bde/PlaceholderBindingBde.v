(** Found by Ephyra (round 21, BDE flavour). A match that reads only the
    middle field of a three-field constructor, under [Mapping.BDE], built
    the way BDE tests are ([scripts/compile-bde.sh], [-std=c++20]).

    Expected: compiles; [result = 7].

    Fixed: the unread fields were both printed [_] in one structured
    binding ([const auto &[_, x, _] = ...]), and a repeated [_] is a C++26
    placeholder ("placeholder variables are a C++2c extension").  A flavour
    whose build predates C++26 (BDE) writes an unread binding by its own
    name ([const auto &[d_l, d_x, d_r] = ...]). *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
Module PlaceholderBindingBde.
Inductive tree : Type := Leaf | Node (l : tree) (x : nat) (r : tree).
Definition middle (t : tree) : nat := match t with Leaf => 0 | Node _ x _ => x end.
Definition result : nat := middle (Node Leaf 7 Leaf).
End PlaceholderBindingBde.
Crane Extraction "placeholder_binding_bde" PlaceholderBindingBde.
