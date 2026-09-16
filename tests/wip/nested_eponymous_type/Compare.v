(** Crane bug: a file eponymous with a type declared in a *different* library
    swallows it -- the type is emitted nested inside the file's struct, so
    every qualified use hits C++'s injected-class-name rule.

    This file is [Compare.v] and declares no [Compare]; the inductive of that
    name comes from Stdlib's [OrderedType].  Crane emits

      struct Compare {
        template <typename X> struct Compare { ... };
      };

    and a use spelled [typename Compare::Compare<T>::LT] names the constructor
    of the outer [Compare], not the inner template.

    The same-library case is handled: give this file a [Compare] of its own and
    the module is renamed, as d77449c8 made it do.

    Expected: the module is renamed, leaving [Compare<T>] at top level.
    Actual:   warning: ISO C++ specifies that qualified reference to 'Compare'
                       is a constructor name rather than a type in this
                       context, despite preceding 'typename' keyword
              error: expected '>'
              error: type name requires a specifier or qualifier
              error: expected unqualified-id

    Seen in Vellvm on [Semantics/Operations/Compare.v] against Stdlib's
    [OrderedType.Compare]; it used to be worked around with
    [Crane Extraction Blacklist Compare]. *)

From Crane Require Extraction.
From Stdlib Require Import OrderedType.

(* [is_lt] collides with [Other.is_lt], which forces both files to be emitted
   as structs rather than flattened into the top level. *)
Definition is_lt (n : nat) : bool := Nat.ltb n 3.

Definition cmp_lt {X : Type} {lt eq : X -> X -> Prop} {x y : X}
                  (c : Compare lt eq x y) : bool :=
  match c with LT _ => true | _ => false end.
