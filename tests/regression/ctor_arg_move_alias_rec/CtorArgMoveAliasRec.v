From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Recursive variant of [ctor_arg_move_alias]: the same use-after-move, but
    reached through a tail-modulo-cons [Fixpoint] rather than a one-shot
    [Definition], so every level of the recursion re-triggers it.

    [annotate] rebuilds the list, interleaving a running total.  Because [h]
    occurs exactly once and [o] is owned (it escapes through the [mynil]
    branch), Crane used to emit

    {[
      auto& [a0, a1] = std::get<Mycons>(o.v_mut());
      return mylist<inner>::mycons(
          std::move(a0),
          mylist<inner>::mycons(inner::icons(osum(o), inner::inil()),
                                annotate( *a1 )));
    ]}

    [std::move(a0)] hollowed out [o]'s head element while the sibling argument
    computed [osum(o)] over that same [o].  The two are unsequenced; clang
    performed the move first, so [osum] walked a moved-from [inner] whose tail
    [shared_ptr] was null.

    The field move is now suppressed because the branch body still reads [o],
    so [run 1 = 8]. *)

Module CtorArgMoveAliasRec.

Inductive inner : Type :=
| INil : inner
| ICons : nat -> inner -> inner.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint isum (i : inner) : nat :=
  match i with
  | INil => 0
  | ICons x xs => x + isum xs
  end.

Fixpoint osum (o : mylist inner) : nat :=
  match o with
  | mynil => 0
  | mycons h t => isum h + osum t
  end.

(** The head element [h] is consumed into the freshly built cell while the
    sibling argument still reads [o]. *)
Fixpoint annotate (o : mylist inner) : mylist inner :=
  match o with
  | mynil => o
  | mycons h t => mycons h (mycons (ICons (osum o) INil) (annotate t))
  end.

(** For [n = 1] the input is [[ICons 1 INil; ICons 2 INil]], so
    [annotate] yields [[I 1; I 3; I 2; I 2]] and [run 1 = 1+3+2+2 = 8]. *)
Definition run (n : nat) : nat :=
  osum (annotate (mycons (ICons n INil) (mycons (ICons (S n) INil) mynil))).

End CtorArgMoveAliasRec.

Crane Extraction "ctor_arg_move_alias_rec" CtorArgMoveAliasRec.
