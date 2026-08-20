From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** Use-after-move: a constructor field is moved out of an owned scrutinee
    while a sibling argument of the same call still reads that scrutinee.

    Ingredients, all of which are needed:

    - [mylist] is polymorphic, so [grab] stays a free function instead of
      being methodified onto a [const this] (a [const] receiver silently
      degrades [std::move] to a copy and hides the problem).
    - [o] escapes through the [mynil] branch, so escape analysis marks it
      {i owned} and it is passed by value.  Owned scrutinees are destructured
      with [auto& [a0, a1] = std::get<Mycons>(o.v_mut())], i.e. [a0] is a
      mutable reference {i into} [o].
    - the element type [inner] is a non-trivial inductive, so moving [a0]
      really does hollow out [o]'s head (a trivial [nat] element would make
      the move a no-op).
    - [h] occurs exactly once in the branch, so move-on-last-use fires and
      emits [std::move(a0)].

    Crane used to emit

    {[
      auto& [a0, a1] = std::get<Mycons>(o.v_mut());
      return pack::pack0(std::move(a0), osum(o));
    ]}

    The two arguments are {i unsequenced}: [std::move(a0)] consumes [o]'s
    head element, and [osum(o)] walks the very same [o].  Whichever order
    the compiler picks, one of them is wrong; with clang the move happened
    first, so [osum] read a moved-from [inner] whose tail [shared_ptr] was
    null and dereferenced it.

    [gen_match_branch] now suppresses field moves whenever the branch body
    still reads the owned scrutinee, so the field is copied instead and
    [run 1 = 6]. *)

Module CtorArgMoveAlias.

Inductive inner : Type :=
| INil : inner
| ICons : nat -> inner -> inner.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Inductive pack : Type :=
| Pack : inner -> nat -> pack
| PList : mylist inner -> pack.

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

(** [h] is the sole occurrence of the head field, so Crane moves it out of
    [o]; the sibling argument [osum o] still reads the whole [o]. *)
Definition grab (o : mylist inner) : pack :=
  match o with
  | mynil => PList o
  | mycons h _ => Pack h (osum o)
  end.

(** [o = [ICons n (ICons (S n) INil)]], so [osum o = 2n+1] and
    [isum h = 2n+1]; the result is [4n+2], i.e. [6] for [n = 1]. *)
Definition run (n : nat) : nat :=
  match grab (mycons (ICons n (ICons (S n) INil)) mynil) with
  | Pack i s => s + isum i
  | PList l => osum l
  end.

End CtorArgMoveAlias.

Crane Extraction "ctor_arg_move_alias" CtorArgMoveAlias.
