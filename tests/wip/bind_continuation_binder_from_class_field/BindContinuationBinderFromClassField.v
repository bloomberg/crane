(** The {e element} half of Vellvm Cluster A --- h:40336, h:40344, h:40348 ---
    as distinct from the three {e codomain} sites covered by
    [tests/wip/inner_fix_codomain_from_class].  Six bare [typename _tcI0::IPTR]
    in [MemoryBytes.memory_bytes_to_dvalue] split 3/3 by position:

    {v
      40281  std::function<typename _tcI0::IPTR(          codomain
      40295  -> typename _tcI0::IPTR {                    codomain
      40358  -> typename _tcI0::IPTR {                    codomain
      40336  [=](typename _tcI0::IPTR f) mutable {        ELEMENT   <-- here
      40344  [=](List::list<typename _tcI0::IPTR> rest)   ELEMENT   <-- here
      40348  List::template list<typename _tcI0::IPTR>::cons(       ELEMENT
    v}

    The codomain account does not reach these, and the artifact decides it
    rather than an argument.  [bind<A, B>]'s continuation takes an [A], and [A]
    is spelled out {e correctly} two lines above the binder that gets it wrong:

    {v
      ::EOU_monad::template bind<
          Dvalue<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>,
          List::list<Dvalue<..., ...>>>(
          MemoryBytes::template memory_bytes_to_dvalue<_tcI0>(...),
          [=](typename _tcI0::IPTR f) mutable {          // f must be Dvalue<...>
    v}

    At 40344 the outer [List::list] is right and only the {e leaf} is erased,
    which rules out a whole-type substitution: something wrote the correct
    constructor around the wrong argument.  And unlike the codomain half, this
    one has a source you can name --- the element type is [dv], an ordinary
    class-parameterised inductive, not a type field of any class, and it is
    present in the [bind] call's own type arguments.  If it is still lost at the
    binder, it was dropped rather than never held.

    {b The control is inside the reduction, not beside it.}  The two [bind]
    continuations below are over the same element type in the same emitted
    function, one inside the inline [fix] and one outside it:

    {v
      inside   [=](List<typename _tcI0::addr> r) mutable {        WRONG
      outside  [](const List<Dv<typename _tcI0::addr>>& r) {      RIGHT
    v}

    Every variable a sibling control would have to hold constant --- the class,
    the monad instance, the element type, the plugin revision, the flags --- is
    held here by identity rather than by assertion, because the two sites are
    eleven lines apart in one function.

    {b Hypothesis, stated as one, before any fix exists:} [f] and [r] are the
    erased binders and [cons]'s argument type is merely inferred from them, so
    the element half is {e one} hole with two cascade sites, not three.  Not
    established.  Written down so that a 3 -> 0 is not read afterwards as three
    separate fixes landing.

    Four features of the Vellvm site are kept because it is not yet known which
    is load-bearing: an enclosing [Fixpoint] parameterised by a class; an inner
    [fix] that calls it, which is what keeps it inline rather than lifted (see
    [tests/regression/inline_inner_fix_writes_instance]); two {e nested} binds,
    the inner binder being a [list] of the element; and an element type built
    from a field of the class without being a class field itself.  The last is
    the first one to drop when narrowing.

    Reduced by the Vellvm-side session; ported here unchanged in substance from
    [src/crane/reductions/bind_continuation_binder_from_class_field]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

(** Carrier and monad, reached through an ExtLib [Monad] {e instance}, as
    Vellvm reaches them. *)
Inductive EOU (A : Type) : Type :=
| Ok : A -> EOU A
| Err : nat -> EOU A.

Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end
  |}.

Class Params := { addr : Type ; zero : addr }.

(** The element type: class-parameterised, but an ordinary inductive and {e not}
    a type field of any class.  This is the difference from the codomain half. *)
Inductive dv (P : Params) : Type :=
| DAddr : addr -> dv P
| DNum : nat -> dv P.

Arguments DAddr {P}.
Arguments DNum {P}.

Inductive byte (P : Params) : Type :=
| B : nat -> byte P.

Arguments B {P}.

Fixpoint bytes_to_dv {P : Params} (n : nat) (bs : list (byte P)) : EOU (dv P) :=
  match n, bs with
  | O, _ => ret (DNum 0)
  | S k, nil => ret (DAddr zero)
  | S k, cons (B v) rest =>
      (* The inner [fix] calls the enclosing [Fixpoint], so it stays inline. *)
      let fix go (ds : list nat) (bs0 : list (byte P)) : EOU (list (dv P)) :=
          match ds with
          | nil => ret nil
          | cons _ ds' =>
              (* Outer bind: the continuation binder must be [dv P].  Vellvm
                 h:40336 writes the class instance here. *)
              bind (bytes_to_dv k bs0)
                   (fun (f : dv P) =>
                      (* Nested bind: the binder must be [list (dv P)], and in
                         the artifact the outer [list] is correct while the
                         LEAF is erased.  Vellvm h:40344, h:40348. *)
                      bind (go ds' bs0)
                           (fun (r : list (dv P)) => ret (cons f r)))
          end
      in
      (* The control arm: the same element type, the same monad, outside the
         inline [fix].  This one is spelled correctly. *)
      bind (go (cons v nil) rest) (fun r => ret (DNum (length r)))
  end.

#[global] Instance natParams : Params := {| addr := nat ; zero := 0 |}.

Module BindContinuationBinderFromClassField.
  Definition run : EOU (dv natParams) :=
    @bytes_to_dv natParams 2 (cons (B 1) nil).
End BindContinuationBinderFromClassField.
Crane Extraction "bind_continuation_binder_from_class_field" BindContinuationBinderFromClassField.
