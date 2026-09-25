(** The other half of the pair with [bind_continuation_binder_ctor_order]:
    byte-for-byte that file with [Params]'s two [Type] fields swapped, so [tag]
    is declared first and [addr] second.  The element type, the constructor
    argument order, the monad, the nesting and the inline [fix] are all held
    fixed; only the class's declaration order moves.

    {b Why only the pair says anything.}  Either file alone shows an emitted
    spelling and no reason to call it positional.  Together they vary exactly
    one input, and the carrier guess the Vellvm session was characterising
    followed it: the filler was [addr] in one and [tag] in the other, moving
    with declaration order and not with the lost type.  That is what made the
    pair the unit rather than the file.

    {b The reason is restated, not inherited.}  That guess
    ([Gen_decls.rewrite_ml_ast_types]) is deleted in crane [a290bbbab], so the
    pair no longer characterises a live mechanism.  It is kept as a pair
    because declaration order was the only input the guess ever read, so these
    two files are the corpus's most direct check that no later pass starts
    filling holes positionally again.  A regression test for the absence of a
    mechanism, which is a weaker thing than a reduction and is labelled as one.

    See [bind_continuation_binder_ctor_order] for the shared account and for
    the one respect in which these are also a genuine widening of
    [tests/regression/bind_continuation_binder_from_class_field].

    Ported from the Vellvm session's
    [src/crane/reductions/bind_continuation_binder_field_order] ([1341e658]),
    unchanged in substance. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive EOU (A : Type) : Type :=
| Ok : A -> EOU A
| Err : nat -> EOU A.

Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end
  |}.

(** The only difference from the file next door: [tag] is declared first. *)
Class Params := { tag : Type ; addr : Type ; t0 : tag ; zero : addr }.

Inductive dv (P : Params) : Type :=
| DAddr : tag -> addr -> dv P
| DNum : nat -> dv P.

Arguments DAddr {P}.
Arguments DNum {P}.

Inductive byte (P : Params) : Type :=
| B : nat -> byte P.

Arguments B {P}.

Fixpoint bytes_to_dv {P : Params} (n : nat) (bs : list (byte P)) : EOU (dv P) :=
  match n, bs with
  | O, _ => ret (DNum 0)
  | S k, nil => ret (DAddr t0 zero)
  | S k, cons (B v) rest =>
      let fix go (ds : list nat) (bs0 : list (byte P)) : EOU (list (dv P)) :=
          match ds with
          | nil => ret nil
          | cons _ ds' =>
              bind (bytes_to_dv k bs0)
                   (fun (f : dv P) =>
                      bind (go ds' bs0)
                           (fun (r : list (dv P)) => ret (cons f r)))
          end
      in bind (go (cons v nil) rest) (fun r => ret (DNum (length r)))
  end.

#[global] Instance natParams : Params :=
  {| tag := bool ; addr := nat ; t0 := true ; zero := 0 |}.

Module BindContinuationBinderFieldOrder.
  Definition run : EOU (dv natParams) :=
    @bytes_to_dv natParams 2 (cons (B 1) nil).
End BindContinuationBinderFieldOrder.
Crane Extraction "bind_continuation_binder_field_order" BindContinuationBinderFieldOrder.
