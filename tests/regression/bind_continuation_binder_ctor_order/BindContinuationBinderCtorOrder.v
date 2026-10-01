(** [bind_continuation_binder_from_class_field] widened so the element type has
    {e two} class-dependent fields, with the class's second-declared one last in
    the constructor: [Params] declares [addr] then [tag], and [DAddr] takes
    [tag -> addr -> dv P].

    {b What this file was built for, and what it is now.}  The Vellvm-side
    session built this and its neighbour
    [bind_continuation_binder_field_order] as a {e pair} to characterise the
    carrier guess in [Gen_decls.rewrite_ml_ast_types]: only the pair holds the
    element type fixed while moving which associated type heads the class, so
    only the pair can show that the emitted filler follows declaration order
    rather than the lost type.  That guess is deleted (crane [a290bbbab]), so
    the pair no longer characterises anything.

    It is kept, and kept as a pair, for a different and weaker reason that is
    stated here rather than inherited: {b a deleted mechanism needs a test that
    it stays deleted}, and declaration order is the only input the guess ever
    read.  If a future pass starts filling holes positionally again, these two
    files disagree with each other before anything else in the corpus does.
    They are regression tests for the {e absence} of a mechanism, not
    reductions of a defect.

    There is one thing here that is not merely a re-run.  Two class-dependent
    constructor fields in an order that does not match the class's is a
    genuinely wider input than the single-field original, and it is the
    recovery ([recover_fix_codomain] through [ml_app_result_type]) that has to
    answer it now.  A recovery that read a position rather than a type would
    pass the original and fail this.

    The control remains internal and eleven lines away: the [bind] {e outside}
    the inline [fix], over the same element type in the same emitted function,
    holding the class, the monad instance, the plugin revision and the flags by
    identity rather than by assertion.

    Ported from the Vellvm session's
    [src/crane/reductions/bind_continuation_binder_ctor_order] ([1341e658]),
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

Class Params := { addr : Type ; tag : Type ; zero : addr ; t0 : tag }.

(** Two class-dependent fields, the second-declared one first in [DAddr]. *)
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
      (* The inner [fix] calls the enclosing [Fixpoint], so it stays inline. *)
      let fix go (ds : list nat) (bs0 : list (byte P)) : EOU (list (dv P)) :=
          match ds with
          | nil => ret nil
          | cons _ ds' =>
              bind (bytes_to_dv k bs0)
                   (fun (f : dv P) =>
                      bind (go ds' bs0)
                           (fun (r : list (dv P)) => ret (cons f r)))
          end
      in
      (* The control arm: same element type, same monad, outside the fix. *)
      bind (go (cons v nil) rest) (fun r => ret (DNum (length r)))
  end.

#[global] Instance natParams : Params :=
  {| addr := nat ; tag := bool ; zero := 0 ; t0 := true |}.

Module BindContinuationBinderCtorOrder.
  Definition run : EOU (dv natParams) :=
    @bytes_to_dv natParams 2 (cons (B 1) nil).
End BindContinuationBinderCtorOrder.
Crane Extraction "bind_continuation_binder_ctor_order" BindContinuationBinderCtorOrder.
